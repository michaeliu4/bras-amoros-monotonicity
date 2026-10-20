import Results.Genus.CapFourMass.RationalModeAdapter
import Results.Genus.CapFourMass.NormalizedFeedback
import Results.Genus.FixedPivot.PurePhases
import Results.Genus.FixedPivot.SourceGenerating

/-!
# Original cap-four source modes and pure all-multiplicity progression

The finite core is contracted before the absolute value of a complete mode
assignment is taken. All definitions below use the actual raw source kernels.
-/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open FixedPivot

lemma lam_ne_zero : lam ≠ 0 := ne_of_gt lam_pos
lemma mu_ne_zero : mu ≠ 0 := ne_of_lt mu_neg
lemma roots_gap_ne_zero : lam-mu ≠ 0 := by linarith [lam_pos,mu_neg]
lemma real_carryB_ne_zero : FixedPivot.carryB radius ≠ 0 := by
  change carryB ≠ 0
  exact ne_of_gt carryB_pos

/-- The actual all-positive source contraction, including zero-edge tails. -/
def sourcePure (r N d : ℕ) (hN : d<N) : ℝ :=
  canonicalPureContribution radius lam mu lam⁻¹ (lam-mu)⁻¹ r N d hN

/-- This is a complete carry-mode coefficient: the core-spin contraction is
performed inside this sum, before any absolute value is introduced. -/
def sourceCoefficient (r N d : ℕ) (hN : d<N)
    (choice : CarryRepresentative N d hN → Bool) : ℝ :=
  ∑ x : Fin (r+d) → Fin 5,
    sourceModeCoefficient hN radius lam mu lam⁻¹ mu⁻¹ (lam-mu)⁻¹ (x,choice)

lemma sourcePure_eq_coefficient (r N d : ℕ) (hN : d<N) :
    sourcePure r N d hN=sourceCoefficient r N d hN (fun _ => false) := by
  simp [sourcePure,sourceCoefficient,canonicalPureContribution,
    sourceModeCoefficient,canonicalModeAmplitude]

lemma stableCore_eval_nonneg (r d : ℕ) (x : Fin (r+d) → Fin 5) :
    0 ≤ Polynomial.eval₂ (Nat.castRingHom ℝ) radius (stableCoreTerm r (r+d) x) := by
  unfold stableCoreTerm
  split_ifs
  · simp only [Polynomial.eval₂_pow,Polynomial.eval₂_X]
    exact pow_nonneg radius_pos.le _
  · simp

lemma sourceHalf_indicator_nonneg (f : Fin 3 → Prop) [DecidablePred f] (i : State) :
    0 ≤ sourceHalf (fun j => if f j then 1 else 0) i := by
  unfold sourceHalf halfScale
  apply mul_nonneg (halfWeight_pos i).le
  change 0 ≤ ![if f 0 then (1:ℝ) else 0,if f 1 then 1 else 0,if f 2 then 1 else 0,0] i
  fin_cases i <;> norm_num <;> split_ifs <;> norm_num

lemma source_positive_amplitude_nonneg {r N d : ℕ} (hN : d<N)
    (x : Fin (r+d) → Fin 5) (c : CarryRepresentative N d hN) :
    0 ≤ canonicalModeAmplitude hN radius lam mu lam⁻¹ (lam-mu)⁻¹ x c := by
  unfold canonicalModeAmplitude
  rw [rational_positive_amplitude]
  apply mul_nonneg
  · apply mul_nonneg (pow_nonneg lam_pos.le _)
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (sourceHalf_indicator_nonneg _ i) (qplus_nonneg i))
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (qplus_nonneg i) (sourceHalf_indicator_nonneg _ i))

lemma sourcePure_nonneg (r N d : ℕ) (hN : d<N) : 0 ≤ sourcePure r N d hN := by
  change 0 ≤ ∑ x : Fin (r+d)→Fin 5,
    Polynomial.eval₂ (Nat.castRingHom ℝ) radius (stableCoreTerm r (r+d) x)*
      ∏ c : CarryRepresentative N d hN,
        canonicalModeAmplitude hN radius lam mu lam⁻¹ (lam-mu)⁻¹ x c
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (stableCore_eval_nonneg r d x)
    (Finset.prod_nonneg (fun c _ => source_positive_amplitude_nonneg hN x c)))

/-- Exact equality to the symmetric orthonormal source convention, term by term. -/
theorem sourcePure_eq_symmetric (r N d : ℕ) (hN : d<N) :
    sourcePure r N d hN=
      ∑ x : Fin (r+d)→Fin 5,
        Polynomial.eval₂ (Nat.castRingHom ℝ) radius (stableCoreTerm r (r+d) x)*
        ∏ c : CarryRepresentative N d hN,
          lam^(carryTailSize N d hN c-1)*
            (sourceHalf (fun v => if canonicalStartAllowed x c v then 1 else 0) ⬝ᵥ qplus)*
            (qplus ⬝ᵥ sourceHalf (fun v => if canonicalFinishAllowed x c v then 1 else 0)) := by
  unfold sourcePure canonicalPureContribution
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact Finset.prod_congr rfl (fun c _ => rational_positive_amplitude _ _ _)

/-- The actual source pure partition advances by λ² for both parity phases. -/
theorem sourcePure_two_step (r N d : ℕ) (hd : 0<d) (hN : d<N) (hbig : 2*d<N) :
    sourcePure r (N+2) d (by omega)=lam^2*sourcePure r N d hN := by
  rcases Nat.even_or_odd d with he | ho
  · exact pureContribution_even_step radius lam mu (FixedPivot.carryB radius)⁻¹ lam⁻¹
      (lam-mu)⁻¹ real_roots_sum real_roots_product
      (mul_inv_cancel₀ real_carryB_ne_zero) r N d hd hN hbig he
  · have h1 := pureContribution_odd_step radius lam mu (FixedPivot.carryB radius)⁻¹ lam⁻¹
      (lam-mu)⁻¹ real_roots_sum real_roots_product
      (mul_inv_cancel₀ real_carryB_ne_zero) r N d hd hN hbig ho
    have h2 := pureContribution_odd_step radius lam mu (FixedPivot.carryB radius)⁻¹ lam⁻¹
      (lam-mu)⁻¹ real_roots_sum real_roots_product
      (mul_inv_cancel₀ real_carryB_ne_zero) r (N+1) d hd (by omega) (by omega) ho
    change sourcePure r (N+1+1) d _=lam*sourcePure r (N+1) d _ at h2
    change sourcePure r (N+1) d _=lam*sourcePure r N d hN at h1
    rw [h1] at h2
    simpa only [pow_two,mul_assoc] using h2

/-- The original normalized pure progression, for the actual source. -/
theorem normalized_sourcePure_two_step (r N d : ℕ) (hd : 0<d) (hN : d<N)
    (hbig : 2*d<N) :
    normalizedMass (r+(N+2)) (sourcePure r (N+2) d (by omega))=
      (normalizer*lam)^2*normalizedMass (r+N) (sourcePure r N d hN) := by
  rw [sourcePure_two_step r N d hd hN hbig]
  unfold normalizedMass
  have he : r+(N+2)-1=(r+N-1)+2 := by omega
  rw [he,pow_add,mul_pow]
  ring

/-- The signed finite mode expansion equals the actual raw polynomial. -/
theorem rawPolynomial_eq_source_modes {r N d : ℕ} (hr : 0<r) (hd : 0<d)
    (hN : d<N) (hbig : r+2*d<N) (k : ℕ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) radius
      (RawGraph.rawPolynomial (r+(N+k*d)) r (r+d) 4)=
      ∑ choice : CarryRepresentative N d hN → Bool,
        sourceCoefficient r N d hN choice*
          (lam^(pureModeDegree (carryPortArity N d hN) choice)*
            mu^(mixedModeDegree (carryPortArity N d hN) choice))^k := by
  rw [rawPolynomial_progression_modes hr hd hN hbig radius lam mu lam⁻¹ mu⁻¹ (lam-mu)⁻¹
    real_roots_sum real_roots_product (mul_inv_cancel₀ lam_ne_zero)
    (mul_inv_cancel₀ mu_ne_zero) (mul_inv_cancel₀ roots_gap_ne_zero)]
  simp only [finiteMode_expansion,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro choice _
  rw [sourceCoefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  simp only [sourceModeCoefficient,mul_assoc]

end SubmittedGenus.CapFourMass
