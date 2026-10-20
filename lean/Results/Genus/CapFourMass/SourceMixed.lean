import Results.Genus.CapFourMass.SourceProgression

/-! Exact complete source-mode absolute partitions and all-multiplicity mixed contraction. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass
open FixedPivot

section Source
variable (r N d : ℕ) (hN : d<N)

def sourceAbsolute : ℝ := ∑ choice : CarryRepresentative N d hN → Bool,
  |sourceCoefficient r N d hN choice|

def sourceMixed : ℝ := ∑ choice : CarryRepresentative N d hN → Bool,
  if choice=(fun _ => false) then 0 else |sourceCoefficient r N d hN choice|

lemma sourceMixed_nonneg : 0 ≤ sourceMixed r N d hN := by
  unfold sourceMixed
  exact Finset.sum_nonneg (fun _ _ => by split_ifs; rfl; exact abs_nonneg _)

lemma sourceAbsolute_eq_pure_add_mixed :
    sourceAbsolute r N d hN=sourcePure r N d hN+sourceMixed r N d hN := by
  classical
  have hs : sourceAbsolute r N d hN=
      (∑ choice : CarryRepresentative N d hN → Bool,
        if choice=(fun _ => false) then |sourceCoefficient r N d hN choice| else 0)+
      sourceMixed r N d hN := by
    rw [sourceAbsolute,sourceMixed,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro choice _
    split_ifs <;> simp
  rw [hs]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← sourcePure_eq_coefficient,abs_of_nonneg (sourcePure_nonneg r N d hN)]

lemma sourcePure_le_absolute : sourcePure r N d hN ≤ sourceAbsolute r N d hN := by
  rw [sourceAbsolute_eq_pure_add_mixed]
  exact le_add_of_nonneg_right (sourceMixed_nonneg r N d hN)

end Source

/-- Signed source modes are dominated only after complete core contraction. -/
theorem rawPolynomial_le_source_pure_mixed {r N d : ℕ} (hr : 0<r) (hd : 0<d)
    (hN : d<N) (hbig : r+2*d<N) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) radius (RawGraph.rawPolynomial (r+N) r (r+d) 4) ≤
      sourcePure r N d hN+sourceMixed r N d hN := by
  have hh:=rawPolynomial_eq_source_modes hr hd hN hbig 0
  simp only [zero_mul,add_zero,pow_zero,mul_one] at hh
  rw [hh,← sourceAbsolute_eq_pure_add_mixed]
  exact Finset.sum_le_sum (fun _ _ => le_abs_self _)

/-- The exact actual component identification on m↦m+kd. -/
def sourceChoiceEquiv (N d : ℕ) (hN : d<N) (k : ℕ) :
    (CarryRepresentative N d hN → Bool) ≃
      (CarryRepresentative (N+k*d) d (by omega) → Bool) where
  toFun choice := fun c => choice ((carryRepresentativeIterated N d hN k).symm c)
  invFun choice := fun c => choice (carryRepresentativeIterated N d hN k c)
  left_inv choice := by funext c; simp
  right_inv choice := by funext c; simp

lemma sourceChoiceEquiv_apply (N d : ℕ) (hN : d<N) (k : ℕ)
    (choice : CarryRepresentative N d hN → Bool) (c : CarryRepresentative N d hN) :
    sourceChoiceEquiv N d hN k choice (carryRepresentativeIterated N d hN k c)=choice c := by
  simp [sourceChoiceEquiv]

lemma sourceChoiceEquiv_zero (N d : ℕ) (hN : d<N) (k : ℕ)
    (choice : CarryRepresentative N d hN → Bool) :
    sourceChoiceEquiv N d hN k choice=(fun _ => false) ↔ choice=(fun _ => false) := by
  constructor
  · intro hh
    funext c
    have h:=congrFun hh (carryRepresentativeIterated N d hN k c)
    simpa only [sourceChoiceEquiv_apply] using h
  · rintro rfl
    rfl

lemma weightedModeAmplitude_shift (theta other ti di : ℝ) (n a k : ℕ)
    (start finish : Fin 3 → ℝ) :
    weightedModeAmplitude radius theta other ti di (n+a*k) start finish=
      weightedModeAmplitude radius theta other ti di n start finish*(theta^a)^k := by
  unfold weightedModeAmplitude
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add,pow_mul]
  ring

lemma canonicalModeAmplitude_iterated {r N d : ℕ} (hN : d<N) (hbig : 2*d<N)
    (k : ℕ) (theta other ti di : ℝ) (x : Fin (r+d) → Fin 5)
    (c : CarryRepresentative N d hN) :
    canonicalModeAmplitude (show d<N+k*d by omega) radius theta other ti di x
        (carryRepresentativeIterated N d hN k c)=
      canonicalModeAmplitude hN radius theta other ti di x c*(theta^(carryPortArity N d hN c))^k := by
  unfold canonicalModeAmplitude
  rw [carryTailEdges_iterated N d hN hbig]
  simp only [canonicalStartAllowed_iterated,canonicalFinishAllowed_iterated,weightedModeAmplitude_shift]
  congr 2

/-- Every complete mode coefficient gains its exact signed spectral rate. -/
theorem sourceCoefficient_iterated (r N d : ℕ) (hN : d<N) (hbig : 2*d<N)
    (k : ℕ) (choice : CarryRepresentative N d hN → Bool) :
    sourceCoefficient r (N+k*d) d (by omega) (sourceChoiceEquiv N d hN k choice)=
      sourceCoefficient r N d hN choice*
        (lam^(pureModeDegree (carryPortArity N d hN) choice)*
          mu^(mixedModeDegree (carryPortArity N d hN) choice))^k := by
  unfold sourceCoefficient sourceModeCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [← (carryRepresentativeIterated N d hN k).prod_comp]
  simp only [sourceChoiceEquiv_apply,canonicalModeAmplitude_iterated hN hbig]
  have hprod : (∏ c : CarryRepresentative N d hN,
      if choice c then canonicalModeAmplitude hN radius mu lam mu⁻¹ (-(lam-mu)⁻¹) x c*(mu^(carryPortArity N d hN c))^k
      else canonicalModeAmplitude hN radius lam mu lam⁻¹ (lam-mu)⁻¹ x c*(lam^(carryPortArity N d hN c))^k)=
      (∏ c : CarryRepresentative N d hN,
        if choice c then canonicalModeAmplitude hN radius mu lam mu⁻¹ (-(lam-mu)⁻¹) x c
        else canonicalModeAmplitude hN radius lam mu lam⁻¹ (lam-mu)⁻¹ x c)*
      (lam^(pureModeDegree (carryPortArity N d hN) choice)*
        mu^(mixedModeDegree (carryPortArity N d hN) choice))^k := by
    calc
      _ = ∏ c : CarryRepresentative N d hN,
        (if choice c then canonicalModeAmplitude hN radius mu lam mu⁻¹ (-(lam-mu)⁻¹) x c
          else canonicalModeAmplitude hN radius lam mu lam⁻¹ (lam-mu)⁻¹ x c)*
        (if choice c then mu^(carryPortArity N d hN c) else lam^(carryPortArity N d hN c))^k := by
          apply Finset.prod_congr rfl
          intro c _
          cases choice c <;> rfl
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow,modeRate_eq]
  rw [hprod]
  ring

lemma source_mixed_degree_pos {N d : ℕ} (hN : d<N)
    (choice : CarryRepresentative N d hN → Bool) (hc : choice ≠ (fun _ => false)) :
    0 < mixedModeDegree (carryPortArity N d hN) choice := by
  classical
  have he : ∃ c,choice c=true := by
    by_contra hn
    apply hc
    funext c
    cases hh : choice c
    · rfl
    · exact False.elim (hn ⟨c,hh⟩)
  obtain ⟨c,hc⟩:=he
  unfold mixedModeDegree
  have hle := Finset.single_le_sum (f:=fun c => if choice c then carryPortArity N d hN c else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  simp only [hc,ite_true] at hle
  exact (carryPortArity_pos N d hN c).trans_le hle

lemma source_mixed_rate_bound {N d : ℕ} (hN : d<N)
    (choice : CarryRepresentative N d hN → Bool) (hc : choice ≠ (fun _ => false)) :
    |(lam^(pureModeDegree (carryPortArity N d hN) choice)*
      mu^(mixedModeDegree (carryPortArity N d hN) choice))^2| ≤ lam^(2*d)*rho^2 := by
  let a:=pureModeDegree (carryPortArity N d hN) choice
  let b:=mixedModeDegree (carryPortArity N d hN) choice
  have hab : a+b=d := by
    exact (modeDegrees_sum (carryPortArity N d hN) choice).trans (carry_port_arity_sum N d hN)
  have hb : 0<b := source_mixed_degree_pos hN choice hc
  have hmu : |mu|=lam*rho := by rw [rho]; field_simp [lam_ne_zero]
  have hrho : rho ≤ 1 := by linarith [rho_bounds.2]
  change |(lam^a*mu^b)^2| ≤ _
  rw [abs_pow,abs_mul,abs_pow,abs_pow,abs_of_pos lam_pos,hmu]
  have he : (lam^a*(lam*rho)^b)^2=lam^(2*(a+b))*rho^(2*b) := by
    simp only [pow_mul,pow_add,mul_pow]
    ring
  rw [he,hab]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one rho_bounds.1.le hrho (show 2 ≤ 2*b by omega)) (pow_nonneg lam_pos.le _)

/-- Original unnormalized mixed progression, for actual complete source assignments. -/
theorem sourceMixed_two_gap (r N d : ℕ) (hN : d<N) (hbig : 2*d<N) :
    sourceMixed r (N+2*d) d (by omega) ≤ lam^(2*d)*rho^2*sourceMixed r N d hN := by
  classical
  unfold sourceMixed
  rw [← (sourceChoiceEquiv N d hN 2).sum_comp,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro choice _
  simp only [sourceChoiceEquiv_zero,sourceCoefficient_iterated r N d hN hbig 2]
  by_cases hc : choice=(fun _ => false)
  · simp [hc]
  · simp only [hc,ite_false,abs_mul]
    exact (mul_le_mul_of_nonneg_left (source_mixed_rate_bound hN choice hc) (abs_nonneg _)).trans_eq (by ring)

/-- Original normalized mixed progression, with its essential rho² gain. -/
theorem normalized_sourceMixed_two_gap (r N d : ℕ) (hN : d<N) (hbig : 2*d<N) :
    normalizedMass (r+(N+2*d)) (sourceMixed r (N+2*d) d (by omega)) ≤
      (normalizer*lam)^(2*d)*rho^2*normalizedMass (r+N) (sourceMixed r N d hN) := by
  unfold normalizedMass
  have hh:=mul_le_mul_of_nonneg_left (sourceMixed_two_gap r N d hN hbig)
    (pow_nonneg normalizer_bounds.1.le (r+(N+2*d)-1))
  rw [show r+(N+2*d)-1=(r+N-1)+2*d by omega,pow_add] at hh ⊢
  simpa only [mul_pow,mul_assoc,mul_comm,mul_left_comm] using hh

end SubmittedGenus.CapFourMass
