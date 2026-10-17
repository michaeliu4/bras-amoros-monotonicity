import Results.Genus.GoldenGraph.WordCompiler

/-! Golden-q graph bounds on every actual original path and cycle. -/
namespace SubmittedGenus.GoldenGraph.Source
open RawGraph RawGraph.SourceModel RawGraph.Topology
open CapFourMass.ActualComponent GoldenSpectral CapFiveMass.MatrixBounds
open scoped BigOperators Matrix
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

lemma sourceRunWord_restricted {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) :
    restrictedLength (sourceRunWord hp c)=restrictedLength (sourceWord c) := by
  unfold sourceRunWord sourceWord
  split_ifs
  · exact (rotated_exponents _ _).2.2
  · rfl

def componentEnvelope {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) : ℝ :=
  componentBoundaryMass c * pathInflation^(if (freeComponentOrder m r p c).cycle=true then 0 else 1) *
    strongBound^(strongLength (sourceWord c)+2*restrictedLength (sourceWord c)) *
    paidCost^(componentPaidRuns hp c)

lemma componentEnvelope_nonneg {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) :
    0≤componentEnvelope hp c := by
  unfold componentEnvelope
  exact mul_nonneg (mul_nonneg (mul_nonneg (componentBoundaryMass_nonneg c)
    (pow_nonneg pathInflation_pos.le _)) (pow_nonneg strongBound_pos.le _)) (pow_nonneg paidCost_pos.le _)

lemma component_path_paid_bound {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=false) : componentMass c≤componentEnvelope hp c := by
  obtain ⟨q,hq,hm⟩:=actual_path_code_le hp c hc
  have hcounts:=sourceAtoms_counts (pathWord c) (pathWord_compatible hp c)
  rw [hq,(PathCode.atoms_counts q).1,(PathCode.atoms_counts q).2.1,(PathCode.atoms_counts q).2.2] at hcounts
  have hruns : pathRunCount q=strongRunCount (pathWord c) := by
    rw [pathRunCount_eq_atomic,← hq,sourceAtoms_strong_runs]
  have hs:=path_conservative_bound q (halfWeights c 0) (halfWeights c (edgeCount c))
  rw [hcounts.1,hcounts.2.2,hruns] at hs
  have hb : Real.sqrt (vectorEnergy (halfWeights c 0))*Real.sqrt (vectorEnergy (halfWeights c (edgeCount c)))≤
      Real.sqrt (endpointMass (CapFiveMass.ActualComponent.leftKind c))*
        Real.sqrt (endpointMass (CapFiveMass.ActualComponent.rightKind c)) :=
    mul_le_mul (Real.sqrt_le_sqrt (first_half_energy c)) (Real.sqrt_le_sqrt (last_half_energy c))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have he:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb pathInflation_pos.le) (pow_nonneg strongBound_pos.le
      (strongLength (pathWord c)+2*restrictedLength (pathWord c))))
    (pow_nonneg paidCost_pos.le (strongRunCount (pathWord c)-2))
  have hc' : ¬(freeComponentOrder m r p c).cycle=true := by simp [hc]
  simpa only [componentEnvelope,componentBoundaryMass,if_neg hc',pow_one,sourceWord,
    componentPaidRuns,sourceRunWord,dif_neg hc'] using (hm.trans hs).trans he

lemma component_cycle_paid_bound {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) : componentMass c≤componentEnvelope hp c := by
  obtain ⟨bs,hbs,he,hm⟩:=actual_cycle_code_le hp c hc
  have hcounts:=sourceAtoms_counts (sourceRunWord hp c) (sourceRunWord_compatible hp c)
  rw [he,(paired_counts bs).1,(paired_counts bs).2.1,(paired_counts bs).2.2,
    sourceRunWord_strong,sourceRunWord_restricted] at hcounts
  have hruns : bs.length=strongRunCount (sourceRunWord hp c) := by
    rw [← paired_strong_runs,← he,sourceAtoms_strong_runs]
  cases bs with
  | nil => contradiction
  | cons b bs =>
    have hs:=cycle_paid_bound b bs
    rw [hcounts.1,hcounts.2.2] at hs
    have hruns' : bs.length+1=strongRunCount (sourceRunWord hp c) := hruns
    rw [hruns'] at hs
    have hm' : componentMass c≤(blockMatrix b*(bs.map blockMatrix).prod).trace := hm
    simpa only [componentEnvelope,componentBoundaryMass,if_pos hc,pow_zero,one_mul,mul_one,
      componentPaidRuns] using hm'.trans hs

/-- The actual source component receives one physical boundary factor, one
k₀ only when it is a path, every D/E edge charge, and its proved paid runs. -/
theorem component_paid_bound {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) :
    componentMass c≤componentEnvelope hp c := by
  cases hc : (freeComponentOrder m r p c).cycle
  · exact component_path_paid_bound hp c hc
  · exact component_cycle_paid_bound hp c hc

lemma componentEnvelope_product {m r p : ℕ} (hp : Parameters m r p 4) :
    (∏ c : Component m r p,componentEnvelope hp c)=
      sourceBoundaryMass m r p * pathInflation^sourcePathCount m r p *
      strongBound^(totalStrongLength m r p+2*totalRestrictedLength m r p)*
      paidCost^sourcePaidRunCount hp := by
  unfold componentEnvelope
  simp only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.sum_add_distrib,← Finset.mul_sum]
  rfl

/-- Golden source bound before the scalar endpoint/path/gap budgets. -/
theorem raw_eval_le_paid_product {m r p : ℕ} (hp : Parameters m r p 4) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) radius (rawPolynomial m r p 4)≤
      radius^8*(sourceBoundaryMass m r p * pathInflation^sourcePathCount m r p *
        strongBound^(totalStrongLength m r p+2*totalRestrictedLength m r p)*
        paidCost^sourcePaidRunCount hp) := by
  rw [raw_eval_eq_component_product hp,← componentEnvelope_product hp]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg radius_pos.le _)
  exact Finset.prod_le_prod (fun c _ => componentMass_nonneg c) (fun c _ => component_paid_bound hp c)

end
end SubmittedGenus.GoldenGraph.Source
