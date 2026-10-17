import Results.Genus.CapFourMass.ComponentMatrices
import Results.Genus.CapFiveMass.MissingCount

/-! The actual cap-four global endpoint budget, including isolated loop vertices. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology
open CapFiveMass.MatrixSource CapFiveMass.MatrixBounds

/-- Cycles have no boundary factor. Paths retain both actual endpoint vectors;
for an isolated vertex these are the same physical vector. -/
def endpointFactor {m r p : ℕ} (c : Component m r p) : ℝ :=
  if (freeComponentOrder m r p c).cycle=true then 1 else
    Real.sqrt (vectorEnergy (domainHalf c 0))*
      Real.sqrt (vectorEnergy (domainHalf c (Fin.last _)))

lemma endpointFactor_nonneg {m r p : ℕ} (c : Component m r p) : 0≤endpointFactor c := by
  unfold endpointFactor
  split_ifs
  · norm_num
  · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma domain_energy_kind {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) :
    vectorEnergy (domainHalf c j) ≤
      alphabetMass^(if CapFiveMass.ActualComponent.loopKind (r:=r) (p:=p) (vertex c j)=.free then 1 else 0) := by
  by_cases hs : StrongLoop r p (vertex c j)
  · simp only [CapFiveMass.ActualComponent.loopKind,if_pos hs,reduceCtorEq,if_false,pow_zero]
    exact (domainHalf_loop_energy_le c j (Or.inl hs)).trans loopMass_lt_one.le
  · by_cases hc : CarryLoop r p (vertex c j)
    · simp only [CapFiveMass.ActualComponent.loopKind,if_neg hs,if_pos hc,reduceCtorEq,if_false,pow_zero]
      exact (domainHalf_loop_energy_le c j (Or.inr hc)).trans loopMass_lt_one.le
    · simpa only [CapFiveMass.ActualComponent.loopKind,if_neg hs,if_neg hc,if_true,pow_one]
        using domainHalf_energy_le c j

lemma left_energy_kind {m r p : ℕ} (c : Component m r p) :
    vectorEnergy (domainHalf c 0) ≤
      alphabetMass^(if CapFiveMass.ActualComponent.leftKind c=.free then 1 else 0) :=
  domain_energy_kind c 0

lemma right_energy_kind {m r p : ℕ} (c : Component m r p) :
    vectorEnergy (domainHalf c (Fin.last _)) ≤
      alphabetMass^(if CapFiveMass.ActualComponent.rightKind c=.free then 1 else 0) := by
  by_cases hn : CapFiveMass.ActualComponent.edgeCount c=0
  · simpa only [CapFiveMass.ActualComponent.rightKind,hn,if_true,pow_one] using domainHalf_energy_le c (Fin.last _)
  · have hh:=domain_energy_kind c (Fin.last _)
    simp only [CapFiveMass.ActualComponent.rightKind,hn,if_false,vertex,edgeCount,
      CapFiveMass.ActualComponent.vertex,CapFiveMass.ActualComponent.edgeCount] at hh ⊢
    convert hh using 1
    congr 3


lemma endpointFactor_sq_le {m r p : ℕ} (c : Component m r p) :
    endpointFactor c^2 ≤ alphabetMass^(CapFiveMass.ActualComponent.endpointCount c .free) := by
  by_cases hc : (freeComponentOrder m r p c).cycle=true
  · simp only [endpointFactor,CapFiveMass.ActualComponent.endpointCount,if_pos hc,pow_zero,one_pow,le_refl]
  · simp only [endpointFactor,CapFiveMass.ActualComponent.endpointCount,if_neg hc]
    rw [mul_pow,Real.sq_sqrt (vectorEnergy_nonneg _),Real.sq_sqrt (vectorEnergy_nonneg _),pow_add]
    exact mul_le_mul (left_energy_kind c) (right_energy_kind c) (vectorEnergy_nonneg _)
      (pow_nonneg (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one)) _)

/-- The at-most-two free endpoint incidences contribute only one s4 factor.
Every loop endpoint costs at most one, including the zero-edge corner. -/
theorem actual_endpoint_product_le {m r p : ℕ} (hp : Parameters m r p 4) :
    (∏ c : Component m r p,endpointFactor c) ≤ alphabetMass := by
  classical
  have hU:=CapFiveMass.MissingGeometry.free_endpoint_count_le_two hp
  have hs : (∏ c : Component m r p,endpointFactor c)^2 ≤
      alphabetMass^(CapFiveMass.ActualComponent.totalEndpointCount m r p .free) := by
    rw [← Finset.prod_pow,CapFiveMass.ActualComponent.totalEndpointCount,← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun c _ => sq_nonneg _) (fun c _ => endpointFactor_sq_le c)
  have hh:=hs.trans (pow_le_pow_right₀ alphabetMass_gt_one.le hU)
  exact le_of_sq_le_sq hh (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one))

lemma endpointFactor_path_eq {m r p : ℕ} (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=false) :
    endpointFactor c=Real.sqrt (vectorEnergy (halfWeights c 0))*
      Real.sqrt (vectorEnergy (halfWeights c (edgeCount c))) := by
  have hl : halfWeights c 0=domainHalf c 0 := funext (halfWeights_fin c 0)
  have hr : halfWeights c (edgeCount c)=domainHalf c (Fin.last _) := funext (halfWeights_fin c (Fin.last _))
  rw [hl,hr]
  simp only [endpointFactor,hc,Bool.false_eq_true,if_false]

end SubmittedGenus.CapFourMass.ActualComponent
