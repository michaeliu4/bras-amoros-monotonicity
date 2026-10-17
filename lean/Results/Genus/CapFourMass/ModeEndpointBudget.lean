import Results.Genus.CapFourMass.EndpointProduct

/-! The spectral endpoint budget uses endpoint incidences, including the free
second incidence of an isolated carry-loop component. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

lemma freeBoundary_energy_le : vectorEnergy freeBoundary ≤ alphabetMass := by
  have he : freeBoundary=endpoint 3 false := by
    funext i
    fin_cases i <;> norm_num [freeBoundary,endpoint,halfScale]
  rw [he]
  exact endpoint_energy_free _ _

lemma loopBoundary_energy_le_one : vectorEnergy loopBoundary ≤ 1 := by
  have he : loopBoundary=endpoint 3 true := by
    funext i
    fin_cases i <;> norm_num [loopBoundary,endpoint,halfScale]
  rw [he]
  exact (endpoint_energy_loop _).trans loopMass_lt_one.le

/-- The boundary-only carry-loop mode sum has one free and one loop endpoint.
No strong-block assertion at zero edges is used. -/
lemma isolated_carry_loop_absolute_le :
    carryAbsolute 0 freeBoundary loopBoundary ≤ Real.sqrt alphabetMass := by
  have h:=carryAbsolute_le 0 freeBoundary loopBoundary
  simp only [pow_zero,mul_one] at h
  have hb:=mul_le_mul (Real.sqrt_le_sqrt freeBoundary_energy_le)
    (Real.sqrt_le_sqrt loopBoundary_energy_le_one) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  simpa only [Real.sqrt_one,mul_one] using h.trans hb

namespace ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology

def modeEndpointBudget {m r p : ℕ} (c : Component m r p) : ℝ :=
  Real.sqrt (alphabetMass^(CapFiveMass.ActualComponent.endpointCount c .free))

lemma modeEndpointBudget_nonneg {m r p : ℕ} (c : Component m r p) :
    0≤modeEndpointBudget c := Real.sqrt_nonneg _

lemma modeEndpointBudget_sq {m r p : ℕ} (c : Component m r p) :
    modeEndpointBudget c^2=alphabetMass^(CapFiveMass.ActualComponent.endpointCount c .free) :=
  Real.sq_sqrt (pow_nonneg (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one)) _)

/-- A generic endpoint product bound for the actual component geometry. The
local factor may use a free second endpoint at a zero-edge carry-loop. -/
theorem component_endpoint_budget_le {m r p : ℕ} (hp : Parameters m r p 4)
    (f : Component m r p→ℝ)
    (hf : ∀ c,f c^2≤alphabetMass^(CapFiveMass.ActualComponent.endpointCount c .free)) :
    (∏ c,f c)≤alphabetMass := by
  classical
  have hU:=CapFiveMass.MissingGeometry.free_endpoint_count_le_two hp
  have hs : (∏ c,f c)^2≤alphabetMass^(CapFiveMass.ActualComponent.totalEndpointCount m r p .free) := by
    rw [← Finset.prod_pow,CapFiveMass.ActualComponent.totalEndpointCount,← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun c _ => sq_nonneg _) (fun c _ => hf c)
  exact le_of_sq_le_sq (hs.trans (pow_le_pow_right₀ alphabetMass_gt_one.le hU))
    (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one))

lemma modeEndpointBudget_product_le {m r p : ℕ} (hp : Parameters m r p 4) :
    (∏ c : Component m r p,modeEndpointBudget c)≤alphabetMass :=
  component_endpoint_budget_le hp modeEndpointBudget (fun c => (modeEndpointBudget_sq c).le)

lemma path_endpoint_le_modeBudget {m r p : ℕ} (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=false)
    (x y : State→ℝ)
    (hx : vectorEnergy x≤alphabetMass^(if CapFiveMass.ActualComponent.leftKind c=.free then 1 else 0))
    (hy : vectorEnergy y≤alphabetMass^(if CapFiveMass.ActualComponent.rightKind c=.free then 1 else 0)) :
    Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)≤modeEndpointBudget c := by
  apply le_of_sq_le_sq _ (modeEndpointBudget_nonneg c)
  rw [mul_pow,Real.sq_sqrt (vectorEnergy_nonneg _),Real.sq_sqrt (vectorEnergy_nonneg _),modeEndpointBudget_sq]
  simp only [CapFiveMass.ActualComponent.endpointCount,hc,Bool.false_eq_true,if_false,pow_add]
  exact mul_le_mul hx hy (vectorEnergy_nonneg _) (pow_nonneg (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one)) _)

end ActualComponent
end SubmittedGenus.CapFourMass
