import Results.Genus.CapFiveMass.General.Components

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass.General
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer LocalSource MatrixSource ActualComponent

lemma path_edge_bound_product (H : Control) {m r p : ℕ} (c : Component m r p) :
    MatrixBounds.chainBound (controls (edgeCount c) (edgeControls H c)) =
      H.a ^ pathStrongCount c * H.b ^ pathCarryCount c := by
  rw [controls_bound_product]
  have he (j : Fin (edgeCount c)) : (edgeControls H c j.val).bound =
      if StrongEdge r p (vertex c j.castSucc) (vertex c j.succ) then H.a else H.b := by
    simp only [edgeControls, dif_pos j.isLt, sourceTransfer]
    split_ifs <;> rfl
  simp_rw [he]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, pathStrongCount, pathCarryCount]

lemma two_endpoint_product (H : Control) (x y : EndpointKind) :
    endpointBound H x * endpointBound H y =
      alphabetMass 5 H.z ^ ((if x = .free then 1 else 0) + (if y = .free then 1 else 0)) *
      H.a ^ ((if x = .strongLoop then 1 else 0) + (if y = .strongLoop then 1 else 0)) *
      H.b ^ ((if x = .carryLoop then 1 else 0) + (if y = .carryLoop then 1 else 0)) := by
  cases x <;> cases y <;> simp [endpointBound] <;> ring

lemma cycleBound_eq (H : Control) {m r p : ℕ} (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle = true) :
    cycleBound H c = H.a ^ strongCount c * H.b ^ carryCount c := by
  have he : MatrixBounds.chainBound (controls (edgeCount c) (edgeControls H c) ++ [closeControl H c]) =
      MatrixBounds.chainBound (controls (edgeCount c) (edgeControls H c)) * (closeControl H c).bound := by
    simp [MatrixBounds.chainBound, List.map_append, List.prod_append]
  rw [cycleBound, he, path_edge_bound_product H]
  unfold closeControl sourceTransfer
  split_ifs with hs
  · simp [strongCount, carryCount, hc, hs, strongTransferSix, extendControlled, strongTransfer, pow_succ]
    ring
  · simp [strongCount, carryCount, hc, hs, carryTransferSix, extendControlled, carryTransfer, pow_succ]
    ring

/-- Exact exponent accounting for the actual component contraction. -/

lemma componentBound_sq (H : Control) {m r p : ℕ} (c : Component m r p) :
    componentBound H c ^ 2 =
      alphabetMass 5 H.z ^ endpointCount c .free *
      H.a ^ (2 * strongCount c + endpointCount c .strongLoop) *
      H.b ^ (2 * carryCount c + endpointCount c .carryLoop) := by
  by_cases hc : (freeComponentOrder m r p c).cycle = true
  · rw [componentBound, if_pos hc, cycleBound_eq H c hc]
    simp only [endpointCount, hc, if_true, add_zero, pow_zero, one_mul, mul_pow]
    rw [← pow_mul, ← pow_mul]
    congr 1 <;> congr 1 <;> omega
  · rw [componentBound, if_neg hc, pathBound, mul_pow, mul_pow,
      Real.sq_sqrt (endpointBound_nonneg H _), Real.sq_sqrt (endpointBound_nonneg H _),
      two_endpoint_product H, path_edge_bound_product H]
    simp only [strongCount, carryCount, endpointCount, hc, Bool.false_eq_true, false_and, if_false, add_zero,
      pow_add, mul_pow, pow_mul]
    ring

def allComponentMass (H : Control) (m r p : ℕ) : ℝ := ∏ c : Component m r p, componentMass H c

def allComponentBound (H : Control) (m r p : ℕ) : ℝ := ∏ c : Component m r p, componentBound H c

lemma allComponentMass_nonneg (H : Control) (m r p : ℕ) : 0 ≤ allComponentMass H m r p :=
  Finset.prod_nonneg fun c _ => componentMass_nonneg H c

lemma allComponentBound_nonneg (H : Control) (m r p : ℕ) : 0 ≤ allComponentBound H m r p :=
  Finset.prod_nonneg fun c _ => componentBound_nonneg H c

lemma allComponentMass_le (H : Control) {m r p : ℕ} (hp : Parameters m r p 5) :
    allComponentMass H m r p ≤ allComponentBound H m r p := by
  exact Finset.prod_le_prod (fun c _ => componentMass_nonneg H c) (fun c _ => componentMass_le H hp c)

lemma allComponentBound_sq (H : Control) (m r p : ℕ) :
    allComponentBound H m r p ^ 2 =
      alphabetMass 5 H.z ^ totalEndpointCount m r p .free *
      H.a ^ (2 * totalStrongCount m r p + totalEndpointCount m r p .strongLoop) *
      H.b ^ (2 * totalCarryCount m r p + totalEndpointCount m r p .carryLoop) := by
  unfold allComponentBound
  rw [← Finset.prod_pow]
  simp_rw [componentBound_sq H]
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, totalEndpointCount, totalStrongCount, totalCarryCount]

lemma allComponentMass_sq_le (H : Control) {m r p : ℕ} (hp : Parameters m r p 5) :
    allComponentMass H m r p ^ 2 ≤
      alphabetMass 5 H.z ^ totalEndpointCount m r p .free *
      H.a ^ (2 * totalStrongCount m r p + totalEndpointCount m r p .strongLoop) *
      H.b ^ (2 * totalCarryCount m r p + totalEndpointCount m r p .carryLoop) := by
  rw [← allComponentBound_sq H]
  exact pow_le_pow_left₀ (allComponentMass_nonneg H m r p) (allComponentMass_le H hp) 2

end SubmittedGenus.CapFiveMass.General
