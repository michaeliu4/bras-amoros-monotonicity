import Results.Genus.CapFiveMass.ActualComponent
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass
namespace ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer LocalSource MatrixSource

/-- Consecutive strong edges in the proved strict component ordering. -/
def pathStrongCount {m r p : ℕ} (c : Component m r p) : ℕ :=
  (Finset.univ.filter (fun j : Fin (edgeCount c) => StrongEdge r p
    (vertex c j.castSucc) (vertex c j.succ))).card

def pathCarryCount {m r p : ℕ} (c : Component m r p) : ℕ :=
  (Finset.univ.filter (fun j : Fin (edgeCount c) => ¬ StrongEdge r p
    (vertex c j.castSucc) (vertex c j.succ))).card

def strongCount {m r p : ℕ} (c : Component m r p) : ℕ := pathStrongCount c +
  if (freeComponentOrder m r p c).cycle = true ∧ StrongEdge r p (vertex c (Fin.last _)) (vertex c 0) then 1 else 0

def carryCount {m r p : ℕ} (c : Component m r p) : ℕ := pathCarryCount c +
  if (freeComponentOrder m r p c).cycle = true ∧ ¬ StrongEdge r p (vertex c (Fin.last _)) (vertex c 0) then 1 else 0

/-- Zero for cycles; paths have exactly their two endpoint incidences. An
isolated vertex's right incidence is free, so a loop is never counted twice. -/
def endpointCount {m r p : ℕ} (c : Component m r p) (kind : EndpointKind) : ℕ :=
  if (freeComponentOrder m r p c).cycle = true then 0 else
    (if leftKind c = kind then 1 else 0) + (if rightKind c = kind then 1 else 0)

lemma controls_bound_product {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℕ) (E : ℕ → MatrixBounds.Controlled (ι := A)) :
    MatrixBounds.chainBound (controls n E) = ∏ j : Fin n, (E j.val).bound := by
  induction n generalizing E with
  | zero => simp [controls]
  | succ n ih =>
    simp only [controls, MatrixBounds.chainBound_cons, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ]
    rw [ih]
    rfl

lemma path_edge_bound_product {m r p : ℕ} (c : Component m r p) :
    MatrixBounds.chainBound (controls (edgeCount c) (edgeControls c)) =
      strongBound ^ pathStrongCount c * carryBound ^ pathCarryCount c := by
  rw [controls_bound_product]
  have he (j : Fin (edgeCount c)) : (edgeControls c j.val).bound =
      if StrongEdge r p (vertex c j.castSucc) (vertex c j.succ) then strongBound else carryBound := by
    simp only [edgeControls, dif_pos j.isLt, sourceTransfer]
    split_ifs <;> rfl
  simp_rw [he]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, pathStrongCount, pathCarryCount]

lemma two_endpoint_product (x y : EndpointKind) :
    endpointBound x * endpointBound y =
      alphabetMass 5 radius ^ ((if x = .free then 1 else 0) + (if y = .free then 1 else 0)) *
      strongBound ^ ((if x = .strongLoop then 1 else 0) + (if y = .strongLoop then 1 else 0)) *
      carryBound ^ ((if x = .carryLoop then 1 else 0) + (if y = .carryLoop then 1 else 0)) := by
  cases x <;> cases y <;> simp [endpointBound] <;> ring

lemma cycleBound_eq {m r p : ℕ} (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle = true) :
    cycleBound c = strongBound ^ strongCount c * carryBound ^ carryCount c := by
  have he : MatrixBounds.chainBound (controls (edgeCount c) (edgeControls c) ++ [closeControl c]) =
      MatrixBounds.chainBound (controls (edgeCount c) (edgeControls c)) * (closeControl c).bound := by
    simp [MatrixBounds.chainBound, List.map_append, List.prod_append]
  rw [cycleBound, he, path_edge_bound_product]
  unfold closeControl sourceTransfer
  split_ifs with hs
  · simp [strongCount, carryCount, hc, hs, strongTransferSix, extendControlled, strongTransfer, pow_succ]
    ring
  · simp [strongCount, carryCount, hc, hs, carryTransferSix, extendControlled, carryTransfer, pow_succ]
    ring

/-- Exact exponent accounting for the actual component contraction. -/
lemma componentBound_sq {m r p : ℕ} (c : Component m r p) :
    componentBound c ^ 2 =
      alphabetMass 5 radius ^ endpointCount c .free *
      strongBound ^ (2 * strongCount c + endpointCount c .strongLoop) *
      carryBound ^ (2 * carryCount c + endpointCount c .carryLoop) := by
  by_cases hc : (freeComponentOrder m r p c).cycle = true
  · rw [componentBound, if_pos hc, cycleBound_eq c hc]
    simp only [endpointCount, hc, if_true, add_zero, pow_zero, one_mul, mul_pow]
    rw [← pow_mul, ← pow_mul]
    congr 1 <;> congr 1 <;> omega
  · rw [componentBound, if_neg hc, pathBound, mul_pow, mul_pow,
      Real.sq_sqrt (endpointBound_nonneg _), Real.sq_sqrt (endpointBound_nonneg _),
      two_endpoint_product, path_edge_bound_product]
    simp only [strongCount, carryCount, endpointCount, hc, Bool.false_eq_true, false_and, if_false, add_zero,
      pow_add, mul_pow, pow_mul]
    ring

noncomputable instance componentFintype (m r p : ℕ) : Fintype (Component m r p) := Fintype.ofFinite _
noncomputable instance freeVertexFintype (m r p : ℕ) : Fintype (FreeVertex m r p) := Fintype.ofFinite _

def totalStrongCount (m r p : ℕ) : ℕ := ∑ c : Component m r p, strongCount c
def totalCarryCount (m r p : ℕ) : ℕ := ∑ c : Component m r p, carryCount c
def totalEndpointCount (m r p : ℕ) (kind : EndpointKind) : ℕ := ∑ c : Component m r p, endpointCount c kind

def allComponentMass (m r p : ℕ) : ℝ := ∏ c : Component m r p, componentMass c

def allComponentBound (m r p : ℕ) : ℝ := ∏ c : Component m r p, componentBound c

lemma allComponentMass_nonneg (m r p : ℕ) : 0 ≤ allComponentMass m r p :=
  Finset.prod_nonneg fun c _ => componentMass_nonneg c

lemma allComponentBound_nonneg (m r p : ℕ) : 0 ≤ allComponentBound m r p :=
  Finset.prod_nonneg fun c _ => componentBound_nonneg c

lemma allComponentMass_le {m r p : ℕ} (hp : Parameters m r p 5) :
    allComponentMass m r p ≤ allComponentBound m r p := by
  exact Finset.prod_le_prod (fun c _ => componentMass_nonneg c) (fun c _ => componentMass_le hp c)

lemma allComponentBound_sq (m r p : ℕ) :
    allComponentBound m r p ^ 2 =
      alphabetMass 5 radius ^ totalEndpointCount m r p .free *
      strongBound ^ (2 * totalStrongCount m r p + totalEndpointCount m r p .strongLoop) *
      carryBound ^ (2 * totalCarryCount m r p + totalEndpointCount m r p .carryLoop) := by
  unfold allComponentBound
  rw [← Finset.prod_pow]
  simp_rw [componentBound_sq]
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, totalEndpointCount, totalStrongCount, totalCarryCount]

lemma allComponentMass_sq_le {m r p : ℕ} (hp : Parameters m r p 5) :
    allComponentMass m r p ^ 2 ≤
      alphabetMass 5 radius ^ totalEndpointCount m r p .free *
      strongBound ^ (2 * totalStrongCount m r p + totalEndpointCount m r p .strongLoop) *
      carryBound ^ (2 * totalCarryCount m r p + totalEndpointCount m r p .carryLoop) := by
  rw [← allComponentBound_sq]
  exact pow_le_pow_left₀ (allComponentMass_nonneg m r p) (allComponentMass_le hp) 2

lemma path_counts_sum {m r p : ℕ} (c : Component m r p) :
    pathStrongCount c + pathCarryCount c = edgeCount c := by
  simpa only [pathStrongCount, pathCarryCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (edgeCount c))))
      (p := fun j => StrongEdge r p (vertex c j.castSucc) (vertex c j.succ))

lemma edge_counts_sum {m r p : ℕ} (c : Component m r p) :
    strongCount c + carryCount c = edgeCount c + if (freeComponentOrder m r p c).cycle = true then 1 else 0 := by
  have h := path_counts_sum c
  unfold strongCount carryCount
  by_cases hc : (freeComponentOrder m r p c).cycle = true <;>
    by_cases hs : StrongEdge r p (vertex c (Fin.last _)) (vertex c 0) <;>
    simp only [hc, hs, true_and, false_and, and_true, and_false, not_true_eq_false,
      not_false_eq_true, Bool.false_eq_true, ↓reduceIte] <;> omega

lemma endpoint_counts_sum {m r p : ℕ} (c : Component m r p) :
    endpointCount c .free + endpointCount c .strongLoop + endpointCount c .carryLoop =
      if (freeComponentOrder m r p c).cycle = true then 0 else 2 := by
  by_cases hc : (freeComponentOrder m r p c).cycle = true
  · simp [endpointCount, hc]
  · cases hL : leftKind c <;> cases hR : rightKind c <;> simp [endpointCount, hc, hL, hR]

lemma component_incidence_count {m r p : ℕ} (c : Component m r p) :
    endpointCount c .free + endpointCount c .strongLoop + endpointCount c .carryLoop +
      2 * (strongCount c + carryCount c) = 2 * (edgeCount c + 1) := by
  rw [endpoint_counts_sum, edge_counts_sum]
  split_ifs <;> omega

lemma total_incidence_count (m r p : ℕ) :
    totalEndpointCount m r p .free + totalEndpointCount m r p .strongLoop + totalEndpointCount m r p .carryLoop +
      2 * (totalStrongCount m r p + totalCarryCount m r p) = 2 * Fintype.card (FreeVertex m r p) := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun c _ => component_incidence_count (m := m) (r := r) (p := p) c)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have hcard : (∑ c : Component m r p, (edgeCount c + 1)) = Fintype.card (FreeVertex m r p) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr (freeOrderedVertexEquiv m r p)
  simp only [Finset.sum_add_distrib] at hcard
  rw [hcard] at h
  exact h

end ActualComponent
end SubmittedGenus.CapFiveMass
