import Results.Genus.CapFiveMass.ComponentCounts
import Results.Genus.RawGraph.Factorization

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass
namespace ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer LocalSource

/-- The original unary and binary source restrictions on the actual ordered
free component. Its finite alphabet is the original enumerator's Fin6. -/
def Allowed {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c + 1) → BoundedState) : Prop :=
  (∀ j, Domain r p 5 (vertex c j) (x j).val) ∧
  (∀ j : Fin (edgeCount c), edgeBound r p 5 (vertex c j.castSucc) (vertex c j.succ) ≤
    (x j.castSucc).val + (x j.succ).val) ∧
  ((freeComponentOrder m r p c).cycle = true →
    edgeBound r p 5 (vertex c (Fin.last _)) (vertex c 0) ≤ (x (Fin.last _)).val + (x 0).val)

instance {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c + 1) → BoundedState) :
    Decidable (Allowed c x) := by
  unfold Allowed
  infer_instance

def sourceTermGate {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c + 1) → BoundedState) : ℝ :=
  (∏ j, if Domain r p 5 (vertex c j) (x j).val then radius ^ (x j).val else 0) *
  (∏ j : Fin (edgeCount c), edgeFactor r p (vertex c j.castSucc) (vertex c j.succ) (x j.castSucc) (x j.succ)) *
  (if (freeComponentOrder m r p c).cycle = true then closeFactor c (x (Fin.last _)) (x 0) else 1)

lemma sourceTermGate_eq {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c + 1) → BoundedState) :
    sourceTermGate c x = if Allowed c x then radius ^ (∑ j, (x j).val) else 0 := by
  unfold sourceTermGate closeFactor edgeFactor
  rw [RawGraph.Factorization.prod_gate, RawGraph.Factorization.prod_gate]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const_one]
  unfold Allowed
  split_ifs <;> simp_all

@[simp] lemma edgeFactors_fin {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c))
    (v w : BoundedState) : edgeFactors c j.val v w =
      edgeFactor r p (vertex c j.castSucc) (vertex c j.succ) v w := by
  simp only [edgeFactors, dif_pos j.isLt]

/-- Exact equality from actual component half-weight transfer to its full
finite original source. No vertex monomial is lost or duplicated. -/
lemma componentMass_eq_gated_sum {m r p : ℕ} (c : Component m r p) :
    componentMass c = ∑ x : Fin (edgeCount c + 1) → BoundedState,
      if Allowed c x then radius ^ (∑ j, (x j).val) else 0 := by
  simp_rw [← sourceTermGate_eq]
  unfold componentMass
  split_ifs with hc
  · unfold cycleSource
    apply Finset.sum_congr rfl
    intro x _
    simp only [sourceTerm, sourceTermGate, halfWeights_fin, domainHalf_sq _ radius_bounds.1.le,
      edgeFactors_fin, hc, if_true]
  · unfold pathSource
    apply Finset.sum_congr rfl
    intro x _
    simp only [sourceTerm, sourceTermGate, halfWeights_fin, domainHalf_sq _ radius_bounds.1.le,
      edgeFactors_fin, hc, Bool.false_eq_true, if_false]

/-- Polynomial form of the same actual finite component source. -/
def componentPolynomial {m r p : ℕ} (c : Component m r p) : Polynomial ℕ :=
  ∑ x : Fin (edgeCount c + 1) → BoundedState,
    if Allowed c x then Polynomial.X ^ (∑ j, (x j).val) else 0

lemma componentMass_eq_eval {m r p : ℕ} (c : Component m r p) :
    componentMass c = (componentPolynomial c).eval₂ (Nat.castRingHom ℝ) radius := by
  rw [componentMass_eq_gated_sum]
  unfold componentPolynomial
  rw [Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Allowed c x <;> simp [hx]

end ActualComponent
end SubmittedGenus.CapFiveMass
