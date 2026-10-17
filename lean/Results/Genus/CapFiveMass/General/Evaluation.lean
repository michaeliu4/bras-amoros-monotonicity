import Results.Genus.CapFiveMass.General.Counts

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass.General
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer LocalSource MatrixSource ActualComponent

def sourceTermGate (H : Control) {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c + 1) → BoundedState) : ℝ :=
  (∏ j, if Domain r p 5 (vertex c j) (x j).val then H.z ^ (x j).val else 0) *
  (∏ j : Fin (edgeCount c), edgeFactor r p (vertex c j.castSucc) (vertex c j.succ) (x j.castSucc) (x j.succ)) *
  (if (freeComponentOrder m r p c).cycle = true then closeFactor c (x (Fin.last _)) (x 0) else 1)

lemma sourceTermGate_eq (H : Control) {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c + 1) → BoundedState) :
    sourceTermGate H c x = if Allowed c x then H.z ^ (∑ j, (x j).val) else 0 := by
  unfold sourceTermGate closeFactor edgeFactor
  rw [RawGraph.Factorization.prod_gate, RawGraph.Factorization.prod_gate]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const_one]
  unfold Allowed
  split_ifs <;> simp_all

lemma componentMass_eq_gated_sum (H : Control) {m r p : ℕ} (c : Component m r p) :
    componentMass H c = ∑ x : Fin (edgeCount c + 1) → BoundedState,
      if Allowed c x then H.z ^ (∑ j, (x j).val) else 0 := by
  simp_rw [← sourceTermGate_eq H]
  unfold componentMass
  split_ifs with hc
  · unfold cycleSource
    apply Finset.sum_congr rfl
    intro x _
    simp only [sourceTerm, sourceTermGate, halfWeights_fin H, domainHalf_sq _ H.z_pos.le,
      edgeFactors_fin, hc, if_true]
  · unfold pathSource
    apply Finset.sum_congr rfl
    intro x _
    simp only [sourceTerm, sourceTermGate, halfWeights_fin H, domainHalf_sq _ H.z_pos.le,
      edgeFactors_fin, hc, Bool.false_eq_true, if_false]

/-- Polynomial form of the same actual finite component source. -/

lemma componentMass_eq_eval (H : Control) {m r p : ℕ} (c : Component m r p) :
    componentMass H c = (componentPolynomial c).eval₂ (Nat.castRingHom ℝ) H.z := by
  rw [componentMass_eq_gated_sum H]
  unfold componentPolynomial
  rw [Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Allowed c x <;> simp [hx]

end SubmittedGenus.CapFiveMass.General
