import Results.Genus.CapFiveMass.General.Control

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass.General
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer LocalSource MatrixSource ActualComponent

def sourceTransfer (H : Control) {m : ℕ} (r p : ℕ) (i j : Fin (m - 1)) : MatrixBounds.Controlled (ι := BoundedState) :=
  if StrongEdge r p i j then strongTransferSix H else carryTransferSix H

lemma sourceTransfer_nonneg (H : Control) {m r p : ℕ} (i j : Fin (m - 1)) (v w : BoundedState) :
    0 ≤ (sourceTransfer H r p i j).matrix v w := by
  unfold sourceTransfer
  split_ifs <;> exact thresholdSix_nonneg _ _ v w

/-- Exact reflection geometry supplies the carry alphabet cutoff. -/

lemma split_edge_le_transfer (H : Control) {m r p : ℕ} (hp : Parameters m r p 5)
    {i j : Fin (m - 1)} (hadj : (RawGraph.Topology.rawGraph m r p).Adj i j)
    (v w : BoundedState) :
    domainHalf r p i H.z v * edgeFactor r p i j v w * domainHalf r p j H.z w ≤
      (sourceTransfer H r p i j).matrix v w := by
  have hi : IsFree r p i := hadj.2.1
  have hj : IsFree r p j := hadj.2.2.1
  by_cases hdi : Domain r p 5 i v.val
  swap
  · simpa [domainHalf, hdi] using sourceTransfer_nonneg H i j v w
  by_cases hdj : Domain r p 5 j w.val
  swap
  · simpa [domainHalf, hdj] using sourceTransfer_nonneg H i j v w
  by_cases hedge : edgeBound r p 5 i j ≤ v.val + w.val
  swap
  · simpa [edgeFactor, hedge] using sourceTransfer_nonneg H i j v w
  have hv0 : v ≠ 0 := by intro he; exact domain_zero_impossible hi (by simpa [he] using hdi)
  have hw0 : w ≠ 0 := by intro he; exact domain_zero_impossible hj (by simpa [he] using hdj)
  obtain ⟨v, rfl⟩ := Fin.exists_succ_eq.mpr hv0
  obtain ⟨w, rfl⟩ := Fin.exists_succ_eq.mpr hw0
  have hi' : ¬ IsPivot r p i := hi
  have hj' : ¬ IsPivot r p j := hj
  by_cases hs : StrongEdge r p i j
  · have hs' : physical i + physical j = r ∨ physical i + physical j = p := hs
    have he : edgeBound r p 5 i j = 5 := by simp [edgeBound, hi', hj', hadj.1, hs']
    have hel : eligible 5 v w := by
      rw [he] at hedge
      have hv := v.isLt
      have hw := w.isLt
      simp only [eligible, Fin.val_succ] at *
      omega
    simp only [Fin.val_succ] at hdi hdj hedge
    simp [domainHalf, edgeFactor, hdi, hdj, hedge, sourceTransfer, hs, strongTransferSix,
      extendControlled, strongTransfer, zeroExtend, thresholdMatrix, hel, vertexHalf]
  · have hc : physical i + physical j = m + r ∨ physical i + physical j = m + p := by
      rcases hadj.2.2.2 with hr | hp
      · rcases hr with hr | hr
        · exact (hs (Or.inl hr)).elim
        · exact Or.inl hr
      · rcases hp with hp | hp
        · exact (hs (Or.inr hp)).elim
        · exact Or.inr hp
    have hs' : ¬ (physical i + physical j = r ∨ physical i + physical j = p) := hs
    have he : edgeBound r p 5 i j = 4 := by simp [edgeBound, hi', hj', hadj.1, hs', hc]
    have hvi := domain_carry_bound hi hc hp.2.1 hdi
    have hwj := domain_carry_bound (j := i) hj (by simpa only [Nat.add_comm (physical i) (physical j)] using hc) hp.2.1 hdj
    have hel : eligible 4 v w := by
      rw [he] at hedge
      simp only [eligible, Fin.val_succ] at *
      omega
    simp only [Fin.val_succ] at hdi hdj hedge
    simp [domainHalf, edgeFactor, hdi, hdj, hedge, sourceTransfer, hs, carryTransferSix,
      extendControlled, carryTransfer, zeroExtend, thresholdMatrix, hel, vertexHalf]

end SubmittedGenus.CapFiveMass.General
