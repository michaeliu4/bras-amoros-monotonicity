import Results.Genus.FiniteComparison.AllGenusOmittedSource
import Results.Genus.FiniteComparison.RangeSourceBridge

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.FiniteComparison.RetainedPrefix
open RawGraph RawGraph.SignedCounterexample SourceBoxes OmittedSource AllGenusOmittedSource RangeSourceBridge

lemma pivot_sum_301 (p g : ℕ) (hp : p<301) :
    (∑ r ∈ Finset.range 301,fixedPivotCoeff r p g)=
      ∑ r ∈ Finset.Ico 1 p,fixedPivotCoeff r p g := by
  have he : (∑ r ∈ Finset.range 301,fixedPivotCoeff r p g)=
      ∑ r ∈ Finset.range p,fixedPivotCoeff r p g := by
    apply sum_range_same
    · intro r hr; exact fixedPivotCoeff_invalid (Or.inr (by omega))
    · intro r hr; exact fixedPivotCoeff_invalid (Or.inr hr)
  rw [he]
  by_cases hz : p=0
  · subst p; simp
  · rw [←Finset.sum_range_add_sum_Ico (fun r => fixedPivotCoeff r p g) (show 1≤p by omega)]
    simp [fixedPivotCoeff_invalid (r:=0) (Or.inl rfl)]

/-- The finite source polynomial used by the original supplement is exactly
C_g(300), including all multiplicities, for every stored degree0 through897. -/
theorem retainedFour_eq_prefix (g : ℕ) (hg : g≤897) : retainedFour g=retainedPrefix g := by
  unfold retainedFour retainedPrefix
  calc
    _ = ∑ m ∈ Finset.range 598,∑ p ∈ Finset.range 301,∑ r ∈ Finset.range 301,
        (rawPolynomial m r p 4).coeff g := by
      apply Finset.sum_congr rfl; intro m hm; rw [Finset.sum_comm]
    _ = ∑ p ∈ Finset.range 301,∑ r ∈ Finset.range 301,∑ m ∈ Finset.range 598,
        (rawPolynomial m r p 4).coeff g := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro p hp; rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [multiplicity_sum _ _ _ hg]
      apply Finset.sum_congr rfl; intro p hp
      exact pivot_sum_301 p g (Finset.mem_range.mp hp)

theorem originalFour_range_eq_prefix (g : ℕ) (hg : g≤897) :
    (PackedAcceptance.rangePolynomial 597 300 4).coeff g=retainedPrefix g := by
  rw [originalFour_range,retainedFour_eq_prefix g hg]

#print axioms originalFour_range_eq_prefix
end SubmittedGenus.FiniteComparison.RetainedPrefix
