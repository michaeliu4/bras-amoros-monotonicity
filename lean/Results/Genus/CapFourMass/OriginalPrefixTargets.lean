import Results.Genus.CapFourMass.SourceMultiplicitySums
import Results.Genus.CapFourMass.InputNumerics

/-! Exact finite source targets for the three remaining original prefix calculations.
These definitions retain the original pivot/multiplicity ranges and complete
core-before-absolute-value convention. No numerical acceptance is asserted here. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

/-- Every original short source graph: 1≤r<p≤P and p<m≤2p. -/
def originalShortPrefix (P : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (P+1), ∑ r ∈ Finset.Ico 1 p,
    ∑ m ∈ Finset.Ico (p+1) (2*p+1),
      Polynomial.eval₂ (Nat.castRingHom ℝ) radius (RawGraph.rawPolynomial m r p 4)

/-- Exactly two pure source bases per pivot pair, with the original denominator. -/
def originalPurePrefix (P : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (P+1), ∑ r ∈ Finset.Ico 1 p,
    (∑ j : Fin 2, sourcePureSeries r (p-r) j.val)/(1-(normalizer*lam)^2)

/-- Exactly 2(p-r) mixed source bases, after the complete core contraction. -/
def originalMixedPrefix (P : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (P+1), ∑ r ∈ Finset.Ico 1 p,
    (∑ j : Fin (2*(p-r)), sourceMixedSeries r (p-r) j.val)/
      (1-(normalizer*lam)^(2*(p-r))*rho^2)

/-- The finite pure target is the actual complete long-multiplicity mass over p≤P. -/
theorem originalPurePrefix_eq_source_sum (P : ℕ) :
    originalPurePrefix P=∑ p ∈ Finset.range (P+1), ∑ r ∈ Finset.Ico 1 p,
      ∑' n,sourcePureSeries r (p-r) n := by
  unfold originalPurePrefix
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro r hr
  exact (sourcePureSeries_hasSum r (p-r) (by have:=Finset.mem_Ico.mp hr; omega)).tsum_eq.symm

/-- The finite mixed target controls the actual complete long-multiplicity mass over p≤P. -/
theorem originalMixed_source_sum_le (P : ℕ) :
    (∑ p ∈ Finset.range (P+1), ∑ r ∈ Finset.Ico 1 p,
      ∑' n,sourceMixedSeries r (p-r) n)≤originalMixedPrefix P := by
  unfold originalMixedPrefix
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro r hr
  exact (sourceMixedSeries_complete r (p-r) (by have:=Finset.mem_Ico.mp hr; omega)).2

/-- The number of source graphs, independent of any approximate arithmetic. -/
def originalPureGraphCount (P : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (P+1), (p-1)*2
def originalShortGraphCount (P : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (P+1), (p-1)*p
def originalMixedGraphCount (P : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (P+1), ∑ r ∈ Finset.Ico 1 p,2*(p-r)

theorem pure_graph_count_is_exact (P : ℕ) :
    (∑ p ∈ Finset.range (P+1), ∑ _r ∈ Finset.Ico 1 p, Fintype.card (Fin 2))=
      originalPureGraphCount P := by
  simp [originalPureGraphCount]

theorem short_graph_count_is_exact (P : ℕ) :
    (∑ p ∈ Finset.range (P+1), ∑ _r ∈ Finset.Ico 1 p,
      (Finset.Ico (p+1) (2*p+1)).card)=originalShortGraphCount P := by
  unfold originalShortGraphCount
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.sum_const,Nat.card_Ico,smul_eq_mul]
  congr 1
  omega

theorem mixed_graph_count_is_exact (P : ℕ) :
    (∑ p ∈ Finset.range (P+1), ∑ r ∈ Finset.Ico 1 p,
      Fintype.card (Fin (2*(p-r))))=originalMixedGraphCount P := by
  simp [originalMixedGraphCount]

set_option maxRecDepth 10000 in
theorem original_pure_graph_count : originalPureGraphCount 400=159600 := by decide +kernel

set_option maxRecDepth 10000 in
theorem original_short_graph_count : originalShortGraphCount 100=333300 := by decide +kernel

set_option maxRecDepth 10000 in
theorem original_mixed_graph_count : originalMixedGraphCount 100=333300 := by decide +kernel

theorem original_short_mixed_graph_count :
    originalShortGraphCount 100+originalMixedGraphCount 100=666600 := by
  rw [original_short_graph_count,original_mixed_graph_count]

end SubmittedGenus.CapFourMass
