import Results.Genus.CapFourMass.PivotPrefix
import Results.Genus.CapFourMass.MasterCoordinates
import Results.Genus.CapFourMass.OriginalPrefixTargets

/-! Finite pivot prefixes of infinite multiplicity series, with convergence
proved before any infinite regrouping. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass
attribute [local instance] Classical.propDecidable

def prefixSeries (P : ℕ) (S : ℕ→ℕ→ℕ→ℝ) (ij : TailIndex×ℕ) : ℝ :=
  if ij.1.pivot.p ≤ P then S ij.1.pivot.r ij.1.pivot.p ij.2 else 0

lemma prefixSeries_nonneg (P : ℕ) (S : ℕ→ℕ→ℕ→ℝ)
    (hn : ∀ r p,1 ≤ r → r < p → ∀ n,0 ≤ S r p n) (ij : TailIndex×ℕ) :
    0 ≤ prefixSeries P S ij := by
  unfold prefixSeries
  split_ifs
  · exact hn _ _ ij.1.pivot.toPivot.property.1 ij.1.pivot.toPivot.property.2 _
  · rfl

lemma prefixSeries_rows (P : ℕ) (S : ℕ→ℕ→ℕ→ℝ) (i : TailIndex) :
    (∑' n,prefixSeries P S (i,n))=
      prefixIndicator P (fun r p => ∑' n,S r p n) (tailPivotEquiv i) := by
  unfold prefixSeries prefixIndicator
  change (∑' n,if i.pivot.p ≤ P then S i.pivot.r i.pivot.p n else 0)=
    if i.pivot.p ≤ P then (∑' n,S i.pivot.r i.pivot.p n) else 0
  split_ifs <;> simp

lemma prefixSeries_summable (P : ℕ) (S : ℕ→ℕ→ℕ→ℝ)
    (hn : ∀ r p,1 ≤ r → r < p → ∀ n,0 ≤ S r p n)
    (hs : ∀ r p,1 ≤ r → r < p → Summable (S r p)) :
    Summable (prefixSeries P S) := by
  apply (summable_prod_of_nonneg (prefixSeries_nonneg P S hn)).mpr
  constructor
  · intro i
    have hpi:=i.pivot.toPivot.property
    change 1  ≤  i.pivot.r ∧ i.pivot.r < i.pivot.p at hpi
    by_cases hi : i.pivot.p  ≤  P
    · simpa only [prefixSeries,hi,if_true] using hs i.pivot.r i.pivot.p hpi.1 hpi.2
    · simpa only [prefixSeries,hi,if_false] using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
  · have he : Summable (fun i : TailIndex =>
        prefixIndicator P (fun r p => ∑' n,S r p n) (tailPivotEquiv i)) :=
      (tailPivotEquiv.summable_iff (f := prefixIndicator P (fun r p => ∑' n,S r p n))).mpr
        (prefixIndicator_summable P (fun r p => ∑' n,S r p n))
    exact he.congr (fun i => (prefixSeries_rows P S i).symm)

lemma prefixSeries_tsum (P : ℕ) (S : ℕ→ℕ→ℕ→ℝ)
    (hn : ∀ r p,1 ≤ r → r < p → ∀ n,0 ≤ S r p n)
    (hs : ∀ r p,1 ≤ r → r < p → Summable (S r p)) :
    (∑' ij,prefixSeries P S ij)=
      ∑ p ∈ Finset.range (P+1),∑ r ∈ Finset.Ico 1 p,∑' n,S r p n := by
  rw [(prefixSeries_summable P S hn hs).tsum_prod]
  simp_rw [prefixSeries_rows]
  rw [tailPivotEquiv.tsum_eq,prefixIndicator_tsum,pivotPrefix_eq_rows]

lemma purePrefix_summable (P : ℕ) :
    Summable (prefixSeries P (fun r p => sourcePureSeries r (p-r))) :=
  prefixSeries_summable P _ (fun r p _ _ => sourcePureSeries_nonneg r (p-r))
    (fun r p _ hp => (sourcePureSeries_hasSum r (p-r) (by omega)).summable)

lemma purePrefix_tsum (P : ℕ) :
    (∑' ij,prefixSeries P (fun r p => sourcePureSeries r (p-r)) ij)=originalPurePrefix P := by
  rw [prefixSeries_tsum P _ (fun r p _ _ => sourcePureSeries_nonneg r (p-r))
    (fun r p _ hp => (sourcePureSeries_hasSum r (p-r) (by omega)).summable)]
  exact (originalPurePrefix_eq_source_sum P).symm

lemma mixedPrefix_summable (P : ℕ) :
    Summable (prefixSeries P (fun r p => sourceMixedSeries r (p-r))) :=
  prefixSeries_summable P _ (fun r p _ _ => sourceMixedSeries_nonneg r (p-r))
    (fun r p _ hp => (sourceMixedSeries_complete r (p-r) (by omega)).1)

lemma mixedPrefix_tsum_le (P : ℕ) :
    (∑' ij,prefixSeries P (fun r p => sourceMixedSeries r (p-r)) ij) ≤ originalMixedPrefix P := by
  rw [prefixSeries_tsum P _ (fun r p _ _ => sourceMixedSeries_nonneg r (p-r))
    (fun r p _ hp => (sourceMixedSeries_complete r (p-r) (by omega)).1)]
  exact originalMixed_source_sum_le P

#print axioms purePrefix_tsum
#print axioms mixedPrefix_tsum_le
end SubmittedGenus.CapFourMass
