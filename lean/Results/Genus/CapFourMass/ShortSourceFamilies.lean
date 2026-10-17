import Results.Genus.CapFourMass.FinitePrefixFamilies

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass
attribute [local instance] Classical.propDecidable

lemma finiteHead_hasSum (k : ℕ) (f : ℕ→ℝ) :
    HasSum (fun n => if n < k then f n else 0) (∑ n ∈ Finset.range k,f n) := by
  have hh : HasSum (fun n => if n < k then f n else 0)
      (∑ n ∈ Finset.range k,if n < k then f n else 0) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      have h : ¬n < k := by simpa only [Finset.mem_range] using hn
      exact if_neg h)
  have he : (∑ n ∈ Finset.range k,if n < k then f n else 0)=∑ n ∈ Finset.range k,f n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact if_pos (Finset.mem_range.mp hn)
  rwa [he] at hh

def shortSeries (r p n : ℕ) : ℝ :=
  if n < p then Polynomial.eval₂ (Nat.castRingHom ℝ) radius
    (RawGraph.rawPolynomial (p+1+n) r p 4) else 0

lemma shortSeries_nonneg (r p : ℕ) (hr : 1  ≤  r) (hp : r < p) (n : ℕ) : 0  ≤  shortSeries r p n := by
  unfold shortSeries
  split_ifs
  · exact raw_eval_nonneg ⟨hr,hp,by omega,by decide⟩
  · rfl
lemma shortSeries_summable (r p : ℕ) : Summable (shortSeries r p) := (finiteHead_hasSum p _).summable
lemma shortSeries_tsum (r p : ℕ) :
    (∑' n,shortSeries r p n)=∑ m ∈ Finset.Ico (p+1) (2*p+1),
      Polynomial.eval₂ (Nat.castRingHom ℝ) radius (RawGraph.rawPolynomial m r p 4) := by
  unfold shortSeries
  rw [(finiteHead_hasSum p (fun n => Polynomial.eval₂ (Nat.castRingHom ℝ) radius
    (RawGraph.rawPolynomial (p+1+n) r p 4))).tsum_eq]
  rw [Finset.sum_Ico_eq_sum_range]
  have he : 2*p+1-(p+1)=p := by omega
  rw [he]

lemma shortPrefix_summable (P : ℕ) : Summable (prefixSeries P shortSeries) :=
  prefixSeries_summable P _ shortSeries_nonneg (fun r p _ _ => shortSeries_summable r p)
lemma shortPrefix_tsum (P : ℕ) :
    (∑' ij,prefixSeries P shortSeries ij)=originalShortPrefix P := by
  rw [prefixSeries_tsum P _ shortSeries_nonneg (fun r p _ _ => shortSeries_summable r p)]
  simp only [shortSeries_tsum,originalShortPrefix]

def shortOmittedFamily (P : ℕ) (ij : TailIndex×ℕ) : ℝ :=
  if P < ij.1.pivot.p then shortSeries ij.1.pivot.r ij.1.pivot.p ij.2 else 0
lemma shortOmittedFamily_nonneg (P : ℕ) (ij : TailIndex×ℕ) : 0  ≤  shortOmittedFamily P ij := by
  unfold shortOmittedFamily
  split_ifs
  · exact shortSeries_nonneg _ _ ij.1.pivot.toPivot.property.1 ij.1.pivot.toPivot.property.2 _
  · rfl
lemma shortOmittedFamily_row (P : ℕ) (i : TailIndex) :
    (∑' n,shortOmittedFamily P (i,n))=shortOmittedSource P i := by
  unfold shortOmittedFamily shortOmittedSource
  split_ifs
  · unfold shortSeries
    rw [(finiteHead_hasSum i.pivot.p (fun n => Polynomial.eval₂ (Nat.castRingHom ℝ) radius
      (RawGraph.rawPolynomial (i.pivot.p+1+n) i.pivot.r i.pivot.p 4))).tsum_eq]
    exact (Fin.sum_univ_eq_sum_range (fun n => Polynomial.eval₂ (Nat.castRingHom ℝ) radius
      (RawGraph.rawPolynomial (i.pivot.p+1+n) i.pivot.r i.pivot.p 4)) i.pivot.p).symm
  · simp
lemma shortOmittedFamily_bound (P : ℕ) :
    Summable (shortOmittedFamily P) ∧ (∑' ij,shortOmittedFamily P ij)  ≤  shortTailExpression P := by
  have ht:=actual_short_omitted_sum P
  have hs : Summable (shortOmittedFamily P) := by
    apply (summable_prod_of_nonneg (shortOmittedFamily_nonneg P)).mpr
    constructor
    · intro i
      by_cases hi : P < i.pivot.p
      · simpa only [shortOmittedFamily,hi,if_true] using shortSeries_summable i.pivot.r i.pivot.p
      · simpa only [shortOmittedFamily,hi,if_false] using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
    · simpa only [shortOmittedFamily_row] using ht.1
  refine ⟨hs,?_⟩
  rw [hs.tsum_prod]
  simpa only [shortOmittedFamily_row] using ht.2

#print axioms shortPrefix_tsum
#print axioms shortOmittedFamily_bound
end SubmittedGenus.CapFourMass
