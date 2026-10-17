import Results.Genus.CapFourMass.PivotCoordinates
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Exact finite pivot prefixes, independent of any numerical evaluator. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass
attribute [local instance] Classical.propDecidable

abbrev BoundedPivot (P : ℕ) := {q : PositivePivot // q.val.2≤P}
abbrev PrefixRows (P : ℕ) := Σ p : Fin (P+1), {r : Fin p.val // 1≤r.val}

def boundedPivotEquiv (P : ℕ) : BoundedPivot P ≃ PrefixRows P where
  toFun q := ⟨⟨q.val.val.2,by have:=q.property; omega⟩,
    ⟨⟨q.val.val.1,q.val.property.2⟩,q.val.property.1⟩⟩
  invFun q := ⟨⟨(q.2.val.val,q.1.val),q.2.property,q.2.val.isLt⟩,by change q.1.val≤P; have:=q.1.isLt; omega⟩
  left_inv q := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv q := by rcases q with ⟨⟨p,hp⟩,⟨⟨r,hr⟩,hpos⟩⟩; rfl

instance (P : ℕ) : Fintype (BoundedPivot P) := Fintype.ofEquiv (PrefixRows P) (boundedPivotEquiv P).symm

def pivotPrefix (P : ℕ) (F : ℕ→ℕ→ℝ) : ℝ :=
  ∑ q : BoundedPivot P,F q.val.val.1 q.val.val.2

def prefixIndicator (P : ℕ) (F : ℕ→ℕ→ℝ) (q : PositivePivot) : ℝ :=
  if q.val.2≤P then F q.val.1 q.val.2 else 0

lemma prefixIndicator_summable (P : ℕ) (F : ℕ→ℕ→ℝ) : Summable (prefixIndicator P F) := by
  have hs : Summable (fun q : BoundedPivot P => F q.val.val.1 q.val.val.2) :=
    (hasSum_fintype _).summable
  have hi := (summable_subtype_iff_indicator (s := {q : PositivePivot | q.val.2≤P})
      (f := fun q : PositivePivot => F q.val.1 q.val.2)).mp hs
  exact hi.congr (fun q => by simp [prefixIndicator,Set.indicator])

lemma prefixIndicator_tsum (P : ℕ) (F : ℕ→ℕ→ℝ) :
    (∑' q,prefixIndicator P F q)=pivotPrefix P F := by
  have hs : HasSum (fun q : BoundedPivot P => F q.val.val.1 q.val.val.2) (pivotPrefix P F) :=
    hasSum_fintype _
  have hi := (hasSum_subtype_iff_indicator (s := {q : PositivePivot | q.val.2≤P})
      (f := fun q : PositivePivot => F q.val.1 q.val.2)).mp hs
  have he : HasSum (prefixIndicator P F) (pivotPrefix P F) :=
    hi.congr (fun q => by simp [prefixIndicator,Set.indicator])
  exact he.tsum_eq

lemma prefix_row_sum (p : ℕ) (F : ℕ→ℝ) :
    (∑ r : {r : Fin p // 1≤r.val},F r.val.val)=∑ r ∈ Finset.Ico 1 p,F r := by
  rw [←Finset.sum_subtype (Finset.univ.filter (fun r : Fin p => 1≤r.val)) (by simp)
    (fun r : Fin p => F r.val),Finset.sum_filter]
  change (∑ r : Fin p,(fun n : ℕ => if 1≤n then F n else 0) r.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if 1≤n then F n else 0) p]
  rw [←Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
  omega

lemma pivotPrefix_eq_rows (P : ℕ) (F : ℕ→ℕ→ℝ) :
    pivotPrefix P F=∑ p ∈ Finset.range (P+1),∑ r ∈ Finset.Ico 1 p,F r p := by
  unfold pivotPrefix
  rw [←(boundedPivotEquiv P).symm.sum_comp (fun q : BoundedPivot P => F q.val.val.1 q.val.val.2)]
  rw [Fintype.sum_sigma]
  change (∑ p : Fin (P+1),∑ r : {r : Fin p.val // 1≤r.val},F r.val.val p.val)=_
  calc
    _ = ∑ p : Fin (P+1),∑ r ∈ Finset.Ico 1 p.val,F r p.val := by
      apply Finset.sum_congr rfl
      intro p hp
      exact prefix_row_sum p.val (fun r => F r p.val)
    _ = _ := Fin.sum_univ_eq_sum_range (fun p : ℕ => ∑ r ∈ Finset.Ico 1 p,F r p) (P+1)

#print axioms pivotPrefix_eq_rows
end SubmittedGenus.CapFourMass
