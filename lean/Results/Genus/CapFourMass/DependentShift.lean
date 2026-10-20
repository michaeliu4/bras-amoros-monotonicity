import Results.Genus.CapFourMass.GenuineSource

/-! Exact insertion of a pivot-dependent initial zero interval. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass
attribute [local instance] Classical.propDecidable

variable {α : Type*}
def dependentShiftEquiv (k : α→ℕ) : (α×ℕ) ≃ {ij : α×ℕ // k ij.1 ≤ ij.2} where
  toFun ij := ⟨(ij.1,k ij.1+ij.2),by dsimp; omega⟩
  invFun ij := (ij.val.1,ij.val.2-k ij.val.1)
  left_inv ij := by apply Prod.ext <;> dsimp <;> omega
  right_inv ij := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      have:=ij.property
      omega

def extendPast (k : α→ℕ) (f : α×ℕ→ℝ) (ij : α×ℕ) : ℝ :=
  if k ij.1 ≤ ij.2 then f (ij.1,ij.2-k ij.1) else 0

lemma extendPast_summable (k : α→ℕ) (f : α×ℕ→ℝ) (hs : Summable f) :
    Summable (extendPast k f) := by
  have hsub : Summable (fun ij : {ij : α×ℕ // k ij.1 ≤ ij.2} =>
      f (ij.val.1,ij.val.2-k ij.val.1)) :=
    (dependentShiftEquiv k).symm.summable_iff.mpr hs
  have hi := (summable_subtype_iff_indicator (s := {ij : α×ℕ | k ij.1 ≤ ij.2})
      (f := fun ij : α×ℕ => f (ij.1,ij.2-k ij.1))).mp hsub
  exact hi.congr (fun ij => by simp [extendPast,Set.indicator])

lemma extendPast_tsum (k : α→ℕ) (f : α×ℕ→ℝ) (hs : Summable f) :
    (∑' ij,extendPast k f ij)=∑' ij,f ij := by
  have hsub : HasSum (fun ij : {ij : α×ℕ // k ij.1 ≤ ij.2} =>
      f (ij.val.1,ij.val.2-k ij.val.1)) (∑' ij,f ij) :=
    (dependentShiftEquiv k).symm.hasSum_iff.mpr hs.hasSum
  have hi := (hasSum_subtype_iff_indicator (s := {ij : α×ℕ | k ij.1 ≤ ij.2})
      (f := fun ij : α×ℕ => f (ij.1,ij.2-k ij.1))).mp hsub
  have he : HasSum (extendPast k f) (∑' ij,f ij) :=
    hi.congr (fun ij => by simp [extendPast,Set.indicator])
  exact he.tsum_eq

#print axioms extendPast_summable
#print axioms extendPast_tsum
end SubmittedGenus.CapFourMass
