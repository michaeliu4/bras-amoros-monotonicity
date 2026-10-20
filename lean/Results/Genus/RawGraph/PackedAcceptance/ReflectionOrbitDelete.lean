import Results.Genus.RawGraph.PackedAcceptance.ReflectionDelete

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionOrbitDelete

/-- Explicit omission of an interior or endpoint index below the last slot. -/
def omitEquiv {n : ℕ} (cut : Fin (n+1)) :
    Fin (n+1) ≃ {j : Fin (n+2) // j≠cut.castSucc} where
  toFun := fun j=>⟨cut.castSucc.succAbove j,Fin.succAbove_ne _ _⟩
  invFun := fun j=>cut.predAbove j.val
  left_inv := by intro j; exact Fin.predAbove_succAbove cut j
  right_inv := by intro j; apply Subtype.ext; exact Fin.succAbove_predAbove j.property

/-- Restrict any explicit finite order by deleting the image of one index. -/
def deletePoint {n : ℕ} {A : Type*} (e : Fin (n+2) ≃ A) (cut : Fin (n+1)) :
    Fin (n+1) ≃ {x : A // x≠e cut.castSucc} :=
  (omitEquiv cut).trans (e.subtypeEquiv (fun j=>by
    constructor
    · intro hj he; exact hj (e.injective he)
    · intro hj he; exact hj (congrArg e he)))

lemma deletePoint_val {n : ℕ} {A : Type*} (e : Fin (n+2) ≃ A) (cut : Fin (n+1))
    (j : Fin (n+1)) : (deletePoint e cut j).val=e (cut.castSucc.succAbove j) := rfl

/-- Delete a zero-valued member of any finite residue subtype. -/
def deleteSubtypeZero {n : ℕ} {B : Type*} [Zero B] {P : B→Prop}
    (e : Fin (n+2) ≃ Subtype P) (cut : Fin (n+1)) (hz : (e cut.castSucc).val=0) :
    Fin (n+1) ≃ {x : Subtype P // x.val≠0} :=
  (deletePoint e cut).trans (Equiv.subtypeEquivRight (fun x=>by
    apply not_congr
    constructor
    · intro h; exact (congrArg Subtype.val h).trans hz
    · intro h; apply Subtype.ext; exact h.trans hz.symm))

lemma deleteSubtypeZero_val {n : ℕ} {B : Type*} [Zero B] {P : B→Prop}
    (e : Fin (n+2) ≃ Subtype P) (cut : Fin (n+1)) (hz : (e cut.castSucc).val=0)
    (j : Fin (n+1)) : (deleteSubtypeZero e cut hz j).val.val=(e (cut.castSucc.succAbove j)).val := rfl

#print axioms deleteSubtypeZero
#print axioms omitEquiv
#print axioms deletePoint
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionOrbitDelete
