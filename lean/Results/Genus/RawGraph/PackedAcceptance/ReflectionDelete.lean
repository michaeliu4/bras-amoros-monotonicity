import Results.Genus.RawGraph.PackedAcceptance.ReflectionConsecutive
import Results.Genus.RawGraph.PackedAcceptance.LayoutCheck

/-! Removing the zero residue from an explicitly ordered reflection graph.
The finite permutation adapter is independent of the reflection parameters. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionDelete

lemma image_ne_zero {n : ℕ} (e : Fin (n+1)≃Fin (n+1)) (cut : Fin n)
    (hz : e cut.castSucc=0) (j : Fin n) : e (cut.castSucc.succAbove j)≠0 := by
  intro h
  exact Fin.succAbove_ne _ _ (e.injective (h.trans hz.symm))

/-- Delete one position and its zero image from a computable permutation. -/
def removeZero {n : ℕ} (e : Fin (n+1)≃Fin (n+1)) (cut : Fin n)
    (hz : e cut.castSucc=0) : Fin n ≃ Fin n where
  toFun := fun j=>(e (cut.castSucc.succAbove j)).pred (image_ne_zero e cut hz j)
  invFun := fun u=>cut.predAbove (e.symm u.succ)
  left_inv := by
    intro j
    dsimp only
    rw [Fin.succ_pred,e.symm_apply_apply,Fin.predAbove_succAbove]
  right_inv := by
    intro u
    dsimp only
    have he : e.symm u.succ≠cut.castSucc := by
      intro h
      have h' := congrArg e h
      rw [e.apply_symm_apply,hz] at h'
      exact Fin.succ_ne_zero u h'
    apply Fin.succ_injective
    rw [Fin.succ_pred,Fin.succAbove_predAbove he,e.apply_symm_apply]

lemma removeZero_succ {n : ℕ} (e : Fin (n+1)≃Fin (n+1)) (cut : Fin n)
    (hz : e cut.castSucc=0) (j : Fin n) :
    (removeZero e cut hz j).succ=e (cut.castSucc.succAbove j) := Fin.succ_pred _ (image_ne_zero e cut hz j)

/-- Deleting a third position preserves every existing adjacent pair. -/
lemma adjacent_after_delete {n : ℕ} (cut : Fin n) (i j : Fin n)
    (h : (cut.castSucc.succAbove i).val+1=(cut.castSucc.succAbove j).val ∨
      (cut.castSucc.succAbove j).val+1=(cut.castSucc.succAbove i).val) :
    i.val+1=j.val ∨ j.val+1=i.val := by
  simp only [Fin.succAbove] at h
  split_ifs at h <;> simp_all only [Fin.val_castSucc,Fin.val_succ,Fin.lt_def] <;> omega

#print axioms removeZero
#print axioms removeZero_succ
#print axioms adjacent_after_delete
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionDelete
