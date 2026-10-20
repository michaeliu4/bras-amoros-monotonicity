import Results.Genus.CapFourMass.RetainedTailSum

/-! Unreindexed vertex-weight product for gluing the canonical finite tail sum
to the actual physical vertex and edge partitions. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.CarryLocalization
open FixedPivot
attribute [local instance] Classical.propDecidable Classical.decEq

variable (N d : ℕ) (hN : d<N) (hbig : 2*d<N) (a : CarryRepresentative N d hN)

/-- The transfer reindexing has exactly the physical product on Fin tailSize;
only the edge-endpoint casts retain the explicit value-preserving equivalence. -/
theorem retainedTailTerm_explicit (j : Mode) (left right : State)
    (y : Fin (carryTailSize N d hN a)→State) :
    retainedTailTerm N d hN hbig a j left right y=
      (∏ t : Fin (carryTailSize N d hN a),
        if (y t).val+1 ≤ 3 ∧
          ((a.val=portPartner N d hN a.val ∧ t.val+1=carryTailSize N d hN a) → 2 ≤ (y t).val+1)
        then radius^((y t).val+1) else 0)*
      (∏ k : Fin (carryTailSize N d hN a-1),normalizedModeEdge j
        (y (retainedTailIndex N d hN hbig a k.castSucc))
        (y (retainedTailIndex N d hN hbig a k.succ)))*
      (if a.val.val+1=d then 1 else normalizedModeEdge j left
        (y (retainedTailIndex N d hN hbig a 0)))*
      (if a.val=portPartner N d hN a.val then 1 else normalizedModeEdge j
        (y (retainedTailIndex N d hN hbig a (Fin.last _))) right) := by
  unfold retainedTailTerm normalizedTailTerm tailInitial
  simp only [Function.comp_apply]
  congr 1
  congr 1
  congr 1
  refine Fintype.prod_equiv (retainedTailIndex N d hN hbig a) _ _ ?_
  intro t
  have hs : carryTailSize N d hN a-1+1=carryTailSize N d hN a := by
    have:=carryTailSize_positive N d hN hbig a
    omega
  have ht : (retainedTailIndex N d hN hbig a t).val=t.val := rfl
  have he : (t.val+1=carryTailSize N d hN a-1+1) ↔
      ((retainedTailIndex N d hN hbig a t).val+1=carryTailSize N d hN a) := by
    omega
  simp only [he]

end SubmittedGenus.CapFourMass.CarryLocalization
