import Results.Genus.CapFourMass.RetainedEdgeProduct
import Results.Genus.CapFourMass.TailUnaryFactor

/-! Canonical retained edge products read exactly their own tail states and
surviving physical core-port states. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq
section Values
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d) (a : ModeFiber hr hN hbig c)
variable (choice : Option (CarryRepresentative N d hN)→Mode)
variable (core : CoreAt hN c→State)
variable (tail : (a : ModeFiber hr hN hbig c)→Fin (carryTailSize N d hN a.val)→State)

lemma runEdgeProduct_eq_retained :
    runEdgeProduct hr hd hN hbig c (sourceSignedKernel hd hN choice)
      ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)) a=
      (∏k : Fin (carryTailSize N d hN a.val-1),normalizedModeEdge (choice (some a.val))
        (tail a (retainedTailIndex N d hN hbig a.val k.castSucc))
        (tail a (retainedTailIndex N d hN hbig a.val k.succ)))*
      (if a.val.val.val+1=d then 1 else normalizedModeEdge (choice (some a.val))
        (localPortState hr hd hN hbig c core (firstModePort hr hN hbig c a))
        (tail a (retainedTailIndex N d hN hbig a.val 0)))*
      (if a.val.val=portPartner N d hN a.val.val then 1 else normalizedModeEdge (choice (some a.val))
        (tail a (retainedTailIndex N d hN hbig a.val (Fin.last _)))
        (localPortState hr hd hN hbig c core (lastModePort hr hN hbig c a))) := by
  rw [runEdgeProduct_split]
  apply congrArg₂ (·*·)
  · apply congrArg₂ (·*·)
    · apply Finset.prod_congr rfl
      intro k _
      have hleft:=runState_tail hr hd hN hbig c a core tail
        (retainedTailIndex N d hN hbig a.val k.castSucc)
      have hright:=runState_tail hr hd hN hbig c a core tail
        (retainedTailIndex N d hN hbig a.val k.succ)
      simp only [retainedTailIndex_val,Fin.val_castSucc,Fin.val_succ] at hleft hright
      rw [hleft,show k.val+(if a.val.val.val+1=d then 0 else 1)+1=
        (k.val+1)+(if a.val.val.val+1=d then 0 else 1) by omega,hright]
    · split_ifs with hp
      · rfl
      · rw [runState_first hr hd hN hbig c a core tail hp]
        have h:=runState_tail hr hd hN hbig c a core tail (retainedTailIndex N d hN hbig a.val 0)
        simp only [retainedTailIndex_val,Fin.val_zero,if_neg hp,Nat.zero_add] at h
        rw [h]
  · by_cases hf : a.val.val=portPartner N d hN a.val.val
    · rw [if_pos hf,if_pos hf]
    · rw [if_neg hf,if_neg hf]
      have h:=runState_tail hr hd hN hbig c a core tail (retainedTailIndex N d hN hbig a.val (Fin.last _))
      simp only [retainedTailIndex_val,Fin.val_last] at h
      rw [h,runState_last hr hd hN hbig c a core tail hf]

/-- The pointwise factor of one canonical tail is exactly the complete
retained-tail term, with no sum or absolute value moved past the core. -/
theorem physical_tail_factor :
    tailUnaryProduct hr hd hN hbig c ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)) a*
      runEdgeProduct hr hd hN hbig c (sourceSignedKernel hd hN choice)
        ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)) a=
      retainedTailTerm N d hN hbig a.val (choice (some a.val))
        (localPortState hr hd hN hbig c core (firstModePort hr hN hbig c a))
        (localPortState hr hd hN hbig c core (lastModePort hr hN hbig c a)) (tail a) := by
  rw [tailUnaryProduct_eq_retained,runEdgeProduct_eq_retained,retainedTailTerm_explicit]
  ring

end Values
end SubmittedGenus.CapFourMass.CarryLocalization
