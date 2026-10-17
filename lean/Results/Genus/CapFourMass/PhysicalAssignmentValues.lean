import Results.Genus.CapFourMass.PhysicalSourceFactorization
import Results.Genus.CapFourMass.RetainedTailPositions
import Results.Genus.CapFourMass.RetainedPortProduct

/-! Exact evaluation of reindexed physical states at core, tail and port vertices. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq
section Values
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d)
variable (core : CoreAt hN c→State)
variable (tail : (a : ModeFiber hr hN hbig c)→Fin (carryTailSize N d hN a.val)→State)

@[simp] lemma physicalAssignment_core (k : CoreAt hN c) :
    (physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail) (ownedCoreVertex hN c k)=core k := by
  change (physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)
    (componentVertexEquiv hr hd hN hbig c (.inl k))=core k
  simp only [physicalAssignmentEquiv,Equiv.coe_fn_symm_mk,Equiv.symm_apply_apply]

@[simp] lemma physicalAssignment_tail (a : ModeFiber hr hN hbig c)
    (t : Fin (carryTailSize N d hN a.val)) :
    (physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)
      (componentVertexEquiv hr hd hN hbig c (.inr ⟨a,t⟩))=tail a t := by
  simp only [physicalAssignmentEquiv,Equiv.coe_fn_symm_mk,Equiv.symm_apply_apply]

lemma ownedRunVertex_tail (a : ModeFiber hr hN hbig c)
    (t : Fin (carryTailSize N d hN a.val)) :
    ownedRunVertex hr hd hN hbig c a (retainedTailPosition N d hN a.val t)=
      componentVertexEquiv hr hd hN hbig c (.inr ⟨a,t⟩) := by
  apply Subtype.ext
  exact retainedTailPosition_vertex hr hN a.val t

@[simp] lemma physicalAssignment_run_tail (a : ModeFiber hr hN hbig c)
    (t : Fin (carryTailSize N d hN a.val)) :
    (physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)
      (ownedRunVertex hr hd hN hbig c a (retainedTailPosition N d hN a.val t))=tail a t := by
  rw [ownedRunVertex_tail,physicalAssignment_tail]

lemma ownedRunVertex_port (a : ModeFiber hr hN hbig c)
    (t : Fin (freeCarrySize N d hN a.val)) (q : PortAt hr hN hbig c)
    (hq : q.val.val+1≠d) (ht : freeCarryLabel N d hN a.val t.val=q.val.val+1) :
    ownedRunVertex hr hd hN hbig c a t=ownedCoreVertex hN c (portCoreAt hr hd hN hbig q hq) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Fin.ext
  have hv:=runVertex_physical hr hN a.val t
  rw [ht] at hv
  change (runVertex hr hN a.val t).val.val=r+q.val.val
  unfold physical at hv
  omega

lemma physicalAssignment_run_port (a : ModeFiber hr hN hbig c)
    (t : Fin (freeCarrySize N d hN a.val)) (q : PortAt hr hN hbig c)
    (hq : q.val.val+1≠d) (ht : freeCarryLabel N d hN a.val t.val=q.val.val+1) :
    (physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)
      (ownedRunVertex hr hd hN hbig c a t)=localPortState hr hd hN hbig c core q := by
  rw [ownedRunVertex_port hr hd hN hbig c a t q hq ht,physicalAssignment_core,
    localPortState,dif_neg hq]

end Values
end SubmittedGenus.CapFourMass.CarryLocalization
