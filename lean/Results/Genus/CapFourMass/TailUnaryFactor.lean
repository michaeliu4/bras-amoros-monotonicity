import Results.Genus.CapFourMass.PhysicalSourceFactorization
import Results.Genus.CapFourMass.RetainedTailExplicit

/-! Exact physical tail unary domains and products in the actual core/tail
assignment equivalence. No stronger endpoint or loop gate is introduced. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq

section Domains
variable {r N d : ℕ} (hr : 0<r) (hN : d<N)

lemma tail_carry_loop_iff (a : CarryRepresentative N d hN) (t : Fin (carryTailSize N d hN a)) :
    CarryLoop r (r+d) (tailVertex hr hN a t).val ↔
      a.val=portPartner N d hN a.val ∧ t.val+1=carryTailSize N d hN a := by
  have hh:=carryTail_loop_iff N d hN a t.isLt
  have ht:=t.isLt
  unfold SourceModel.CarryLoop
  rw [tailVertex_physical]
  omega

/-- Every tail spin is in 1..3, and only the fixed class's last spin has the
original carry-loop lower bound 2. -/
lemma physical_tail_domain (a : CarryRepresentative N d hN) (t : Fin (carryTailSize N d hN a))
    (v : State) :
    Domain r (r+d) 4 (tailVertex hr hN a t).val (v.val+1) ↔
      v.val+1 ≤ 3 ∧ ((a.val=portPartner N d hN a.val ∧ t.val+1=carryTailSize N d hN a) → 2 ≤ v.val+1) := by
  have hp:=tailVertex_gt_p hr hN a t
  have hf : ¬IsPivot r (r+d) (tailVertex hr hN a t).val := (tailVertex hr hN a t).property
  have hs : ¬StrongLoop r (r+d) (tailVertex hr hN a t).val := by unfold StrongLoop; omega
  have hu : upper r 4 (tailVertex hr hN a t).val=3 := by unfold upper; rw [if_neg (by omega)]
  rw [domain_iff_unary]
  simp only [Unary,hf,false_implies,true_and,IsFree,hf,not_false_eq_true,true_implies,hu,hs,
    tail_carry_loop_iff hr hN a t]
  omega

end Domains
section Product
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d)

lemma physical_assignment_tail (core : CoreAt hN c→State)
    (tail : (a : ModeFiber hr hN hbig c)→Fin (carryTailSize N d hN a.val)→State)
    (a : ModeFiber hr hN hbig c) (t : Fin (carryTailSize N d hN a.val)) :
    ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail))
      (componentVertexEquiv hr hd hN hbig c (.inr ⟨a,t⟩))=tail a t := by
  change (match (componentVertexEquiv hr hd hN hbig c).symm
      (componentVertexEquiv hr hd hN hbig c (.inr ⟨a,t⟩)) with
    | .inl k => core k
    | .inr ⟨a,t⟩ => tail a t)=tail a t
  rw [Equiv.symm_apply_apply]

/-- The actual physical unary product is exactly the vertex product of the
retained tail finite sum, after the proved assignment reindexing. -/
theorem tailUnaryProduct_eq_retained (core : CoreAt hN c→State)
    (tail : (a : ModeFiber hr hN hbig c)→Fin (carryTailSize N d hN a.val)→State)
    (a : ModeFiber hr hN hbig c) :
    tailUnaryProduct hr hd hN hbig c
      ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)) a=
      ∏ t : Fin (carryTailSize N d hN a.val),
        if (tail a t).val+1 ≤ 3 ∧
          ((a.val.val=portPartner N d hN a.val.val ∧ t.val+1=carryTailSize N d hN a.val) →
            2 ≤ (tail a t).val+1)
        then radius^((tail a t).val+1) else 0 := by
  unfold tailUnaryProduct
  apply Finset.prod_congr rfl
  intro t _
  rw [physical_assignment_tail]
  simp only [physical_tail_domain hr hN a.val t]

end Product
end SubmittedGenus.CapFourMass.CarryLocalization
