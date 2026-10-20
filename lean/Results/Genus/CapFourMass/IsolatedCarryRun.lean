import Results.Genus.CapFourMass.CarryRunLabels
import Results.Genus.CapFiveMass.ComponentCounts

/-! The only zero-edge carry mode is an actual isolated carry-loop component. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot

section Isolated
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)

include hbig in
lemma singleton_run_gt_p (a : CarryRepresentative N d hN) (hz : freeCarrySize N d hN a=1)
    (t : Fin (freeCarrySize N d hN a)) : r+d<physical (runVertex hr hN a t).val := by
  obtain ⟨ha,hf,htail⟩:=freeCarry_zero_edge N d hN hbig a hz
  have ht : t.val=0 := by have := t.isLt; omega
  rw [runVertex_physical]
  have he : freeCarryLabel N d hN a t.val=carryTailLabel N d hN a 0 := by
    simp only [freeCarryLabel,deletedPrefix,if_pos ha,ht,carryTailLabel]
  rw [he]
  have hh:=carryTailLabel_vertex N d hN a (show 0<carryTailSize N d hN a by omega)
  omega

include hd hbig in
lemma singleton_run_no_adj (a : CarryRepresentative N d hN) (hz : freeCarrySize N d hN a=1)
    (t : Fin (freeCarrySize N d hN a)) (v : FreeVertex (r+N) r (r+d)) :
    ¬(freeGraph (r+N) r (r+d)).Adj (runVertex hr hN a t) v := by
  intro hadj
  change (rawGraph (r+N) r (r+d)).Adj (runVertex hr hN a t).val v.val at hadj
  have hp:=canonicalParameters hr hd hN
  rcases StrongRuns.edge_strong_or_carry hadj with hs | hc
  · have hlo:=StrongRuns.strong_endpoint_lt_p hp hs
    have hhi:=singleton_run_gt_p hr hN hbig a hz t
    omega
  · have hv:=StrongRuns.carry_endpoint_gt_r hp (StrongRuns.carryStep_symm hc)
    obtain ⟨⟨b,s⟩,hrep⟩:= (runVertexEquiv (r:=r) hd hN).surjective ⟨v,hv⟩
    have he : runVertex hr hN b s=v := congrArg Subtype.val hrep
    have hcarry : CarryAdj (runVertex hr hN a t) (runVertex hr hN b s) := by
      rw [he]
      exact ⟨fun hh => hc.1.1 (congrArg Subtype.val hh),hc.2⟩
    have hab:=carry_adj_same_run hr hd hN a b t s hcarry
    subst b
    have hts : t=s := by apply Fin.ext; have := t.isLt; have := s.isLt; omega
    subst s
    exact hcarry.1 rfl

include hd in
/-- Every vertex of the actual component is the unique surviving run vertex. -/
lemma singleton_owner_vertices (a : CarryRepresentative N d hN) (hz : freeCarrySize N d hN a=1)
    (t : Fin (freeCarrySize N d hN a))
    (v : FreeVertex (r+N) r (r+d))
    (hv : (freeGraph (r+N) r (r+d)).connectedComponentMk v=owner hr hN hbig a) :
    v=runVertex hr hN a t := by
  by_contra he
  have hrch := SimpleGraph.ConnectedComponent.exact
    ((run_owner hr hd hN hbig a t).trans hv.symm)
  obtain ⟨w,hw⟩:=hrch.nonempty_neighborSet_left (Ne.symm he)
  exact singleton_run_no_adj hr hd hN hbig a hz t w hw

include hd in
/-- This corner really has zero edges in the independently constructed actual
component order; it is not an empty-tail convention. -/
theorem singleton_owner_edgeCount (a : CarryRepresentative N d hN) (hz : freeCarrySize N d hN a=1) :
    ActualComponent.edgeCount (owner hr hN hbig a)=0 := by
  let c:=owner hr hN hbig a
  let O:=freeComponentOrder (r+N) r (r+d) c
  let t : Fin (freeCarrySize N d hN a):=⟨0,by omega⟩
  have hall (j : Fin (O.edges+1)) : (O.label j).val=runVertex hr hN a t :=
    singleton_owner_vertices hr hd hN hbig a hz t (O.label j).val (O.label j).property
  have he : (0 : Fin (O.edges+1))=Fin.last O.edges :=
    O.label.injective (Subtype.ext ((hall 0).trans (hall (Fin.last O.edges)).symm))
  have hh:=congrArg Fin.val he
  exact hh.symm

include hd in
/-- An isolated carry loop uses precisely one free endpoint incidence. -/
theorem singleton_owner_free_incidence (a : CarryRepresentative N d hN)
    (hz : freeCarrySize N d hN a=1) :
    CapFiveMass.ActualComponent.endpointCount (owner hr hN hbig a) .free=1 := by
  let c:=owner hr hN hbig a
  have hn : CapFiveMass.ActualComponent.edgeCount c=0 := singleton_owner_edgeCount hr hd hN hbig a hz
  have hc : (freeComponentOrder (r+N) r (r+d) c).cycle=false := by
    cases hh : (freeComponentOrder (r+N) r (r+d) c).cycle
    · rfl
    · have hmin:=(freeComponentOrder (r+N) r (r+d) c).cycle_min hh
      change 3≤CapFiveMass.ActualComponent.edgeCount c at hmin
      omega
  let t : Fin (freeCarrySize N d hN a):=⟨0,by omega⟩
  have hv : ((freeComponentOrder (r+N) r (r+d) c).label 0).val=runVertex hr hN a t :=
    singleton_owner_vertices hr hd hN hbig a hz t _
      ((freeComponentOrder (r+N) r (r+d) c).label 0).property
  have hcarry : CarryLoop r (r+d) (runVertex hr hN a t).val :=
    (run_carry_loop_iff hr hN a t).mpr ⟨(freeCarry_zero_edge N d hN hbig a hz).2.1,by dsimp [t]; omega⟩
  have hstrong : ¬StrongLoop r (r+d) (runVertex hr hN a t).val := by
    have hhi:=singleton_run_gt_p hr hN hbig a hz t
    unfold StrongLoop
    omega
  have hl : CapFiveMass.ActualComponent.leftKind c=.carryLoop := by
    unfold CapFiveMass.ActualComponent.leftKind CapFiveMass.ActualComponent.loopKind
    have hv' : CapFiveMass.ActualComponent.vertex c 0=(runVertex hr hN a t).val := congrArg Subtype.val hv
    rw [hv',if_neg hstrong,if_pos hcarry]
  change CapFiveMass.ActualComponent.endpointCount c .free=1
  simp only [CapFiveMass.ActualComponent.endpointCount,hc,Bool.false_eq_true,if_false,
    hl,reduceCtorEq,CapFiveMass.ActualComponent.rightKind,hn,if_true,zero_add]

end Isolated
end SubmittedGenus.CapFourMass.CarryLocalization
