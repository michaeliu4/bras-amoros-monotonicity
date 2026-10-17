import Results.Genus.CapFourMass.CarryRunOwnership

/-! Source carry edges have canonical run labels, constant along every carry
segment and compatible with actual whole-graph component ownership. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot

section Labels
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)

/-- Recover a canonical carry label from any original high free vertex. -/
def runOf (v : FreeVertex (r+N) r (r+d)) (hv : r<physical v.val) :
    CarryRepresentative N d hN :=
  ((runVertexEquiv (r:=r) hd hN).symm ⟨v,hv⟩).1

lemma runOf_runVertex (a : CarryRepresentative N d hN) (t : Fin (freeCarrySize N d hN a)) :
    runOf hd hN (runVertex hr hN a t) (runVertex_high hr hN a t)=a := by
  change ((runVertexEquiv (r:=r) hd hN).symm (runVertexEquiv (r:=r) hd hN ⟨a,t⟩)).1=a
  rw [Equiv.symm_apply_apply]

include hr in
/-- Every actual carry edge has the same canonical label at both endpoints. -/
lemma carryAdj_runOf {u v : FreeVertex (r+N) r (r+d)}
    (hu : r<physical u.val) (hv : r<physical v.val) (h : CarryAdj u v) :
    runOf hd hN u hu=runOf hd hN v hv := by
  let a:=(runVertexEquiv (r:=r) hd hN).symm ⟨u,hu⟩
  let b:=(runVertexEquiv (r:=r) hd hN).symm ⟨v,hv⟩
  have ha : runVertex hr hN a.1 a.2=u :=
    congrArg Subtype.val ((runVertexEquiv (r:=r) hd hN).apply_symm_apply ⟨u,hu⟩)
  have hb : runVertex hr hN b.1 b.2=v :=
    congrArg Subtype.val ((runVertexEquiv (r:=r) hd hN).apply_symm_apply ⟨v,hv⟩)
  exact carry_adj_same_run hr hd hN a.1 b.1 a.2 b.2 (by rwa [ha,hb])

variable (hbig : 2*d<N)

/-- Canonical run-label recovery respects the source connected-component key. -/
lemma owner_runOf (v : FreeVertex (r+N) r (r+d)) (hv : r<physical v.val) :
    owner hr hN hbig (runOf hd hN v hv)=(freeGraph (r+N) r (r+d)).connectedComponentMk v := by
  let a:=(runVertexEquiv (r:=r) hd hN).symm ⟨v,hv⟩
  have ha : runVertex hr hN a.1 a.2=v :=
    congrArg Subtype.val ((runVertexEquiv (r:=r) hd hN).apply_symm_apply ⟨v,hv⟩)
  have hh:=run_owner hr hd hN hbig a.1 a.2
  rw [ha] at hh
  exact hh.symm

/-- Positive-edge canonical runs contain a genuine retained carry edge. -/
lemma run_edge_exists (a : CarryRepresentative N d hN)
    (hn : 1<freeCarrySize N d hN a) :
    ∃ u v : FreeVertex (r+N) r (r+d),CarryAdj u v ∧
      (∃ hu : r<physical u.val,runOf hd hN u hu=a) ∧
      (freeGraph (r+N) r (r+d)).connectedComponentMk u=owner hr hN hbig a := by
  let t : Fin (freeCarrySize N d hN a):=⟨0,by omega⟩
  let s : Fin (freeCarrySize N d hN a):=⟨1,hn⟩
  refine ⟨runVertex hr hN a t,runVertex hr hN a s,
    (run_carry_adj_iff hr hd hN a t s).mpr (Or.inl rfl),?_,run_owner hr hd hN hbig a t⟩
  exact ⟨runVertex_high hr hN a t,runOf_runVertex hr hd hN a t⟩

end Labels
end SubmittedGenus.CapFourMass.CarryLocalization
