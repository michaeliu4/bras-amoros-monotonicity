import Results.Genus.CapFourMass.IsolatedModeSource

/-! The complete actual zero-edge mode-source corner is the retained singleton
carry loop. A mode variable is never silently discarded in this case. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq

lemma zero_edge_no_adj {m r p : ℕ} (c : ActualComponent.Component m r p)
    (hz : ActualComponent.edgeCount c=0)
    (u v : FreeVertex m r p)
    (hu : (freeGraph m r p).connectedComponentMk u=c)
    (hadj : (freeGraph m r p).Adj u v) : False := by
  let O:=freeComponentOrder m r p c
  have he : O.edges=0 := hz
  have hv : (freeGraph m r p).connectedComponentMk v=c :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hu
  let i:=O.label.symm ⟨u,hu⟩
  let j:=O.label.symm ⟨v,hv⟩
  have hij : i=j := by
    apply Fin.ext
    have hi:=i.isLt
    have hj:=j.isLt
    omega
  have huv : u=v := by
    calc
      u=(O.label i).val := (congrArg Subtype.val (O.label.apply_symm_apply ⟨u,hu⟩)).symm
      _=(O.label j).val := congrArg (fun k => (O.label k).val) hij
      _=v := congrArg Subtype.val (O.label.apply_symm_apply ⟨v,hv⟩)
  exact hadj.ne huv

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)

include hd in
lemma mode_singleton_of_zero_edge (c : ActualComponent.Component (r+N) r (r+d))
    (hz : ActualComponent.edgeCount c=0) (a : ModeFiber hr hN hbig c) :
    freeCarrySize N d hN a.val=1 := by
  have hpos:=freeCarrySize_positive N d hN hbig a.val
  by_contra hne
  have hlarge : 1<freeCarrySize N d hN a.val := by omega
  obtain ⟨u,v,hcarry,_,hu⟩:=run_edge_exists hr hd hN hbig a.val hlarge
  exact zero_edge_no_adj c hz u v (hu.trans a.property) hcarry.adj

/-- The actual complete mode/core sum satisfies the global local budget even
when its physical component has zero edges and an inhabited mode fiber. -/
theorem zero_edge_component_absolute_le
    (c : ActualComponent.Component (r+N) r (r+d))
    (hz : ActualComponent.edgeCount c=0) (ha : Nonempty (ModeFiber hr hN hbig c)) :
    (∑ b : ModeFiber hr hN hbig c→Bool,
      |∑ x : CoreAt hN c→State,componentModeTerm hr hd hN hbig c x b|)≤
      ActualComponent.modeEndpointBudget c*ActualComponent.edgeCost c := by
  obtain ⟨a⟩:=ha
  have hsize:=mode_singleton_of_zero_edge hr hd hN hbig c hz a
  have he:=a.property
  rcases a with ⟨a,ha⟩
  dsimp at he hsize
  subst c
  exact singleton_component_absolute_le hr hd hN hbig a hsize

#print axioms zero_edge_component_absolute_le
end Source
end SubmittedGenus.CapFourMass.CarryLocalization
