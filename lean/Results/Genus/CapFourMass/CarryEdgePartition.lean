import Results.Genus.CapFourMass.ModeVertexPartition
import Results.Genus.CapFourMass.CarryRunOwnership
import Results.Genus.RawGraph.ComponentEdgeSlots

/-! Every physical carry edge occurs once in one owned canonical retained run. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq

section Partition
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d)

/-- The actual carry-only subgraph on the existing physical component. -/
def carryGraph : SimpleGraph c where
  Adj u v := CarryAdj u.val v.val
  symm := ⟨by
    intro u v h
    refine ⟨Ne.symm h.1,?_⟩
    simpa only [Nat.add_comm] using h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def ownedRunVertex (a : ModeFiber hr hN hbig c) (t : Fin (freeCarrySize N d hN a.val)) : c :=
  ⟨runVertex hr hN a.val t,(run_owner hr hd hN hbig a.val t).trans a.property⟩

def carryEdgeLeft (a : ModeFiber hr hN hbig c) (k : Fin (freeCarrySize N d hN a.val-1)) :
    Fin (freeCarrySize N d hN a.val) := ⟨k.val,by have:=k.isLt; omega⟩
def carryEdgeRight (a : ModeFiber hr hN hbig c) (k : Fin (freeCarrySize N d hN a.val-1)) :
    Fin (freeCarrySize N d hN a.val) := ⟨k.val+1,by have:=k.isLt; omega⟩

abbrev CarryEdgeSlot := Σ a : ModeFiber hr hN hbig c,Fin (freeCarrySize N d hN a.val-1)

def carrySlotEdge (v : CarryEdgeSlot hr hN hbig c) : (carryGraph c).edgeSet :=
  ⟨s(ownedRunVertex hr hd hN hbig c v.1 (carryEdgeLeft hr hN hbig c v.1 v.2),
      ownedRunVertex hr hd hN hbig c v.1 (carryEdgeRight hr hN hbig c v.1 v.2)),
    (run_carry_adj_iff hr hd hN v.1.val _ _).mpr (Or.inl rfl)⟩

lemma ownedRunVertex_injective : Function.Injective
    (fun v : Σ a : ModeFiber hr hN hbig c,Fin (freeCarrySize N d hN a.val) =>
      ownedRunVertex hr hd hN hbig c v.1 v.2) := by
  intro u v he
  have hh:=runVertex_injective hr hd hN (a₁:=⟨u.1.val,u.2⟩) (a₂:=⟨v.1.val,v.2⟩)
    (congrArg Subtype.val he)
  cases u with
  | mk a t =>
    cases v with
    | mk b s =>
      have hab : a=b:=Subtype.ext (congrArg Sigma.fst hh)
      subst b
      have hts : t=s:=by cases hh; rfl
      subst s
      rfl

lemma carrySlotEdge_injective : Function.Injective (carrySlotEdge hr hd hN hbig c) := by
  rintro ⟨a,k⟩ ⟨b,l⟩ he
  have hh:=congrArg Subtype.val he
  change s(ownedRunVertex hr hd hN hbig c a (carryEdgeLeft hr hN hbig c a k),
    ownedRunVertex hr hd hN hbig c a (carryEdgeRight hr hN hbig c a k))=
    s(ownedRunVertex hr hd hN hbig c b (carryEdgeLeft hr hN hbig c b l),
    ownedRunVertex hr hd hN hbig c b (carryEdgeRight hr hN hbig c b l)) at hh
  rcases Sym2.eq_iff.mp hh with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hi:=ownedRunVertex_injective hr hd hN hbig c
      (a₁:=⟨a,carryEdgeLeft hr hN hbig c a k⟩)
      (a₂:=⟨b,carryEdgeLeft hr hN hbig c b l⟩) h1
    have hab : a=b:=congrArg Sigma.fst hi
    subst b
    have hkl : k=l := by
      apply Fin.ext
      exact congrArg (fun v : Σ a : ModeFiber hr hN hbig c,Fin (freeCarrySize N d hN a.val) => v.2.val) hi
    subst l
    rfl
  · have hi:=ownedRunVertex_injective hr hd hN hbig c
      (a₁:=⟨a,carryEdgeLeft hr hN hbig c a k⟩)
      (a₂:=⟨b,carryEdgeRight hr hN hbig c b l⟩) h1
    have hj:=ownedRunVertex_injective hr hd hN hbig c
      (a₁:=⟨a,carryEdgeRight hr hN hbig c a k⟩)
      (a₂:=⟨b,carryEdgeLeft hr hN hbig c b l⟩) h2
    have hival:=congrArg (fun v : Σ a : ModeFiber hr hN hbig c,Fin (freeCarrySize N d hN a.val) => v.2.val) hi
    have hjval:=congrArg (fun v : Σ a : ModeFiber hr hN hbig c,Fin (freeCarrySize N d hN a.val) => v.2.val) hj
    change k.val=l.val+1 at hival
    change k.val+1=l.val at hjval
    omega

lemma carrySlotEdge_surjective : Function.Surjective (carrySlotEdge hr hd hN hbig c) := by
  rintro ⟨e,he⟩
  induction e using Sym2.ind with
  | h u v =>
    have hc : CarryAdj u.val v.val:=he
    have hp:=canonicalParameters hr hd hN
    have hstep : StrongRuns.CarryStep r (r+d) u.val.val v.val.val:=⟨hc.adj,hc.2⟩
    have hu:=StrongRuns.carry_endpoint_gt_r hp hstep
    have hv:=StrongRuns.carry_endpoint_gt_r hp (StrongRuns.carryStep_symm hstep)
    obtain ⟨⟨a,t⟩,htu⟩:=(runVertexEquiv (r:=r) hd hN).surjective ⟨u.val,hu⟩
    obtain ⟨⟨b,s⟩,hsv⟩:=(runVertexEquiv (r:=r) hd hN).surjective ⟨v.val,hv⟩
    have htu' : runVertex hr hN a t=u.val:=congrArg Subtype.val htu
    have hsv' : runVertex hr hN b s=v.val:=congrArg Subtype.val hsv
    have hcarry : CarryAdj (runVertex hr hN a t) (runVertex hr hN b s):=by rwa [htu',hsv']
    have hab:=carry_adj_same_run hr hd hN a b t s hcarry
    subst b
    have ha : owner hr hN hbig a=c := by rw [←run_owner hr hd hN hbig a t,htu']; exact u.property
    let aa : ModeFiber hr hN hbig c:=⟨a,ha⟩
    have htu'' : ownedRunVertex hr hd hN hbig c aa t=u:=Subtype.ext htu'
    have hsv'' : ownedRunVertex hr hd hN hbig c aa s=v:=Subtype.ext hsv'
    rcases (run_carry_adj_iff hr hd hN a t s).mp hcarry with hts | hst
    · let k : Fin (freeCarrySize N d hN a-1):=⟨t.val,by have:=s.isLt; omega⟩
      refine ⟨⟨aa,k⟩,Subtype.ext ?_⟩
      change s(ownedRunVertex hr hd hN hbig c aa (carryEdgeLeft hr hN hbig c aa k),
        ownedRunVertex hr hd hN hbig c aa (carryEdgeRight hr hN hbig c aa k))=s(u,v)
      have ht : carryEdgeLeft hr hN hbig c aa k=t:=Fin.ext rfl
      have hs : carryEdgeRight hr hN hbig c aa k=s:=Fin.ext hts
      rw [ht,hs,htu'',hsv'']
    · let k : Fin (freeCarrySize N d hN a-1):=⟨s.val,by have:=t.isLt; omega⟩
      refine ⟨⟨aa,k⟩,Subtype.ext ?_⟩
      change s(ownedRunVertex hr hd hN hbig c aa (carryEdgeLeft hr hN hbig c aa k),
        ownedRunVertex hr hd hN hbig c aa (carryEdgeRight hr hN hbig c aa k))=s(u,v)
      have hs : carryEdgeLeft hr hN hbig c aa k=s:=Fin.ext rfl
      have ht : carryEdgeRight hr hN hbig c aa k=t:=Fin.ext hst
      rw [ht,hs,htu'',hsv'']
      exact Sym2.eq_swap

/-- The carry edge set is exactly the disjoint union of the actual retained
canonical consecutive-edge slots. -/
def carryEdgeEquiv : CarryEdgeSlot hr hN hbig c≃(carryGraph c).edgeSet :=
  Equiv.ofBijective (carrySlotEdge hr hd hN hbig c)
    ⟨carrySlotEdge_injective hr hd hN hbig c,carrySlotEdge_surjective hr hd hN hbig c⟩

end Partition
end SubmittedGenus.CapFourMass.CarryLocalization
