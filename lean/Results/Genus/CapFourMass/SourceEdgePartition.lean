import Results.Genus.CapFourMass.CoreEdgePartition
import Results.Genus.CapFourMass.CarryEdgePartition

/-! Exact source edge partition into free-core ordinary edges and the retained
canonical carry-run edges. Arbitrary signed products use each physical edge once. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq

section Partition
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d)

lemma strongGraph_le_actual : strongGraph c≤c.toSimpleGraph := fun _ _ h => h.1
lemma carryGraph_le_actual : carryGraph c≤c.toSimpleGraph := fun _ _ h => h.adj

include hr hd hN in
lemma strong_carry_edge_disjoint (e : Sym2 c) :
    e∈(strongGraph c).edgeSet → e∈(carryGraph c).edgeSet → False := by
  induction e using Sym2.ind with
  | h u v =>
    intro hs hc
    have hs' : StrongRuns.StrongStep r (r+d) u.val.val v.val.val:=hs
    have hc' : CarryAdj u.val v.val:=hc
    exact StrongRuns.strong_carry_disjoint (canonicalParameters hr hd hN) _ _
      ⟨hs',⟨hc'.adj,hc'.2⟩⟩

def edgeSumMap : (strongGraph c).edgeSet ⊕ (carryGraph c).edgeSet→c.toSimpleGraph.edgeSet
  | .inl e => ⟨e.val,SimpleGraph.edgeSet_mono (strongGraph_le_actual c) e.property⟩
  | .inr e => ⟨e.val,SimpleGraph.edgeSet_mono (carryGraph_le_actual c) e.property⟩

include hr hd hN in
lemma edgeSumMap_injective : Function.Injective (edgeSumMap c) := by
  intro u v he
  have hh:=congrArg Subtype.val he
  cases u with
  | inl u =>
    cases v with
    | inl v => exact congrArg Sum.inl (Subtype.ext hh)
    | inr v =>
      exact (strong_carry_edge_disjoint hr hd hN c u.val u.property
        (by change u.val=v.val at hh; rw [hh]; exact v.property)).elim
  | inr u =>
    cases v with
    | inl v =>
      exact (strong_carry_edge_disjoint hr hd hN c v.val v.property
        (by change u.val=v.val at hh; rw [←hh]; exact u.property)).elim
    | inr v => exact congrArg Sum.inr (Subtype.ext hh)

lemma edgeSumMap_surjective : Function.Surjective (edgeSumMap c) := by
  rintro ⟨e,he⟩
  induction e using Sym2.ind with
  | h u v =>
    have hadj : (rawGraph (r+N) r (r+d)).Adj u.val.val v.val.val:=he
    rcases StrongRuns.edge_strong_or_carry hadj with hs | hc
    · exact ⟨.inl ⟨s(u,v),hs⟩,rfl⟩
    · have hc' : CarryAdj u.val v.val:=⟨fun h => hc.1.1 (congrArg Subtype.val h),hc.2⟩
      exact ⟨.inr ⟨s(u,v),hc'⟩,rfl⟩

/-- Every actual edge is ordinary or carried, never both. -/
def edgeSumEquiv : (strongGraph c).edgeSet ⊕ (carryGraph c).edgeSet≃c.toSimpleGraph.edgeSet :=
  Equiv.ofBijective (edgeSumMap c) ⟨edgeSumMap_injective hr hd hN c,edgeSumMap_surjective c⟩

/-- The physical edge set is in bijection with upper core edges and owned
canonical carry slots, without any assumed component decomposition. -/
def sourceEdgeEquiv :
    ({ij // ij∈coreEdgeSet hN c} ⊕ CarryEdgeSlot hr hN hbig c)≃c.toSimpleGraph.edgeSet :=
  (Equiv.sumCongr (coreEdgeEquiv hr hd hN c) (carryEdgeEquiv hr hd hN hbig c)).trans
    (edgeSumEquiv hr hd hN c)

lemma source_edge_product {R : Type*} [CommMonoid R] (w : Sym2 c→R) :
    (∏ e : c.toSimpleGraph.edgeSet,w e.val)=
      (∏ ij : {ij // ij∈coreEdgeSet hN c},w (coreSlotEdge hN c ij).val)*
        ∏ a : ModeFiber hr hN hbig c,∏ k : Fin (freeCarrySize N d hN a.val-1),
          w (carrySlotEdge hr hd hN hbig c ⟨a,k⟩).val := by
  rw [←(sourceEdgeEquiv hr hd hN hbig c).prod_comp (fun e => w e.val)]
  rw [Fintype.prod_sum_type]
  change (∏ ij : {ij // ij∈coreEdgeSet hN c},w (coreSlotEdge hN c ij).val)*
      (∏ v : CarryEdgeSlot hr hN hbig c,w (carrySlotEdge hr hd hN hbig c v).val)=_
  rw [Fintype.prod_sigma]

end Partition
end SubmittedGenus.CapFourMass.CarryLocalization
