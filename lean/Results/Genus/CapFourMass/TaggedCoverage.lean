import Results.Genus.RawGraph.ComponentEdgeWord
import Results.Genus.CapFourMass.TaggedActualCompiler
import Results.Genus.CapFourMass.IsolatedCarryRun

/-! Actual signed carry tags cover every non-isolated canonical mode variable. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology FixedPivot CarryLocalization
attribute [local instance] Classical.propDecidable Classical.decEq

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)

include hr in
lemma taggedEdge_symm {u v : FreeVertex (r+N) r (r+d)}
    (hadj : (freeGraph (r+N) r (r+d)).Adj u v) :
    taggedEdge hd hN u v=taggedEdge hd hN v u := by
  change (rawGraph (r+N) r (r+d)).Adj u.val v.val at hadj
  have hp:=canonicalParameters hr hd hN
  by_cases hc : kind r (r+d) u.val v.val=.carry
  · have hs:=(kind_carry_iff hp hadj).mp hc
    have ht:=StrongRuns.carryStep_symm hs
    rw [taggedEdge_carry hr hd hN hs,taggedEdge_carry hr hd hN ht]
    congr 2
    exact carryAdj_runOf hr hd hN (StrongRuns.carry_endpoint_gt_r hp hs)
      (StrongRuns.carry_endpoint_gt_r hp ht)
      ⟨fun he => hadj.1 (congrArg Subtype.val he),hs.2⟩
  · have hk : kind r (r+d) u.val v.val=kind r (r+d) v.val u.val := by
      unfold kind
      simp only [Nat.add_comm,and_comm]
    unfold taggedEdge
    rw [hk]
    have hc' : kind r (r+d) v.val u.val≠.carry:=fun hh => hc (hk.trans hh)
    cases he : kind r (r+d) v.val u.val <;> simp_all

def taggedSourceWord (c : Component (r+N) r (r+d)) :
    List (TaggedEdge (Option (CarryRepresentative N d hN))) :=
  if (freeComponentOrder (r+N) r (r+d) c).cycle=true then taggedClosedWord hd hN c
  else taggedPathWord hd hN c

lemma taggedSourceWord_edgeWord (c : Component (r+N) r (r+d)) :
    taggedSourceWord hd hN c=(freeComponentOrder (r+N) r (r+d) c).edgeWord
      (fun u v => taggedEdge hd hN u.val v.val) := by
  unfold taggedSourceWord OrderedComponent.edgeWord taggedClosedWord taggedPathWord sourceFreeVertex
  split_ifs <;> simp only [List.append_nil] <;> rfl

include hr in
lemma tagged_edge_mem_source (c : Component (r+N) r (r+d))
    (u v : FreeVertex (r+N) r (r+d))
    (hu : (freeGraph (r+N) r (r+d)).connectedComponentMk u=c)
    (hv : (freeGraph (r+N) r (r+d)).connectedComponentMk v=c)
    (hadj : (freeGraph (r+N) r (r+d)).Adj u v) :
    taggedEdge hd hN u v∈taggedSourceWord hd hN c := by
  rw [taggedSourceWord_edgeWord]
  exact (freeComponentOrder (r+N) r (r+d) c).edge_mem_word
    (fun u v => taggedEdge hd hN u.val v.val)
    (fun u v h => taggedEdge_symm hr hd hN h) ⟨u,hu⟩ ⟨v,hv⟩ hadj

variable (hbig : 2*d<N)

/-- Every canonical carry run with a retained edge occurs in the actual
source word of its actual connected component. -/
theorem mode_label_mem_source (a : CarryRepresentative N d hN)
    (hn : 1<freeCarrySize N d hN a) :
    TaggedEdge.carry (some a)∈taggedSourceWord hd hN (owner hr hN hbig a) := by
  obtain ⟨u,v,hc,⟨hu,he⟩,howner⟩:=run_edge_exists hr hd hN hbig a hn
  have hv : (freeGraph (r+N) r (r+d)).connectedComponentMk v=owner hr hN hbig a :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hc.adj).symm.trans howner
  have hs : StrongRuns.CarryStep r (r+d) u.val v.val:=⟨hc.adj,hc.2⟩
  have hh:=tagged_edge_mem_source hr hd hN _ u v howner hv hc.adj
  rw [taggedEdge_carry hr hd hN hs] at hh
  simpa only [he] using hh

/-- Outside the isolated zero-edge corner, no complete mode variable is lost
by passing from canonical source tails to actual edge-word labels. -/
theorem component_mode_label_coverage (c : Component (r+N) r (r+d))
    (hc : edgeCount c≠0) (a : ModeFiber hr hN hbig c) :
    TaggedEdge.carry (some a.val)∈taggedSourceWord hd hN c := by
  have hn : 1<freeCarrySize N d hN a.val := by
    have hp:=freeCarrySize_positive N d hN hbig a.val
    by_contra hh
    have he : freeCarrySize N d hN a.val=1:=by omega
    have hz:=singleton_owner_edgeCount hr hd hN hbig a.val he
    rw [a.property] at hz
    exact hc hz
  have hh:=mode_label_mem_source hr hd hN hbig a.val hn
  rwa [a.property] at hh

end Source
end SubmittedGenus.CapFourMass.ActualComponent
