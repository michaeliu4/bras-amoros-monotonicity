import Results.Genus.CapFourMass.OrderedModeMatrices
import Results.Genus.CapFourMass.ExecutableRunCheck
import Results.Genus.CapFourMass.SourceModeSlots

/-! Every genuine complete-source mode variable occurs in the supplied signed
word unless its component is the isolated zero-edge corner. Checked run
programs therefore preserve all shared choices and yield pointed injections. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization CarryLocalization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d) (O : OrderedComponent c.toSimpleGraph)

lemma ordered_edgeCount : O.edges=edgeCount c := by
  have h₁ : O.edges+1=Fintype.card c := by simpa using Fintype.card_congr O.label
  have h₂ : edgeCount c+1=Fintype.card c := by
    simpa only [edgeCount,Fintype.card_fin] using Fintype.card_congr (freeComponentOrder (r+N) r (r+d) c).label
  omega

def orderedTags : List (TaggedEdge (Option (CarryRepresentative N d hN))) :=
  if O.cycle=true then cycleTags hd hN (orderedVertex c O) else pathTags hd hN (orderedVertex c O)

lemma orderedTags_edgeWord : orderedTags hd hN c O=O.edgeWord
    (fun u v => edgeTag hd hN u.val.val v.val.val) := by
  unfold orderedTags OrderedComponent.edgeWord cycleTags pathTags orderedVertex
  split_ifs <;> simp only [List.append_nil]

include hr hd hbig in
lemma ordered_mode_label_coverage (hn : O.edges≠0) (a : ModeFiber hr hN hbig c) :
    TaggedEdge.carry (some a.val)∈orderedTags hd hN c O := by
  have ha : 1<freeCarrySize N d hN a.val := by
    have hp:=freeCarrySize_positive N d hN hbig a.val
    by_contra hh
    have he : freeCarrySize N d hN a.val=1:=by omega
    have hz:=singleton_owner_edgeCount hr hd hN hbig a.val he
    rw [a.property] at hz
    exact hn ((ordered_edgeCount c O).trans hz)
  obtain ⟨u,v,hc,⟨hu,he⟩,howner⟩:=run_edge_exists hr hd hN hbig a.val ha
  have huo : (freeGraph (r+N) r (r+d)).connectedComponentMk u=c := howner.trans a.property
  have hvo : (freeGraph (r+N) r (r+d)).connectedComponentMk v=c :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hc.adj).symm.trans huo
  rw [orderedTags_edgeWord]
  have hh:=O.edge_mem_word (fun u v => edgeTag hd hN u.val.val v.val.val)
    (fun u v h => by
      rw [edgeTag_eq_source hr hd hN u.val v.val,edgeTag_eq_source hr hd hN v.val u.val]
      exact taggedEdge_symm hr hd hN h) ⟨u,huo⟩ ⟨v,hvo⟩ hc.adj
  rw [edgeTag_eq_source hr hd hN u v,
    taggedEdge_carry hr hd hN (show StrongRuns.CarryStep r (r+d) u.val v.val from ⟨hc.adj,hc.2⟩)] at hh
  simpa only [he] using hh

include hr hd hbig in
lemma ordered_path_slot_coverage (hc : O.cycle=false) (hn : O.edges≠0)
    (pre post : Option StrongRun) (tag : Option (CarryRepresentative N d hN))
    (n : ℕ) (hn' : 1≤n) (bs : List (TaggedBlock (Option (CarryRepresentative N d hN))))
    (hcheck : pathCodeCheck (pathTags hd hN (orderedVertex c O))
      (.carried pre tag n hn' bs post)=true)
    (a : ModeFiber hr hN hbig c) : ∃i,taggedModeLabels bs tag i=some a.val := by
  obtain ⟨hchain,he⟩:= (pathCodeCheck_eq_true _ _).mp hcheck
  have hm:=ordered_mode_label_coverage hr hd hN hbig c O hn a
  simp only [orderedTags,hc,Bool.false_eq_true,if_false] at hm
  obtain ⟨k,hk,hmem⟩:=carry_mem_taggedAtoms _ hchain _ hm
  rw [he] at hmem
  apply taggedModeLabels_mem
  simp only [TaggedPathCode.atoms,List.mem_append,List.mem_singleton] at hmem
  rcases hmem with ((hpre | htag) | hbs) | hpost
  · cases pre <;> simp at hpre
  · left
    injection htag with hlabel
    exact hlabel.symm
  · exact Or.inr (tagged_pair_carry_mem _ k hk bs hbs)
  · cases post <;> simp at hpost

include hr hd hbig in
lemma ordered_cycle_slot_coverage (hc : O.cycle=true) (rotation : ℕ)
    (b : TaggedBlock (Option (CarryRepresentative N d hN)))
    (bs : List (TaggedBlock (Option (CarryRepresentative N d hN))))
    (hcheck : cycleCodeCheck (cycleTags hd hN (orderedVertex c O)) rotation (b::bs)=true)
    (a : ModeFiber hr hN hbig c) : ∃i,taggedModeLabels bs b.label i=some a.val := by
  obtain ⟨_,hchain,he⟩:= (cycleCodeCheck_eq_true _ _ _).mp hcheck
  have hn : O.edges≠0:=by have := O.cycle_min hc; omega
  have hm:=ordered_mode_label_coverage hr hd hN hbig c O hn a
  simp only [orderedTags,hc,if_true] at hm
  have hrot : TaggedEdge.carry (some a.val)∈(cycleTags hd hN (orderedVertex c O)).rotate rotation :=
    List.mem_rotate.mpr hm
  obtain ⟨k,hk,hmem⟩:=carry_mem_taggedAtoms _ hchain _ hrot
  rw [he] at hmem
  obtain ⟨q,hq,hlabel⟩:=tagged_pair_carry_mem _ k hk (b::bs) hmem
  apply taggedModeLabels_mem
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact Or.inl hlabel
  · exact Or.inr ⟨q,hq,hlabel⟩

include hr hd hbig in
lemma ordered_pure_fiber_empty (hc : O.cycle=false) (hn : O.edges≠0)
    (s : Option StrongRun)
    (hcheck : pathCodeCheck (pathTags hd hN (orderedVertex c O)) (.pure s)=true) :
    IsEmpty (ModeFiber hr hN hbig c) := by
  obtain ⟨hchain,he⟩:= (pathCodeCheck_eq_true _ _).mp hcheck
  refine ⟨fun a => ?_⟩
  have hm:=ordered_mode_label_coverage hr hd hN hbig c O hn a
  simp only [orderedTags,hc,Bool.false_eq_true,if_false] at hm
  obtain ⟨k,hk,hmem⟩:=carry_mem_taggedAtoms _ hchain _ hm
  rw [he] at hmem
  cases s <;> simp [TaggedPathCode.atoms] at hmem

include hr hd hbig in
lemma ordered_zero_low_fiber_empty (hz : O.edges=0)
    (hlow : physical (orderedVertex c O 0)≤r) : IsEmpty (ModeFiber hr hN hbig c) := by
  refine ⟨fun a => ?_⟩
  let t : Fin (freeCarrySize N d hN a.val):=⟨0,freeCarrySize_positive N d hN hbig a.val⟩
  let v : c:=⟨runVertex hr hN a.val t,(run_owner hr hd hN hbig a.val t).trans a.property⟩
  let i:=O.label.symm v
  have hi : i=0 := Fin.ext (by have := i.isLt; omega)
  have hv : O.label 0=v := by rw [←hi]; exact O.label.apply_symm_apply v
  have hh:=runVertex_high hr hN a.val t
  have he : orderedVertex c O 0=(runVertex hr hN a.val t).val :=
    congrArg (fun w : c => w.val.val) hv
  rw [he] at hlow
  omega

include hr hd hbig in
lemma ordered_high_mode_owner (hh : r<physical (orderedVertex c O 0)) :
    owner hr hN hbig (carryLabel hd hN (orderedVertex c O 0))=c := by
  change owner hr hN hbig (carryLabel hd hN (O.label 0).val.val)=c
  rw [carryLabel_eq_runOf hr hd hN (O.label 0).val hh,
    owner_runOf hr hd hN hbig (O.label 0).val hh]
  exact (O.label 0).property

end Source
end SubmittedGenus.CapFourMass.ExecutableModes
