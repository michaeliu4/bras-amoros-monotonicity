import Results.Genus.CapFourMass.CarryRunLabels
import Results.Genus.CapFourMass.TaggedRuns

/-! Actual source edge words retain their canonical complete-mode labels. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot CarryLocalization

section TaggedSource
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)

def taggedEdge (u v : FreeVertex (r+N) r (r+d)) : TaggedEdge (Option (CarryRepresentative N d hN)) :=
  match kind r (r+d) u.val v.val with
  | .strong => .strong
  | .restricted => .restricted
  | .carry => .carry (if hu : r<physical u.val then some (runOf hd hN u hu) else none)

@[simp] lemma taggedEdge_kind (u v : FreeVertex (r+N) r (r+d)) :
    (taggedEdge hd hN u v).kind=kind r (r+d) u.val v.val := by
  unfold taggedEdge
  split <;> simp_all [TaggedEdge.kind]

lemma taggedEdge_carry {u v : FreeVertex (r+N) r (r+d)}
    (hs : StrongRuns.CarryStep r (r+d) u.val v.val) :
    taggedEdge hd hN u v=.carry (some (runOf hd hN u
      (StrongRuns.carry_endpoint_gt_r (canonicalParameters hr hd hN) hs))) := by
  have hk:=(kind_carry_iff (canonicalParameters hr hd hN) hs.1).mpr hs
  simp only [taggedEdge,hk,dif_pos (StrongRuns.carry_endpoint_gt_r (canonicalParameters hr hd hN) hs)]

include hr in
lemma tagged_neighbor_compatible {u v w : FreeVertex (r+N) r (r+d)}
    (huv : (freeGraph (r+N) r (r+d)).Adj u v)
    (hvw : (freeGraph (r+N) r (r+d)).Adj v w) (hne : u≠w) :
    TaggedCompatible (taggedEdge hd hN u v) (taggedEdge hd hN v w) := by
  change (rawGraph (r+N) r (r+d)).Adj u.val v.val at huv
  change (rawGraph (r+N) r (r+d)).Adj v.val w.val at hvw
  have hp:=canonicalParameters hr hd hN
  have hne' : u.val≠w.val := fun he => hne (Subtype.ext he)
  refine ⟨?_,?_⟩
  · simpa only [taggedEdge_kind] using neighbor_compatible hp huv hvw hne'
  · intro he
    simp only [taggedEdge_kind] at he
    by_cases hc : kind r (r+d) u.val v.val=.carry
    · have hc' : kind r (r+d) v.val w.val=.carry := he.symm.trans hc
      have hcu:=(kind_carry_iff hp huv).mp hc
      have hcv:=(kind_carry_iff hp hvw).mp hc'
      rw [taggedEdge_carry hr hd hN hcu,taggedEdge_carry hr hd hN hcv]
      congr 2
      exact carryAdj_runOf hr hd hN (StrongRuns.carry_endpoint_gt_r hp hcu)
        (StrongRuns.carry_endpoint_gt_r hp hcv) ⟨fun hh => hcu.1.1 (congrArg Subtype.val hh),hcu.2⟩
    · unfold taggedEdge
      rw [he]
      have hc' : kind r (r+d) v.val w.val≠.carry := fun hh => hc (he.trans hh)
      cases hk : kind r (r+d) v.val w.val <;> simp_all

def sourceFreeVertex (c : Component (r+N) r (r+d)) (j : Fin (edgeCount c+1)) :
    FreeVertex (r+N) r (r+d) := ((freeComponentOrder (r+N) r (r+d) c).label j).val

@[simp] lemma sourceFreeVertex_val (c : Component (r+N) r (r+d)) (j : Fin (edgeCount c+1)) :
    (sourceFreeVertex c j).val=vertex c j := rfl

def taggedPathWord (c : Component (r+N) r (r+d)) : List (TaggedEdge (Option (CarryRepresentative N d hN))) :=
  List.ofFn (fun j : Fin (edgeCount c) => taggedEdge hd hN
    (sourceFreeVertex c j.castSucc) (sourceFreeVertex c j.succ))

def taggedClosedWord (c : Component (r+N) r (r+d)) : List (TaggedEdge (Option (CarryRepresentative N d hN))) :=
  taggedPathWord hd hN c ++ [taggedEdge hd hN (sourceFreeVertex c (Fin.last _)) (sourceFreeVertex c 0)]

@[simp] lemma taggedPathWord_kinds (c : Component (r+N) r (r+d)) :
    (taggedPathWord hd hN c).map TaggedEdge.kind=pathWord c := by
  simp only [taggedPathWord,List.map_ofFn,Function.comp_def,taggedEdge_kind,sourceFreeVertex_val]
  rfl

@[simp] lemma taggedClosedWord_kinds (c : Component (r+N) r (r+d)) :
    (taggedClosedWord hd hN c).map TaggedEdge.kind=closedWord c := by
  simp only [taggedClosedWord,List.map_append,List.map_cons,List.map_nil,
    taggedPathWord_kinds,taggedEdge_kind,sourceFreeVertex_val,closedWord]

include hr in
/-- Adjacent actual carry edges carry the same canonical mode variable. -/
lemma taggedPathWord_compatible (c : Component (r+N) r (r+d)) :
    (taggedPathWord hd hN c).IsChain TaggedCompatible := by
  rw [List.isChain_iff_getElem]
  intro j hj
  have hj' : j+1<edgeCount c := by simpa only [taggedPathWord,List.length_ofFn] using hj
  have hj0 : j<edgeCount c := by omega
  simp only [taggedPathWord,List.getElem_ofFn]
  apply tagged_neighbor_compatible hr hd hN
    (consecutive_adj c ⟨j,hj0⟩) (consecutive_adj c ⟨j+1,hj'⟩)
  intro he
  have hval:=congrArg Subtype.val he
  have hh:=congrArg Fin.val (vertex_injective c hval)
  simp only [Fin.val_castSucc,Fin.val_succ] at hh
  omega

include hr in
lemma taggedClosedWord_compatible (c : Component (r+N) r (r+d))
    (hc : (freeComponentOrder (r+N) r (r+d) c).cycle=true) :
    (taggedClosedWord hd hN c).IsChain TaggedCompatible := by
  have hn : 3≤edgeCount c := (freeComponentOrder (r+N) r (r+d) c).cycle_min hc
  have hnon : taggedPathWord hd hN c≠[] := by
    intro he
    have hh:=congrArg List.length he
    simp only [taggedPathWord,List.length_ofFn,List.length_nil] at hh
    omega
  unfold taggedClosedWord
  apply List.IsChain.append (taggedPathWord_compatible hr hd hN c) (by simp)
  intro a ha b hb
  rw [List.getLast?_eq_some_getLast hnon] at ha
  have ha' : a=(taggedPathWord hd hN c).getLast hnon := (Option.mem_some_iff.mp ha).symm
  have hb' : b=taggedEdge hd hN (sourceFreeVertex c (Fin.last _)) (sourceFreeVertex c 0) := by
    simpa using (Option.mem_some_iff.mp hb).symm
  subst a; subst b
  simp only [taggedPathWord,List.getLast_ofFn]
  have hlast : edgeCount c-1<edgeCount c := by omega
  have hcast : Fin.succ (⟨edgeCount c-1,hlast⟩ : Fin (edgeCount c))=Fin.last (edgeCount c) := by
    apply Fin.ext
    simp only [Fin.val_succ,Fin.val_last]
    omega
  have he:=consecutive_adj c ⟨edgeCount c-1,hlast⟩
  rw [hcast] at he ⊢
  apply tagged_neighbor_compatible hr hd hN he (closing_adj c hc)
  intro hv
  have hh:=congrArg Fin.val (vertex_injective c (congrArg Subtype.val hv))
  simp only [Fin.val_castSucc,Fin.val_zero] at hh
  omega

include hr in
/-- Rotating an actual cycle keeps the canonical carry labels continuous. -/
lemma taggedClosedWord_cyclic_compatible (c : Component (r+N) r (r+d))
    (hc : (freeComponentOrder (r+N) r (r+d) c).cycle=true) :
    CyclicChain TaggedCompatible (taggedClosedWord hd hN c) := by
  refine ⟨taggedClosedWord_compatible hr hd hN c hc,?_⟩
  have hn : 3≤edgeCount c := (freeComponentOrder (r+N) r (r+d) c).cycle_min hc
  have hnon : taggedPathWord hd hN c≠[] := by
    intro he
    have hh:=congrArg List.length he
    simp only [taggedPathWord,List.length_ofFn,List.length_nil] at hh
    omega
  intro x hx y hy
  have hx' : x=taggedEdge hd hN (sourceFreeVertex c (Fin.last _)) (sourceFreeVertex c 0) := by
    simp only [taggedClosedWord,List.getLast?_append,List.getLast?_cons,List.getLast?_nil] at hx
    exact (Option.mem_some_iff.mp hx).symm
  have hy' : y=taggedEdge hd hN (sourceFreeVertex c (Fin.castSucc ⟨0,by omega⟩))
      (sourceFreeVertex c (Fin.succ ⟨0,by omega⟩)) := by
    rw [taggedClosedWord,List.head?_append_of_ne_nil _ hnon,List.head?_eq_some_head hnon] at hy
    have he:=(Option.mem_some_iff.mp hy).symm
    simpa only [taggedPathWord,List.head_ofFn] using he
  subst x; subst y
  apply tagged_neighbor_compatible hr hd hN (closing_adj c hc) (consecutive_adj c ⟨0,by omega⟩)
  intro he
  have hh:=congrArg Fin.val (vertex_injective c (congrArg Subtype.val he))
  simp only [Fin.val_last,Fin.val_succ] at hh
  omega

end TaggedSource
end SubmittedGenus.CapFourMass.ActualComponent
