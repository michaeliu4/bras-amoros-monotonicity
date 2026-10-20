import Results.Genus.CapFourMass.TaggedSourceWords

/-! Computable canonical carry labels and tagged physical edge words. Their
semantic equality with the original source labels avoids evaluating any
choice-based connected-component ordering or inverse bijection. -/
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.Topology FixedPivot CarryLocalization ActualComponent

section Labels
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)

/-- The actual source label is the larger port in the reflected residue pair. -/
def carryLabel (i : Fin (r+N-1)) : CarryRepresentative N d hN :=
  carryRepresentative N d hN (carryVertexPort d hd (physical i-r))

lemma carryLabel_runVertex (a : CarryRepresentative N d hN)
    (t : Fin (freeCarrySize N d hN a)) :
    carryLabel hd hN (runVertex hr hN a t).val=a := by
  unfold carryLabel
  rw [runVertex_physical,Nat.add_sub_cancel_left]
  exact carryComponentLabel_representative N d hd hN a (t.val+deletedPrefix N d hN a)

include hr in
/-- The executable residue formula equals the established complete-source tag. -/
theorem carryLabel_eq_runOf (v : FreeVertex (r+N) r (r+d)) (hv : r<physical v.val) :
    carryLabel hd hN v.val=runOf hd hN v hv := by
  let a:=(runVertexEquiv (r:=r) hd hN).symm ⟨v,hv⟩
  have he : runVertex hr hN a.1 a.2=v :=
    congrArg Subtype.val ((runVertexEquiv (r:=r) hd hN).apply_symm_apply ⟨v,hv⟩)
  have ht:=carryLabel_runVertex hr hd hN a.1 a.2
  rw [he] at ht
  exact ht

/-- Source masks still distinguish D/E; only the carry-label computation changes. -/
def edgeTag (i j : Fin (r+N-1)) : TaggedEdge (Option (CarryRepresentative N d hN)) :=
  match kind r (r+d) i j with
  | .strong => .strong
  | .restricted => .restricted
  | .carry => .carry (if r<physical i then some (carryLabel hd hN i) else none)

include hr in
lemma edgeTag_eq_source (u v : FreeVertex (r+N) r (r+d)) :
    edgeTag hd hN u.val v.val=taggedEdge hd hN u v := by
  unfold edgeTag taggedEdge
  cases hk : kind r (r+d) u.val v.val
  · rfl
  · rfl
  · by_cases hu : r<physical u.val
    · simp only [if_pos hu,dif_pos hu,carryLabel_eq_runOf hr hd hN u hu]
    · simp only [if_neg hu,dif_neg hu]

@[simp] lemma edgeTag_kind (i j : Fin (r+N-1)) :
    (edgeTag hd hN i j).kind=kind r (r+d) i j := by
  unfold edgeTag
  cases kind r (r+d) i j <;> rfl

/-- This list is finite executable data on the supplied physical order. -/
def pathTags {n : ℕ} (v : Fin (n+1)→Fin (r+N-1)) :
    List (TaggedEdge (Option (CarryRepresentative N d hN))) :=
  List.ofFn (fun k : Fin n => edgeTag hd hN (v k.castSucc) (v k.succ))

def cycleTags {n : ℕ} (v : Fin (n+1)→Fin (r+N-1)) :
    List (TaggedEdge (Option (CarryRepresentative N d hN))) :=
  pathTags hd hN v++[edgeTag hd hN (v (Fin.last n)) (v 0)]

@[simp] lemma pathTags_length {n : ℕ} (v : Fin (n+1)→Fin (r+N-1)) :
    (pathTags hd hN v).length=n := by simp [pathTags]
@[simp] lemma cycleTags_length {n : ℕ} (v : Fin (n+1)→Fin (r+N-1)) :
    (cycleTags hd hN v).length=n+1 := by simp [cycleTags]

include hr in
lemma pathTags_eq_source (c : Component (r+N) r (r+d)) :
    pathTags hd hN (vertex c)=taggedPathWord hd hN c := by
  unfold pathTags taggedPathWord
  congr 1
  funext k
  exact edgeTag_eq_source hr hd hN (sourceFreeVertex c k.castSucc) (sourceFreeVertex c k.succ)

include hr in
lemma cycleTags_eq_source (c : Component (r+N) r (r+d)) :
    cycleTags hd hN (vertex c)=taggedClosedWord hd hN c := by
  rw [cycleTags,pathTags_eq_source hr hd hN]
  unfold taggedClosedWord
  congr 2
  exact edgeTag_eq_source hr hd hN (sourceFreeVertex c (Fin.last _)) (sourceFreeVertex c 0)

end Labels
end SubmittedGenus.CapFourMass.ExecutableModes
