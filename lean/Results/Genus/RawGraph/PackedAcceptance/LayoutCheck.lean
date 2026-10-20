import Results.Genus.RawGraph.Layout

namespace SubmittedGenus.RawGraph.PackedAcceptance
open LayoutCompiler SourceModel

/-- Constant-time adjacency test using the inverse physical labels. -/
def FastAdjacent {m : ℕ} (L : Layout m) (u v : Fin (m-1)) : Prop :=
  let x := L.label.symm u
  let y := L.label.symm v
  x.1=y.1 ∧ (x.2.val+1=y.2.val ∨ y.2.val+1=x.2.val ∨
    (L.cycle x.1=true ∧
      ((x.2.val=L.edges x.1 ∧ y.2.val=0) ∨ (y.2.val=L.edges x.1 ∧ x.2.val=0))))

instance {m : ℕ} (L : Layout m) (u v : Fin (m-1)) : Decidable (FastAdjacent L u v) := by
  unfold FastAdjacent
  infer_instance

lemma adjacent_of_positions {m : ℕ} (L : Layout m) (c : Fin L.count)
    (i j : Fin (L.edges c+1))
    (h : i.val+1=j.val ∨ j.val+1=i.val ∨
      (L.cycle c=true ∧ ((i.val=L.edges c ∧ j.val=0) ∨ (j.val=L.edges c ∧ i.val=0)))) :
    Adjacent L (L.label ⟨c,i⟩) (L.label ⟨c,j⟩) := by
  refine ⟨c,?_⟩
  rcases h with h | h | ⟨hc,h | h⟩
  · left
    let k : Fin (L.edges c) := ⟨i.val,by have := j.isLt; omega⟩
    refine ⟨k,Or.inl ⟨?_,?_⟩⟩
    · congr 1
    · have he : k.succ=j := Fin.ext (by dsimp [k]; omega)
      rw [he]
  · left
    let k : Fin (L.edges c) := ⟨j.val,by have := i.isLt; omega⟩
    refine ⟨k,Or.inr ⟨?_,?_⟩⟩
    · congr 1
    · have he : k.succ=i := Fin.ext (by dsimp [k]; omega)
      rw [he]
  · right
    refine ⟨hc,Or.inl ⟨?_,?_⟩⟩
    · have hi : Fin.last (L.edges c)=i := Fin.ext h.1.symm
      rw [hi]
    · have hj : (0:Fin (L.edges c+1))=j := Fin.ext h.2.symm
      rw [hj]
  · right
    refine ⟨hc,Or.inr ⟨?_,?_⟩⟩
    · have hj : Fin.last (L.edges c)=j := Fin.ext h.1.symm
      rw [hj]
    · have hi : (0:Fin (L.edges c+1))=i := Fin.ext h.2.symm
      rw [hi]

lemma fastAdjacent_sound {m : ℕ} (L : Layout m) (u v : Fin (m-1))
    (h : FastAdjacent L u v) : Adjacent L u v := by
  obtain ⟨⟨c,i⟩,rfl⟩ := L.label.surjective u
  obtain ⟨⟨d,j⟩,rfl⟩ := L.label.surjective v
  dsimp only [FastAdjacent] at h
  rw [L.label.symm_apply_apply,L.label.symm_apply_apply] at h
  obtain ⟨rfl,h⟩ := h
  exact adjacent_of_positions L c i j h

/-- The unique possible reflection partner, in physical one-based indexing. -/
def partnerValue {m : ℕ} (t : ℕ) (u : Fin (m-1)) : ℕ :=
  if physical u<t then t-physical u else m+t-physical u

lemma partnerValue_eq {m t : ℕ} (u v : Fin (m-1)) (h : TargetPair t u v) :
    partnerValue t u=physical v := by
  have hu := u.isLt
  have hv := v.isLt
  dsimp [TargetPair,partnerValue,physical] at *
  split_ifs <;> omega

/-- Only two possible partners per vertex are checked. The inverse layout
makes each adjacency test constant-time instead of searching every edge. -/
def LocalCovers {m : ℕ} (L : Layout m) (r p a : ℕ) : Prop :=
  ∀b:Bool,∀u:Fin (m-1),
    let t := if b then p else r
    let v := partnerValue t u
    if h : 1≤v ∧ v<m then
      0<edgeBound r p a u ⟨v-1,by omega⟩ → FastAdjacent L u ⟨v-1,by omega⟩
    else True

instance {m : ℕ} (L : Layout m) (r p a : ℕ) : Decidable (LocalCovers L r p a) := by
  unfold LocalCovers
  infer_instance

/-- Source-complete coverage follows from the linear-size local certificate. -/
theorem localCovers_sound {m : ℕ} (L : Layout m) (r p a : ℕ)
    (h : LocalCovers L r p a) : Covers L r p a := by
  intro u v hedge
  have ht : TargetPair r u v ∨ TargetPair p u v := by
    unfold edgeBound at hedge
    split_ifs at hedge with h0 hs hc
    · omega
    · rcases hs with hs | hs
      · exact Or.inl (Or.inl hs)
      · exact Or.inr (Or.inl hs)
    · rcases hc with hc | hc
      · exact Or.inl (Or.inr hc)
      · exact Or.inr (Or.inr hc)
    · omega
  have one (b:Bool) (htarget : TargetPair (if b then p else r) u v) : Adjacent L u v := by
    have he := partnerValue_eq u v htarget
    have hv := v.isLt
    have hvalid : 1≤partnerValue (if b then p else r) u ∧
        partnerValue (if b then p else r) u<m := by rw [he]; dsimp [physical]; omega
    have hh := h b u
    dsimp only at hh
    rw [dif_pos hvalid] at hh
    have hi : (⟨partnerValue (if b then p else r) u-1,by omega⟩:Fin (m-1))=v :=
      Fin.ext (by change partnerValue (if b then p else r) u-1=v.val; rw [he]; rfl)
    rw [hi] at hh
    exact fastAdjacent_sound L u v (hh hedge)
  rcases ht with ht | ht
  · exact one false ht
  · exact one true ht

#print axioms localCovers_sound
end SubmittedGenus.RawGraph.PackedAcceptance
