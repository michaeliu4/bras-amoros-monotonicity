import Results.Genus.CapFourMass.RunCounts

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Incidence
open CapFiveMass.LocalSource
attribute [local instance] Classical.propDecidable

private def RestrictedPair {m : ℕ} (r p : ℕ) (i j : Fin (m-1)) : Prop :=
  StrongEdge r p i j ∧ r<physical i ∧ r<physical j

private def RestrictedAdj {m : ℕ} (r p : ℕ) (i j : FreeVertex m r p) : Prop :=
  (freeGraph m r p).Adj i j ∧ RestrictedPair r p i.val j.val

private lemma restricted_symm {m r p : ℕ} {i j : FreeVertex m r p}
    (h : RestrictedAdj r p i j) : RestrictedAdj r p j i :=
  ⟨h.1.symm,by rcases h.2 with ⟨hs,hi,hj⟩; exact ⟨by simpa [StrongEdge,Nat.add_comm] using hs,hj,hi⟩⟩

private def restrictedCount {m r p : ℕ} (c : Component m r p) : ℕ :=
  (Finset.univ.filter (fun j : Fin (edgeCount c) =>
    RestrictedPair r p (vertex c j.castSucc) (vertex c j.succ))).card +
  if (freeComponentOrder m r p c).cycle=true ∧
    RestrictedPair r p (vertex c (Fin.last _)) (vertex c 0) then 1 else 0

private lemma restricted_word_count {m r p : ℕ} (c : Component m r p) :
    restrictedLength (sourceWord c)=restrictedCount c := by
  have hpath : restrictedLength (pathWord c)=
      (Finset.univ.filter (fun j : Fin (edgeCount c) =>
        RestrictedPair r p (vertex c j.castSucc) (vertex c j.succ))).card := by
    unfold restrictedLength pathWord
    simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn,restricted_kind_indicator]
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro j hj
    unfold RestrictedPair StrongEdge
    split_ifs <;> rfl
  unfold sourceWord restrictedCount
  by_cases hc : (freeComponentOrder m r p c).cycle=true
  · simp only [hc,if_true,true_and]
    simp only [closedWord,restrictedLength,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,add_zero]
    change restrictedLength (pathWord c)+_= _
    rw [hpath,restricted_kind_indicator]
    simp only [RestrictedPair,StrongEdge]
    congr 1
    split_ifs <;> rfl
  · simp only [hc,if_false,false_and,add_zero]
    exact hpath

private lemma restricted_pairs_count (m r p : ℕ) :
    (Finset.univ.filter (fun ij : FreeVertex m r p × FreeVertex m r p =>
      RestrictedAdj r p ij.1 ij.2)).card=2*totalRestrictedLength m r p := by
  rw [relation_component_card (freeGraph m r p) (freeGraph_noThird m r p)
    (freeGraph_noTriangle m r p) (RestrictedAdj r p) (fun _ _ h => h.1)]
  have hlocal (c : Component m r p) :
      (Finset.univ.filter (fun ij : Fin (edgeCount c + 1) × Fin (edgeCount c + 1) =>
        RestrictedAdj r p ((freeComponentOrder m r p c).label ij.1).val
          ((freeComponentOrder m r p c).label ij.2).val)).card = 2 * restrictedCount c := by
    let O := freeComponentOrder m r p c
    let R (u v : c) := RestrictedAdj r p u.val v.val
    have hh := O.relation_edge_card R (fun _ _ h => restricted_symm h) (fun _ _ h => h.1)
    have hcons (j : Fin O.edges) : R (O.label j.castSucc) (O.label j.succ) ↔
        RestrictedPair r p (vertex c j.castSucc) (vertex c j.succ) := by
      exact and_iff_right (CapFiveMass.ActualComponent.consecutive_adj c j)
    have hclose : (O.cycle=true ∧ R (O.label 0) (O.label (Fin.last O.edges))) ↔
        O.cycle=true ∧ RestrictedPair r p (vertex c (Fin.last _)) (vertex c 0) := by
      constructor
      · rintro ⟨hc,_,hs,hi,hj⟩
        change StrongEdge r p (vertex c 0) (vertex c (Fin.last _)) at hs
        exact ⟨hc,by simpa [StrongEdge,Nat.add_comm] using hs,hj,hi⟩
      · rintro ⟨hc,hs,hi,hj⟩
        refine ⟨hc,(CapFiveMass.ActualComponent.closing_adj c hc).symm,?_,hj,hi⟩
        change StrongEdge r p (vertex c 0) (vertex c (Fin.last _))
        simpa [StrongEdge,Nat.add_comm] using hs
    simp_rw [hcons,hclose] at hh
    exact hh
  calc
    _ = ∑ c : Component m r p,2*restrictedCount c := by
      apply Finset.sum_congr rfl
      intro c _
      exact hlocal c
    _ = _ := by
      simp_rw [←restricted_word_count]
      rw [←Finset.mul_sum]
      rfl

theorem restricted_edges_match (m r p : ℕ) :
    (StrongEdgeCounts.restrictedEdges m r p).card=totalRestrictedLength m r p := by
  have hupper : (Finset.univ.filter (fun ij : FreeVertex m r p × FreeVertex m r p =>
      ij.1 < ij.2 ∧ RestrictedAdj r p ij.1 ij.2)).card =
      (StrongEdgeCounts.restrictedEdges m r p).card := by
    apply Finset.card_bij (fun ij _ => (ij.1.val,ij.2.val))
    · intro ij hij
      obtain ⟨hlt,hadj,hs,hi,hj⟩ := (Finset.mem_filter.mp hij).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hlt,ij.1.property,ij.2.property,hs⟩,hi,hj⟩
    · intro ij hij kl hkl he
      exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
    · rintro ⟨i,j⟩ hij
      obtain ⟨he,hri,hrj⟩ := Finset.mem_filter.mp hij
      obtain ⟨_,hlt,hi,hj,hs⟩ := Finset.mem_filter.mp he
      let u : FreeVertex m r p := ⟨i,hi⟩
      let v : FreeVertex m r p := ⟨j,hj⟩
      refine ⟨(u,v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt,?_,hs,hri,hrj⟩,rfl⟩
      refine ⟨ne_of_lt hlt,hi,hj,?_⟩
      rcases hs with hs | hs
      · exact Or.inl (Or.inl hs)
      · exact Or.inr (Or.inl hs)
  have hdiag : (Finset.univ.filter (fun i : FreeVertex m r p => RestrictedAdj r p i i))=∅ := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
    exact fun h => (freeGraph m r p).irrefl h.1
  have hh := symmetric_relation_card (RestrictedAdj (m:=m) r p)
    (fun _ _ h => restricted_symm h)
  rw [hdiag,Finset.card_empty,add_zero,hupper,restricted_pairs_count] at hh
  omega

theorem total_restricted_formula {m r p : ℕ} (hp : Parameters m r p 4) :
    totalRestrictedLength m r p=(p-1)/2-r := by
  rw [←restricted_edges_match]
  exact StrongEdgeCounts.restricted_edges_formula hp

#print axioms total_restricted_formula
end SubmittedGenus.CapFourMass.ActualComponent
