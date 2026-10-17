import Results.Genus.RawGraph.StrongRuns

/-! Every actual source cycle contains both strong and carried ordinary edges. -/
namespace SubmittedGenus.RawGraph.StrongRuns
open SourceModel Topology

lemma cycle_two_neighbors {V : Type*} {G : SimpleGraph V} (O : OrderedComponent G)
    (hc : O.cycle=true) (i : Fin (O.edges+1)) :
    ∃ j k : Fin (O.edges+1), G.Adj (O.label i) (O.label j) ∧
      G.Adj (O.label i) (O.label k) ∧ j≠k := by
  have hn := O.cycle_min hc
  have hi := i.isLt
  by_cases hz : i.val=0
  · refine ⟨⟨1,by omega⟩,Fin.last _,?_,?_,?_⟩
    · exact (O.adjacent_iff _ _).2 (Or.inl (by simp [hz]))
    · exact (O.adjacent_iff _ _).2 (Or.inr (Or.inr ⟨hc,Or.inl ⟨hz,rfl⟩⟩))
    · intro he; have := congrArg Fin.val he; simp only [Fin.val_last] at this; omega
  by_cases hl : i.val=O.edges
  · refine ⟨0,⟨O.edges-1,by omega⟩,?_,?_,?_⟩
    · exact (O.adjacent_iff _ _).2 (Or.inr (Or.inr ⟨hc,Or.inr ⟨rfl,hl⟩⟩))
    · exact (O.adjacent_iff _ _).2 (Or.inr (Or.inl (by simp only; omega)))
    · intro he; have := congrArg Fin.val he; simp only [Fin.val_zero] at this; omega
  · refine ⟨⟨i.val-1,by omega⟩,⟨i.val+1,by omega⟩,?_,?_,?_⟩
    · exact (O.adjacent_iff _ _).2 (Or.inr (Or.inl (by simp only; omega)))
    · exact (O.adjacent_iff _ _).2 (Or.inl rfl)
    · intro he; have := congrArg Fin.val he; dsimp at this; omega

/-- Two distinct exact-sum reflection matchings on a finite ordered subset
cannot give every vertex degree two. This discharges monochromatic cycles
without an unproved graph-layout or parity premise. -/
lemma finite_two_sums_not_degree_two {V : Type*} [Fintype V] [Nonempty V]
    (w : V→ℕ) (hw : Function.Injective w) {s t : ℕ} (hst : s<t)
    (hdegree : ∀ i, ∃ j k, (w i+w j=s ∨ w i+w j=t) ∧
      (w i+w k=s ∨ w i+w k=t) ∧ j≠k) : False := by
  classical
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image Finset.univ w Finset.univ_nonempty
  obtain ⟨j,k,hj,hk,hne⟩ := hdegree i
  have hex : ∃ v, w i+w v=t := by
    rcases hj with hj | hj
    · rcases hk with hk | hk
      · exact (hne (hw (by omega))).elim
      · exact ⟨k,hk⟩
    · exact ⟨j,hj⟩
  obtain ⟨v,hv⟩ := hex
  obtain ⟨j,k,hj,hk,hne⟩ := hdegree v
  have hex : ∃ u, u≠i ∧ (w v+w u=s ∨ w v+w u=t) := by
    by_cases he : j=i
    · exact ⟨k,by intro h; exact hne (he.trans h.symm),hk⟩
    · exact ⟨j,he,hj⟩
  obtain ⟨u,hui,hu⟩ := hex
  have hlo : w v+w u=s := hu.resolve_right (fun h => hui (hw (by omega)))
  have hm := hmin u (Finset.mem_univ _)
  omega

lemma cycle_not_two_sums {V : Type*} {G : SimpleGraph V} (O : OrderedComponent G)
    (hc : O.cycle=true) (w : V→ℕ) (hw : Function.Injective w)
    {s t : ℕ} (hst : s<t)
    (hedge : ∀ i j, G.Adj (O.label i) (O.label j) →
      w (O.label i)+w (O.label j)=s ∨ w (O.label i)+w (O.label j)=t) : False := by
  apply finite_two_sums_not_degree_two (fun i => w (O.label i)) (hw.comp O.label.injective) hst
  intro i
  obtain ⟨j,k,hj,hk,hne⟩ := cycle_two_neighbors O hc i
  exact ⟨j,k,hedge i j hj,hedge i k hk,hne⟩

noncomputable def componentPhysicalVertex {m r p : ℕ}
    (c : (freeGraph m r p).ConnectedComponent) (i : Fin ((freeComponentOrder m r p c).edges+1)) :
    Fin (m-1) := ((freeComponentOrder m r p c).label i).val.val

lemma componentPhysicalVertex_injective {m r p : ℕ} (c : (freeGraph m r p).ConnectedComponent) :
    Function.Injective (componentPhysicalVertex c) := by
  intro i j he
  apply (freeComponentOrder m r p c).label.injective
  apply Subtype.ext
  exact Subtype.ext he

/-- Both original edge types occur on every actual free cycle. -/
theorem actual_cycle_mixed {m r p a : ℕ} (hp : Parameters m r p a)
    (c : (freeGraph m r p).ConnectedComponent)
    (hc : (freeComponentOrder m r p c).cycle=true) :
    (∃ i j, StrongStep r p (componentPhysicalVertex c i) (componentPhysicalVertex c j)) ∧
    (∃ i j, CarryStep r p (componentPhysicalVertex c i) (componentPhysicalVertex c j)) := by
  classical
  let O := freeComponentOrder m r p c
  have hw : Function.Injective (fun v : c => physical v.val.val) := by
    intro v w he
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    change v.val.val.val+1 = w.val.val.val+1 at he
    change v.val.val.val = w.val.val.val
    omega
  constructor
  · by_contra h
    push Not at h
    apply cycle_not_two_sums O hc (fun v : c => physical v.val.val) hw (show m+r<m+p by have := hp.2.1; omega)
    intro i j hij
    have hadj : (rawGraph m r p).Adj (componentPhysicalVertex c i) (componentPhysicalVertex c j) := hij
    rcases edge_strong_or_carry hadj with hs | he
    · exact (h i j hs).elim
    · exact he.2
  · by_contra h
    push Not at h
    apply cycle_not_two_sums O hc (fun v : c => physical v.val.val) hw hp.2.1
    intro i j hij
    have hadj : (rawGraph m r p).Adj (componentPhysicalVertex c i) (componentPhysicalVertex c j) := hij
    rcases edge_strong_or_carry hadj with he | he
    · exact he.2
    · exact (h i j he).elim

end SubmittedGenus.RawGraph.StrongRuns
