import Results.Genus.CapFourMass.ExecutableModeLayout
import Results.Genus.CapFourMass.ComponentSource

/-! Proof-only identification of validated executable component indices with
actual connected components. The executable evaluator never uses this quotient. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.Topology SimpleGraph

variable {m r p : ℕ} (L : FreeLayout m r p)

def componentKey (c : Fin L.count) : (freeGraph m r p).ConnectedComponent :=
  (freeGraph m r p).connectedComponentMk (L.label ⟨c,0⟩)

lemma component_origin_reachable (hL : L.Valid) (c : Fin L.count)
    (i : Fin (L.edges c+1)) :
    (freeGraph m r p).Reachable (L.label ⟨c,0⟩) (L.label ⟨c,i⟩) := by
  induction i using Fin.induction with
  | zero => exact Reachable.rfl
  | succ i ih => exact ih.trans (hL.consecutive c i).reachable

lemma vertex_componentKey (hL : L.Valid) (c : Fin L.count)
    (i : Fin (L.edges c+1)) :
    (freeGraph m r p).connectedComponentMk (L.label ⟨c,i⟩)=componentKey L c :=
  (ConnectedComponent.eq.mpr (component_origin_reachable L hL c i)).symm

lemma owner_of_reachable (hL : L.Valid) {v w : FreeVertex m r p}
    (hv : (freeGraph m r p).Reachable v w) :
    (L.label.symm w).1=(L.label.symm v).1 := by
  apply reachable_mem_closed (freeGraph m r p)
    (s:={x | (L.label.symm x).1=(L.label.symm v).1}) ?_ rfl hv
  intro x y hx hxy
  have he := hL.no_cross (L.label.symm x) (L.label.symm y) (by simpa using hxy)
  exact he.symm.trans hx

lemma componentKey_bijective (hL : L.Valid) : Function.Bijective (componentKey L) := by
  constructor
  · intro c d he
    have hr : (freeGraph m r p).Reachable (L.label ⟨c,0⟩) (L.label ⟨d,0⟩) :=
      ConnectedComponent.eq.mp he
    have ho := owner_of_reachable L hL hr
    simpa using ho.symm
  · intro c
    obtain ⟨v,rfl⟩ := c.exists_rep
    obtain ⟨⟨d,i⟩,hi⟩:=L.label.surjective v
    refine ⟨d,?_⟩
    change componentKey L d=(freeGraph m r p).connectedComponentMk v
    rw [←hi]
    exact (vertex_componentKey L hL d i).symm

noncomputable def componentEquiv (hL : L.Valid) :
    Fin L.count ≃ (freeGraph m r p).ConnectedComponent :=
  Equiv.ofBijective (componentKey L) (componentKey_bijective L hL)

noncomputable def componentLabel (hL : L.Valid) (c : Fin L.count) :
    Fin (L.edges c+1) ≃ componentKey L c :=
  Equiv.ofBijective (fun i => ⟨L.label ⟨c,i⟩,vertex_componentKey L hL c i⟩) (by
    constructor
    · intro i j he
      have hs:=L.label.injective (congrArg Subtype.val he)
      exact Sigma.mk.inj_iff.mp hs |>.2 |> eq_of_heq
    · intro v
      obtain ⟨⟨d,i⟩,hi⟩:=L.label.surjective v.val
      have hk : componentKey L d=componentKey L c := by
        have he:=vertex_componentKey L hL d i
        rw [hi] at he
        exact he.symm.trans v.property
      have hc : d=c := (componentKey_bijective L hL).1 hk
      subst d
      exact ⟨i,Subtype.ext hi⟩)

noncomputable def orderedComponent (hL : L.Valid) (c : Fin L.count) :
    OrderedComponent (componentKey L c).toSimpleGraph where
  edges := L.edges c
  label := componentLabel L hL c
  cycle := L.cycle c
  cycle_min := hL.1 c
  adjacent_iff := by
    intro i j
    change (freeGraph m r p).Adj (L.label ⟨c,i⟩) (L.label ⟨c,j⟩) ↔ _
    rw [hL.adjacent_iff c i j]
    tauto

@[simp] lemma ordered_label_val (hL : L.Valid) (c : Fin L.count)
    (i : Fin (L.edges c+1)) :
    ((orderedComponent L hL c).label i).val=L.label ⟨c,i⟩ := rfl

lemma ordered_edges_eq_actual (hL : L.Valid) (c : Fin L.count) :
    (orderedComponent L hL c).edges=ActualComponent.edgeCount (componentKey L c) := by
  have hc:=Fintype.card_congr ((componentLabel L hL c).trans
    (freeComponentOrder m r p (componentKey L c)).label.symm)
  simp only [Fintype.card_fin] at hc
  change L.edges c=ActualComponent.edgeCount (componentKey L c)
  unfold ActualComponent.edgeCount
  omega

#print axioms componentKey_bijective
#print axioms orderedComponent
end SubmittedGenus.CapFourMass.ExecutableModes
