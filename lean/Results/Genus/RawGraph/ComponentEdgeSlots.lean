import Results.Genus.RawGraph.ComponentEdgeProduct

/-! One slot for each physical unordered edge, including one closing slot
exactly for a cycle. This transports arbitrary signed edge products. -/
namespace SubmittedGenus.RawGraph.Topology.OrderedComponent
noncomputable section
variable {V : Type*} {G : SimpleGraph V}

abbrev EdgeSlot (c : OrderedComponent G) := Fin c.edges ⊕ {_u : Unit // c.cycle=true}

def slotEdge (c : OrderedComponent G) : EdgeSlot c→G.edgeSet
  | .inl k => ⟨s(c.label k.castSucc,c.label k.succ),
      (c.adjacent_iff _ _).mpr (Or.inl rfl)⟩
  | .inr u => ⟨s(c.label (Fin.last c.edges),c.label 0),
      (c.adjacent_iff _ _).mpr (Or.inr (Or.inr ⟨u.property,Or.inr ⟨rfl,rfl⟩⟩))⟩

lemma slot_consecutive_ne_close (c : OrderedComponent G) (hc : c.cycle=true) (k : Fin c.edges) :
    s(c.label k.castSucc,c.label k.succ)≠s(c.label (Fin.last c.edges),c.label 0) := by
  intro he
  have hn:=c.cycle_min hc
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  all_goals
    have h1':=congrArg Fin.val (c.label.injective h1)
    have h2':=congrArg Fin.val (c.label.injective h2)
    simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_zero,Fin.val_last] at h1' h2'
    omega

lemma slotEdge_injective (c : OrderedComponent G) : Function.Injective (slotEdge c) := by
  intro a b he
  have he':=congrArg Subtype.val he
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      change s(c.label i.castSucc,c.label i.succ)=s(c.label j.castSucc,c.label j.succ) at he'
      rcases Sym2.eq_iff.mp he' with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact congrArg Sum.inl (Fin.ext (congrArg (fun k : Fin (c.edges+1) => k.val) (c.label.injective h1)))
      · have h1':=congrArg Fin.val (c.label.injective h1)
        have h2':=congrArg Fin.val (c.label.injective h2)
        simp only [Fin.val_castSucc,Fin.val_succ] at h1' h2'
        omega
    | inr u => exact False.elim (slot_consecutive_ne_close c u.property i he')
  | inr u =>
    cases b with
    | inl j => exact False.elim (slot_consecutive_ne_close c u.property j he'.symm)
    | inr v => exact congrArg Sum.inr (Subsingleton.elim u v)

lemma slotEdge_surjective (c : OrderedComponent G) : Function.Surjective (slotEdge c) := by
  intro e
  obtain ⟨e,he⟩:=e
  induction e using Sym2.ind with
  | h v w =>
    obtain ⟨i,rfl⟩:=c.label.surjective v
    obtain ⟨j,rfl⟩:=c.label.surjective w
    have ha : G.Adj (c.label i) (c.label j) := he
    rcases (c.adjacent_iff i j).mp ha with h | h | ⟨hc,h⟩
    · have hi : i.val<c.edges := by have:=j.isLt; omega
      let k : Fin c.edges:=⟨i.val,hi⟩
      refine ⟨.inl k,Subtype.ext ?_⟩
      change s(c.label k.castSucc,c.label k.succ)=s(c.label i,c.label j)
      apply Sym2.eq_iff.mpr
      exact Or.inl ⟨congrArg c.label (Fin.ext rfl),congrArg c.label (Fin.ext h)⟩
    · have hj : j.val<c.edges := by have:=i.isLt; omega
      let k : Fin c.edges:=⟨j.val,hj⟩
      refine ⟨.inl k,Subtype.ext ?_⟩
      change s(c.label k.castSucc,c.label k.succ)=s(c.label i,c.label j)
      apply Sym2.eq_iff.mpr
      exact Or.inr ⟨congrArg c.label (Fin.ext rfl),congrArg c.label (Fin.ext h)⟩
    · refine ⟨.inr ⟨(),hc⟩,Subtype.ext ?_⟩
      change s(c.label (Fin.last c.edges),c.label 0)=s(c.label i,c.label j)
      apply Sym2.eq_iff.mpr
      rcases h with ⟨hi,hj⟩ | ⟨hj,hi⟩
      · exact Or.inr ⟨congrArg c.label (Fin.ext hj.symm),congrArg c.label (Fin.ext hi.symm)⟩
      · exact Or.inl ⟨congrArg c.label (Fin.ext hi.symm),congrArg c.label (Fin.ext hj.symm)⟩

/-- Exactly one source slot per unordered edge. No edge weight is squared,
repeated, or simplified by idempotence. -/
def edgeSlotEquiv (c : OrderedComponent G) : EdgeSlot c≃G.edgeSet :=
  Equiv.ofBijective (slotEdge c) ⟨slotEdge_injective c,slotEdge_surjective c⟩

@[simp] lemma edgeSlotEquiv_consecutive (c : OrderedComponent G) (k : Fin c.edges) :
    (edgeSlotEquiv c (.inl k)).val=s(c.label k.castSucc,c.label k.succ) := rfl

@[simp] lemma edgeSlotEquiv_closing (c : OrderedComponent G) (u : Unit) (hc : c.cycle=true) :
    (edgeSlotEquiv c (.inr ⟨u,hc⟩)).val=s(c.label (Fin.last c.edges),c.label 0) := rfl

end
end SubmittedGenus.RawGraph.Topology.OrderedComponent
