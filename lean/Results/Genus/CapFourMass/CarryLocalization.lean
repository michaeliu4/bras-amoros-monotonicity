import Results.Genus.CapFourMass.CompilerCounts
import Results.Genus.FixedPivot.CanonicalSource

/-! Canonical carry tails and their surviving ports lie in unique actual raw
components. This is source geometry for core-first complete mode regrouping. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot

section Geometry
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)

/-- A tail position is its original physical coordinate, with both pivots absent. -/
def tailVertex (a : CarryRepresentative N d hN)
    (t : Fin (carryTailSize N d hN a)) : FreeVertex (r+N) r (r+d) := by
  let v:=carryTailLabel N d hN a t.val
  have hv : d<v ∧ v<N := carryTailLabel_vertex N d hN a t.isLt
  refine ⟨⟨r+v-1,by omega⟩,?_⟩
  change ¬(r+v-1+1=r ∨ r+v-1+1=r+d)
  omega

lemma tailVertex_physical (a : CarryRepresentative N d hN)
    (t : Fin (carryTailSize N d hN a)) :
    physical (tailVertex hr hN a t).val=r+carryTailLabel N d hN a t.val := by
  have hv:=carryTailLabel_vertex N d hN a t.isLt
  change r+carryTailLabel N d hN a t.val-1+1=_
  omega

lemma tailVertex_injective (a : CarryRepresentative N d hN) :
    Function.Injective (tailVertex hr hN a) := by
  intro t s he
  have he':=congrArg (fun i : FreeVertex (r+N) r (r+d) => physical i.val) he
  rw [tailVertex_physical,tailVertex_physical] at he'
  have hf := carryComponentLabel_injective N d hN a
    (a₁:=⟨t.val+1,carryTail_position N d hN a t.isLt⟩)
    (a₂:=⟨s.val+1,carryTail_position N d hN a s.isLt⟩)
    (show carryComponentLabel N d hN a (t.val+1)=
      carryComponentLabel N d hN a (s.val+1) by
      change r+carryComponentLabel N d hN a (t.val+1)=
        r+carryComponentLabel N d hN a (s.val+1) at he'
      omega)
  apply Fin.ext
  have hval := congrArg Fin.val hf
  change t.val+1=s.val+1 at hval
  omega

lemma tail_adj_iff (a : CarryRepresentative N d hN)
    (t s : Fin (carryTailSize N d hN a)) :
    (freeGraph (r+N) r (r+d)).Adj (tailVertex hr hN a t) (tailVertex hr hN a s) ↔
      t.val+1=s.val ∨ s.val+1=t.val := by
  have ht:=carryTailLabel_vertex N d hN a t.isLt
  have hs:=carryTailLabel_vertex N d hN a s.isLt
  have hi:=carryTail_incidence_iff N d hN a t.isLt s.isLt
  change ((tailVertex hr hN a t).val≠(tailVertex hr hN a s).val ∧
    IsFree r (r+d) (tailVertex hr hN a t).val ∧ IsFree r (r+d) (tailVertex hr hN a s).val ∧
    (TargetPair r (tailVertex hr hN a t).val (tailVertex hr hN a s).val ∨
      TargetPair (r+d) (tailVertex hr hN a t).val (tailVertex hr hN a s).val)) ↔ _
  constructor
  · rintro ⟨hne,_,_,he⟩
    unfold TargetPair at he
    rw [tailVertex_physical,tailVertex_physical] at he
    have hinc : CarryIncidence N d (carryTailLabel N d hN a t.val)
        (carryTailLabel N d hN a s.val) := by unfold CarryIncidence; omega
    rcases hi.mp hinc with h | h | ⟨_,hts,hss⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hne (congrArg Subtype.val (congrArg (tailVertex hr hN a)
        (Fin.ext (hts.trans hss.symm)))))
  · intro he
    have hinc:=hi.mpr (he.elim Or.inl (fun h => Or.inr (Or.inl h)))
    refine ⟨?_,(tailVertex hr hN a t).property,(tailVertex hr hN a s).property,?_⟩
    · intro hval
      have hts:=(tailVertex_injective hr hN a) (Subtype.ext hval)
      have := congrArg Fin.val hts
      omega
    · unfold TargetPair
      rw [tailVertex_physical,tailVertex_physical]
      unfold CarryIncidence at hinc
      omega

variable (hbig : 2*d<N)

/-- The canonical tail is nonempty even in the isolated loop corner. -/
def owner (a : CarryRepresentative N d hN) : (freeGraph (r+N) r (r+d)).ConnectedComponent :=
  (freeGraph (r+N) r (r+d)).connectedComponentMk
    (tailVertex hr hN a ⟨0,carryTailSize_positive N d hN hbig a⟩)

/-- Every position in one canonical carry tail belongs to the same genuine raw
component. No source component certificate is assumed. -/
theorem tail_owner (a : CarryRepresentative N d hN)
    (t : Fin (carryTailSize N d hN a)) :
    (freeGraph (r+N) r (r+d)).connectedComponentMk (tailVertex hr hN a t)=
      owner hr hN hbig a := by
  have haux : ∀ k (hk : k<carryTailSize N d hN a),
      (freeGraph (r+N) r (r+d)).connectedComponentMk (tailVertex hr hN a ⟨k,hk⟩)=
        owner hr hN hbig a := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k<carryTailSize N d hN a := by omega
      have hadj := (tail_adj_iff hr hN a ⟨k,hk'⟩ ⟨k+1,hk⟩).2 (Or.inl rfl)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans (ih hk')
  exact haux t.val t.isLt

/-- A surviving carry port is its genuine free core coordinate. -/
def portVertex (q : Fin d) (hq : q.val+1≠d) : FreeVertex (r+N) r (r+d) := by
  have hbound := hN
  clear hbig hd
  refine ⟨⟨r+q.val,by have := q.isLt; omega⟩,?_⟩
  change ¬(r+q.val+1=r ∨ r+q.val+1=r+d)
  omega

lemma portVertex_physical (q : Fin d) (hq : q.val+1≠d) :
    physical (portVertex hr hN q hq).val=r+q.val+1 := rfl

lemma port_tail_adj (q : Fin d) (hq : q.val+1≠d)
    (a : CarryRepresentative N d hN) (t : Fin (carryTailSize N d hN a))
    (hinc : CarryIncidence N d (carryTailLabel N d hN a t.val) (q.val+1)) :
    (freeGraph (r+N) r (r+d)).Adj (portVertex hr hN q hq) (tailVertex hr hN a t) := by
  have ht:=carryTailLabel_vertex N d hN a t.isLt
  have hq':=q.isLt
  change ((portVertex hr hN q hq).val≠(tailVertex hr hN a t).val ∧
    IsFree r (r+d) (portVertex hr hN q hq).val ∧ IsFree r (r+d) (tailVertex hr hN a t).val ∧
    (TargetPair r (portVertex hr hN q hq).val (tailVertex hr hN a t).val ∨
      TargetPair (r+d) (portVertex hr hN q hq).val (tailVertex hr hN a t).val))
  refine ⟨?_,(portVertex hr hN q hq).property,(tailVertex hr hN a t).property,?_⟩
  · intro he
    have hh:=congrArg physical he
    rw [portVertex_physical,tailVertex_physical] at hh
    omega
  · unfold TargetPair
    rw [portVertex_physical,tailVertex_physical]
    unfold CarryIncidence at hinc
    omega

include hd in
/-- Every surviving initial port is in its canonical tail's actual component. -/
theorem initial_port_owner (a : CarryRepresentative N d hN) (ha : a.val.val+1≠d) :
    (freeGraph (r+N) r (r+d)).connectedComponentMk (portVertex hr hN a.val ha)=
      owner hr hN hbig a := by
  let t : Fin (carryTailSize N d hN a):=⟨0,carryTailSize_positive N d hN hbig a⟩
  have hinc := (carryTail_port_incidence_iff N d hd hN a t.isLt
    (show 0<a.val.val+1 ∧ a.val.val+1≤d by have := a.val.isLt; omega)).mpr
      (Or.inl ⟨rfl,rfl⟩)
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (port_tail_adj hr hN a.val ha a t hinc)).trans (tail_owner hr hN hbig a t)

include hd in
/-- Paired terminal ports likewise stay inside that same actual component. -/
theorem terminal_port_owner (a : CarryRepresentative N d hN)
    (hf : a.val≠portPartner N d hN a.val)
    (ha : (portPartner N d hN a.val).val+1≠d) :
    (freeGraph (r+N) r (r+d)).connectedComponentMk
      (portVertex hr hN (portPartner N d hN a.val) ha)=owner hr hN hbig a := by
  have hn:=carryTailSize_positive N d hN hbig a
  let t : Fin (carryTailSize N d hN a):=⟨carryTailSize N d hN a-1,by omega⟩
  have hinc := (carryTail_port_incidence_iff N d hd hN a t.isLt
    (show 0<(portPartner N d hN a.val).val+1 ∧ (portPartner N d hN a.val).val+1≤d by
      have := (portPartner N d hN a.val).isLt; omega)).mpr
        (Or.inr ⟨hf,rfl,rfl⟩)
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (port_tail_adj hr hN (portPartner N d hN a.val) ha a t hinc)).trans (tail_owner hr hN hbig a t)

include hd in
/-- Every arbitrary surviving port belongs to the component of its canonical
involution representative. -/
theorem port_owner (q : Fin d) (hq : q.val+1≠d) :
    (freeGraph (r+N) r (r+d)).connectedComponentMk (portVertex hr hN q hq)=
      owner hr hN hbig (carryRepresentative N d hN q) := by
  let a:=carryRepresentative N d hN q
  by_cases ho : portPartner N d hN q≤q
  · have hav : a.val=q := max_eq_left ho
    have ha : a.val.val+1≠d := by simpa only [hav] using hq
    have hh:=initial_port_owner hr hd hN hbig a ha
    simpa only [hav] using hh
  · have hav : a.val=portPartner N d hN q := max_eq_right (le_of_not_ge ho)
    have hback : portPartner N d hN a.val=q := by rw [hav,portPartner_involutive]
    have hf : a.val≠portPartner N d hN a.val := by
      rw [hav,portPartner_involutive]
      exact fun he => ho (le_of_eq he)
    have ha : (portPartner N d hN a.val).val+1≠d := by simpa only [hback] using hq
    have hh:=terminal_port_owner hr hd hN hbig a hf ha
    simpa only [hback] using hh

/-- Complete mode variables partition by actual graph component. -/
abbrev ModeFiber (c : (freeGraph (r+N) r (r+d)).ConnectedComponent) :=
  {a : CarryRepresentative N d hN // owner hr hN hbig a=c}

/-- This is a genuine equivalence of complete mode assignments, before any
sum or absolute value is rearranged. -/
def modeAssignmentEquiv : (CarryRepresentative N d hN→Bool) ≃
    ((c : (freeGraph (r+N) r (r+d)).ConnectedComponent) → ModeFiber hr hN hbig c→Bool) where
  toFun choice := fun _ a => choice a.val
  invFun choice := fun a => choice (owner hr hN hbig a) ⟨a,rfl⟩
  left_inv _ := rfl
  right_inv choice := by
    funext c a
    rcases a with ⟨a,ha⟩
    subst c
    rfl

@[simp] lemma modeAssignmentEquiv_apply (choice : CarryRepresentative N d hN→Bool)
    (c : (freeGraph (r+N) r (r+d)).ConnectedComponent) (a : ModeFiber hr hN hbig c) :
    modeAssignmentEquiv hr hN hbig choice c a=choice a.val := rfl

end Geometry
end SubmittedGenus.CapFourMass.CarryLocalization
