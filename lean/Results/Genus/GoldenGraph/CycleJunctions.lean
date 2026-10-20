import Results.Genus.GoldenGraph.PhysicalJunctions
import Results.Genus.CapFourMass.CycleRunLayout

/-! Closing strong junctions are charged to their distinct physical vertices. -/
namespace SubmittedGenus.GoldenGraph
open RawGraph RawGraph.SourceModel RawGraph.Topology CapFourMass.ActualComponent
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def closingKind {m r p : ℕ} (c : Component m r p) : EdgeKind :=
  kind r p (vertex c (Fin.last _)) (vertex c 0)

abbrev ExtraJunction {m r p : ℕ} (c : Component m r p) :=
  {b : Bool // (freeComponentOrder m r p c).cycle=true ∧
    (if b then (pathWord c).getLastD .carry≠.carry ∧ closingKind c≠.carry
      else closingKind c≠.carry ∧ (pathWord c).headD .carry≠.carry)}

lemma pathWord_headD {m r p : ℕ} (c : Component m r p) (hn : 0 < edgeCount c) :
    (pathWord c).headD .carry=
      kind r p (vertex c (Fin.castSucc ⟨0,hn⟩)) (vertex c (Fin.succ ⟨0,hn⟩)) := by
  have hnon : pathWord c≠[] := by intro he; have:=congrArg List.length he; simp at this; omega
  have hhead : ∀ (l : List EdgeKind) (h : l≠[]), l.headD .carry=l.head h := by
    intro l h
    cases l with
    | nil => contradiction
    | cons a l => rfl
  have hh := hhead (pathWord c) hnon
  rw [hh]
  exact List.head_ofFn _

lemma pathWord_getLastD {m r p : ℕ} (c : Component m r p) (hn : 0 < edgeCount c) :
    (pathWord c).getLastD .carry=
      kind r p (vertex c (Fin.castSucc ⟨edgeCount c-1,by omega⟩))
        (vertex c (Fin.succ ⟨edgeCount c-1,by omega⟩)) := by
  have hnon : pathWord c≠[] := by intro he; have:=congrArg List.length he; simp at this; omega
  simp only [List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast hnon,Option.getD_some]
  exact List.getLast_ofFn _

def extraJunctionPosition {m r p : ℕ} (c : Component m r p) (b : ExtraJunction c) :
    Fin (edgeCount c+1) := if b.val then Fin.last _ else 0

def extraJunctionVertex {m r p : ℕ} (c : Component m r p) (b : ExtraJunction c) :
    JunctionVertex m r p := by
  have hn : 3 ≤ edgeCount c := (freeComponentOrder m r p c).cycle_min b.property.1
  refine ⟨((freeComponentOrder m r p c).label (extraJunctionPosition c b)).val,?_⟩
  rcases b with ⟨b,hb⟩
  cases b
  · have hc : StrongRuns.StrongStep r p (vertex c (Fin.last _)) (vertex c 0) :=
      (kind_ne_carry_iff (closing_adj c hb.1)).mp hb.2.1
    have hf : StrongRuns.StrongStep r p (vertex c (Fin.castSucc ⟨0,by omega⟩))
        (vertex c (Fin.succ ⟨0,by omega⟩)) := by
      apply (kind_ne_carry_iff (consecutive_adj c ⟨0,by omega⟩)).mp
      rw [← pathWord_headD c (by omega)]
      exact hb.2.2
    refine ⟨vertex c (Fin.last _),vertex c (Fin.succ ⟨0,by omega⟩),
      StrongRuns.strongStep_symm hc,hf,?_⟩
    intro he
    have hv := congrArg (fun j : Fin (edgeCount c+1) => j.val) (vertex_injective c he)
    simp only [Fin.val_last,Fin.val_succ] at hv
    omega
  · have hc : StrongRuns.StrongStep r p (vertex c (Fin.last _)) (vertex c 0) :=
      (kind_ne_carry_iff (closing_adj c hb.1)).mp hb.2.2
    let k : Fin (edgeCount c) := ⟨edgeCount c-1,by omega⟩
    have hk : k.succ=Fin.last (edgeCount c) := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_last]; dsimp [k]; omega
    have hl : StrongRuns.StrongStep r p (vertex c k.castSucc) (vertex c k.succ) := by
      apply (kind_ne_carry_iff (consecutive_adj c k)).mp
      rw [← pathWord_getLastD c (by omega)]
      exact hb.2.1
    rw [hk] at hl
    refine ⟨vertex c k.castSucc,vertex c 0,StrongRuns.strongStep_symm hl,hc,?_⟩
    intro he
    have hv := congrArg (fun j : Fin (edgeCount c+1) => j.val) (vertex_injective c he)
    change edgeCount c-1=0 at hv
    omega

abbrev AllJunction {m r p : ℕ} (c : Component m r p) := PathWordJunction c ⊕ ExtraJunction c

def allJunctionPosition {m r p : ℕ} (c : Component m r p) : AllJunction c → Fin (edgeCount c+1) :=
  Sum.elim (pathJunctionPosition c) (extraJunctionPosition c)

def allJunctionVertex {m r p : ℕ} (c : Component m r p) : AllJunction c → JunctionVertex m r p :=
  Sum.elim (pathJunctionVertex c) (extraJunctionVertex c)

lemma allJunctionVertex_val {m r p : ℕ} (c : Component m r p) (j : AllJunction c) :
    (allJunctionVertex c j).val=
      freeOrderedVertexEquiv m r p ⟨c,allJunctionPosition c j⟩ := by
  cases j <;> rfl

lemma allJunctionPosition_injective {m r p : ℕ} (c : Component m r p) :
    Function.Injective (allJunctionPosition c) := by
  intro i j he
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (pathJunctionPosition_injective c he)
    | inr j =>
      have hv := congrArg (fun j : Fin (edgeCount c+1) => j.val) he
      have hi:=i.val.isLt
      cases h : j.val <;> simp [allJunctionPosition,pathJunctionPosition,extraJunctionPosition,h] at hv
      omega
  | inr i =>
    cases j with
    | inl j =>
      have hv := congrArg (fun j : Fin (edgeCount c+1) => j.val) he
      have hj:=j.val.isLt
      cases h : i.val <;> simp [allJunctionPosition,pathJunctionPosition,extraJunctionPosition,h] at hv
      omega
    | inr j =>
      apply congrArg Sum.inr
      apply Subtype.ext
      have hn := (freeComponentOrder m r p c).cycle_min i.property.1
      have hv := congrArg (fun j : Fin (edgeCount c+1) => j.val) he
      change (if i.val then Fin.last (edgeCount c) else (0 : Fin (edgeCount c+1))).val=
        (if j.val then Fin.last (edgeCount c) else (0 : Fin (edgeCount c+1))).val at hv
      change 3 ≤ edgeCount c at hn
      cases hi : i.val <;> cases hj : j.val <;> simp [hi,hj] at hv ⊢ <;> omega

end
end SubmittedGenus.GoldenGraph
