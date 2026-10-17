import Results.Genus.CapFourMass.ExecutableModeLayoutCheck
import Results.Genus.RawGraph.PackedAcceptance.LayoutCheck

/-! A source-exact local validator for the same natural signed layout contract.
It checks two reflection partners per physical position, plus every listed
edge, instead of enumerating every pair of supplied positions. -/
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.PackedAcceptance

local instance {m r p : ℕ} (i : Fin (m-1)) : Decidable (IsFree r p i) := by
  unfold IsFree IsPivot
  infer_instance

/-- The possible free reflection partner, computed in original physical
one-based indexing. Pivots, residue zero and out-of-range values give none. -/
def partnerVertex {m r p : ℕ} (t : ℕ) (u : FreeVertex m r p) : Option (FreeVertex m r p) :=
  let v:=partnerValue t u.val
  if hv : 1≤v ∧ v<m then
    let j : Fin (m-1):=⟨v-1,by omega⟩
    if hj : IsFree r p j then some ⟨j,hj⟩ else none
  else none

lemma partnerVertex_eq_some {m r p t : ℕ} (u v : FreeVertex m r p)
    (ht : TargetPair t u.val v.val) : partnerVertex t u=some v := by
  have he:=partnerValue_eq u.val v.val ht
  have hv : 1≤physical v.val ∧ physical v.val<m := by
    have hi:=v.val.isLt
    dsimp [physical]
    omega
  unfold partnerVertex
  dsimp only
  split_ifs with hvalid hfree
  · congr 1
    apply Subtype.ext
    apply Fin.ext
    change partnerValue t u.val-1=v.val.val
    rw [he]
    rfl
  · exfalso
    apply hfree
    convert v.property using 1
    congr 1
    change partnerValue t u.val-1=v.val.val
    rw [he]
    rfl
  · exact (hvalid (by simpa only [he] using hv)).elim

/-- Every listed ordinary edge is genuine, including the closing pair. -/
def FreeLayoutData.GenuineEdges {m r p : ℕ} (D : FreeLayoutData m r p) : Prop :=
  (∀c,∀k : Fin (D.edges c),(freeGraph m r p).Adj
    (D.forward ⟨c,k.castSucc⟩) (D.forward ⟨c,k.succ⟩)) ∧
  ∀c,D.cycle c=true → (freeGraph m r p).Adj
    (D.forward ⟨c,Fin.last _⟩) (D.forward ⟨c,0⟩)

instance {m r p : ℕ} (D : FreeLayoutData m r p) : Decidable D.GenuineEdges := by
  unfold FreeLayoutData.GenuineEdges freeGraph
  infer_instance

/-- Two possible original target partners suffice for source completeness. -/
def FreeLayoutData.LocalCoverage {m r p : ℕ} (D : FreeLayoutData m r p) : Prop :=
  ∀s : D.Position,∀b : Bool,
    match partnerVertex (if b then p else r) (D.forward s) with
    | none => True
    | some v => (freeGraph m r p).Adj (D.forward s) v →
        D.PositionAdjacent s (D.backward v)

instance {m r p : ℕ} (D : FreeLayoutData m r p) : Decidable D.LocalCoverage := by
  unfold FreeLayoutData.LocalCoverage
  refine @Fintype.decidableForallFintype D.Position _ ?_ inferInstance
  intro s
  refine @Fintype.decidableForallFintype Bool _ ?_ inferInstance
  intro b
  dsimp only
  cases partnerVertex (if b then p else r) (D.forward s) with
  | none => infer_instance
  | some v =>
    change Decidable ((rawGraph m r p).Adj (D.forward s).val v.val → D.PositionAdjacent s (D.backward v))
    infer_instance

/-- All finite producer obligations, with no quadratic adjacency enumeration. -/
def FreeLayoutData.LinearValid {m r p : ℕ} (D : FreeLayoutData m r p) : Prop :=
  D.Inverses ∧ (∀c,D.cycle c=true → 3≤D.edges c) ∧ D.GenuineEdges ∧ D.LocalCoverage

instance {m r p : ℕ} (D : FreeLayoutData m r p) : Decidable D.LinearValid := by
  unfold FreeLayoutData.LinearValid
  infer_instance

def FreeLayoutData.linearCheck {m r p : ℕ} (D : FreeLayoutData m r p) : Bool :=
  decide D.LinearValid

@[simp] lemma FreeLayoutData.linearCheck_eq_true {m r p : ℕ} (D : FreeLayoutData m r p) :
    D.linearCheck=true ↔ D.LinearValid := by simp [FreeLayoutData.linearCheck]

lemma FreeLayoutData.GenuineEdges.adjacent {m r p : ℕ} {D : FreeLayoutData m r p}
    (hD : D.GenuineEdges) (s t : D.Position) (h : D.PositionAdjacent s t) :
    (freeGraph m r p).Adj (D.forward s) (D.forward t) := by
  rcases s with ⟨c,i⟩
  rcases t with ⟨d,j⟩
  rcases h with ⟨hc,h⟩
  dsimp only at hc
  subst d
  dsimp only at h
  rcases h with h | h | ⟨hc,h | h⟩
  · let k : Fin (D.edges c):=⟨i.val,by have := j.isLt; omega⟩
    have hi : k.castSucc=i:=Fin.ext rfl
    have hj : k.succ=j:=Fin.ext h
    simpa only [hi,hj] using hD.1 c k
  · let k : Fin (D.edges c):=⟨j.val,by have := i.isLt; omega⟩
    have hj : k.castSucc=j:=Fin.ext rfl
    have hi : k.succ=i:=Fin.ext h
    simpa only [hi,hj] using (hD.1 c k).symm
  · have hi : i=Fin.last (D.edges c):=Fin.ext h.1
    have hj : j=0:=Fin.ext h.2
    simpa only [hi,hj] using hD.2 c hc
  · have hj : j=Fin.last (D.edges c):=Fin.ext h.1
    have hi : i=0:=Fin.ext h.2
    simpa only [hi,hj] using (hD.2 c hc).symm

lemma FreeLayoutData.LocalCoverage.complete {m r p : ℕ} {D : FreeLayoutData m r p}
    (hinv : D.Inverses) (hD : D.LocalCoverage) (s t : D.Position)
    (hadj : (freeGraph m r p).Adj (D.forward s) (D.forward t)) : D.PositionAdjacent s t := by
  have one (b : Bool) (ht : TargetPair (if b then p else r) (D.forward s).val (D.forward t).val) :
      D.PositionAdjacent s t := by
    have hh:=hD s b
    rw [partnerVertex_eq_some (D.forward s) (D.forward t) ht] at hh
    have he:=hh hadj
    rwa [hinv.1 t] at he
  rcases hadj.2.2.2 with ht | ht
  · exact one false ht
  · exact one true ht

/-- The local Boolean checker implies the already-frozen exact natural-layout
contract in both adjacency directions, including cycle-length rejection. -/
theorem FreeLayoutData.linearValid_sound {m r p : ℕ} (D : FreeLayoutData m r p)
    (h : D.LinearValid) : D.Valid := by
  refine ⟨h.1,h.2.1,fun s t => ⟨?_,?_⟩⟩
  · exact h.2.2.2.complete h.1 s t
  · exact h.2.2.1.adjacent s t

/-- Kernel acceptance of the local checker discharges the full checker. -/
theorem FreeLayoutData.linearCheck_sound {m r p : ℕ} (D : FreeLayoutData m r p)
    (h : D.linearCheck=true) : D.check=true :=
  (D.check_eq_true).mpr (D.linearValid_sound ((D.linearCheck_eq_true).mp h))

end SubmittedGenus.CapFourMass.ExecutableModes
