import Results.Genus.CapFourMass.ExecutableModeLayout

/-! Full finite validation of supplied natural-layout data, including the
physical forward/inverse bijection. Acceptance produces the proof-bearing
layout used by the signed source adapter. -/
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.Topology

structure FreeLayoutData (m r p : ℕ) where
  count : ℕ
  edges : Fin count→ℕ
  cycle : Fin count→Bool
  forward : (Σc:Fin count,Fin (edges c+1))→FreeVertex m r p
  backward : FreeVertex m r p→(Σc:Fin count,Fin (edges c+1))

abbrev FreeLayoutData.Position {m r p : ℕ} (D : FreeLayoutData m r p) :=
  Σc:Fin D.count,Fin (D.edges c+1)

def FreeLayoutData.Inverses {m r p : ℕ} (D : FreeLayoutData m r p) : Prop :=
  (∀s,D.backward (D.forward s)=s) ∧ (∀v,D.forward (D.backward v)=v)

instance {m r p : ℕ} (D : FreeLayoutData m r p) : Decidable D.Inverses := by
  letI : DecidablePred (IsFree (m:=m) r p) := fun i => by
    unfold IsFree IsPivot
    infer_instance
  letI : Fintype (FreeVertex m r p) := Subtype.fintype _
  unfold FreeLayoutData.Inverses
  infer_instance

def FreeLayoutData.PositionAdjacent {m r p : ℕ} (D : FreeLayoutData m r p)
    (s t : D.Position) : Prop :=
  s.1=t.1 ∧ (s.2.val+1=t.2.val ∨ t.2.val+1=s.2.val ∨
    (D.cycle s.1=true ∧ ((s.2.val=D.edges s.1 ∧ t.2.val=0) ∨
      (t.2.val=D.edges s.1 ∧ s.2.val=0))))

instance {m r p : ℕ} (D : FreeLayoutData m r p) (s t : D.Position) :
    Decidable (D.PositionAdjacent s t) := by
  unfold FreeLayoutData.PositionAdjacent
  infer_instance

/-- Every assumption about the supplied graph data is checked here. Free
physical vertex membership is already part of the typed label data. -/
def FreeLayoutData.Valid {m r p : ℕ} (D : FreeLayoutData m r p) : Prop :=
  D.Inverses ∧ (∀c,D.cycle c=true → 3≤D.edges c) ∧
    ∀s t : D.Position,(freeGraph m r p).Adj (D.forward s) (D.forward t) ↔ D.PositionAdjacent s t

instance {m r p : ℕ} (D : FreeLayoutData m r p) : Decidable D.Valid := by
  unfold FreeLayoutData.Valid freeGraph
  infer_instance

/-- Executable Boolean validator; no assumed producer correctness is used. -/
def FreeLayoutData.check {m r p : ℕ} (D : FreeLayoutData m r p) : Bool := decide D.Valid

@[simp] lemma FreeLayoutData.check_eq_true {m r p : ℕ} (D : FreeLayoutData m r p) :
    D.check=true ↔ D.Valid := by simp [FreeLayoutData.check]

/-- The inverse function is supplied explicitly and checked, never chosen. -/
def FreeLayoutData.toLayout {m r p : ℕ} (D : FreeLayoutData m r p) (h : D.Inverses) :
    FreeLayout m r p where
  count := D.count
  edges := D.edges
  cycle := D.cycle
  label := ⟨D.forward,D.backward,h.1,h.2⟩

lemma FreeLayoutData.toLayout_valid {m r p : ℕ} (D : FreeLayoutData m r p) (h : D.Valid) :
    (D.toLayout h.1).Valid := h.2

def FreeLayoutData.acceptedLayout {m r p : ℕ} (D : FreeLayoutData m r p) (h : D.check=true) :
    FreeLayout m r p := D.toLayout ((D.check_eq_true).mp h).1

/-- Concrete kernel acceptance discharges every natural-layout premise. -/
theorem FreeLayoutData.acceptedLayout_valid {m r p : ℕ} (D : FreeLayoutData m r p)
    (h : D.check=true) : (D.acceptedLayout h).Valid :=
  D.toLayout_valid ((D.check_eq_true).mp h)

@[simp] lemma FreeLayoutData.acceptedLayout_label {m r p : ℕ} (D : FreeLayoutData m r p)
    (h : D.check=true) (s : D.Position) : (D.acceptedLayout h).label s=D.forward s := rfl

end SubmittedGenus.CapFourMass.ExecutableModes
