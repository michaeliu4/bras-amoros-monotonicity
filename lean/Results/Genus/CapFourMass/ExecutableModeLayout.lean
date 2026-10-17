import Results.Genus.RawGraph.RawComponents

/-! A decidably validated natural free-vertex layout for executable signed
source evaluation. All original nonpivot coordinates occur exactly once;
neutral links and duplicate cycle edges are excluded by the exact adjacency
check and the minimum cycle length. -/
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.Topology

/-- Computational physical order only. The separate `Valid` predicate checks
that these are precisely the original natural graph components. -/
structure FreeLayout (m r p : ℕ) where
  count : ℕ
  edges : Fin count→ℕ
  cycle : Fin count→Bool
  label : (Σc:Fin count,Fin (edges c+1))≃FreeVertex m r p

abbrev FreeLayout.Position {m r p : ℕ} (L : FreeLayout m r p) :=
  Σc:Fin L.count,Fin (L.edges c+1)

/-- The strict path/cycle relation in the supplied ordered coordinates. -/
def FreeLayout.PositionAdjacent {m r p : ℕ} (L : FreeLayout m r p)
    (s t : L.Position) : Prop :=
  s.1=t.1 ∧ (s.2.val+1=t.2.val ∨ t.2.val+1=s.2.val ∨
    (L.cycle s.1=true ∧ ((s.2.val=L.edges s.1 ∧ t.2.val=0) ∨
      (t.2.val=L.edges s.1 ∧ s.2.val=0))))

instance {m r p : ℕ} (L : FreeLayout m r p) (s t : L.Position) :
    Decidable (L.PositionAdjacent s t) := by
  unfold FreeLayout.PositionAdjacent
  infer_instance

/-- Finite exact source validation. In particular, a two-vertex cycle that
would multiply the same signed edge twice is rejected. Unary loops remain
in their original physical Domain, rather than becoming graph edges. -/
def FreeLayout.Valid {m r p : ℕ} (L : FreeLayout m r p) : Prop :=
  (∀c,L.cycle c=true → 3≤L.edges c) ∧
    ∀s t : L.Position,(freeGraph m r p).Adj (L.label s) (L.label t) ↔ L.PositionAdjacent s t

instance {m r p : ℕ} (L : FreeLayout m r p) : Decidable L.Valid := by
  unfold FreeLayout.Valid freeGraph
  infer_instance

lemma FreeLayout.Valid.adjacent_iff {m r p : ℕ} {L : FreeLayout m r p} (hL : L.Valid)
    (c : Fin L.count) (i j : Fin (L.edges c+1)) :
    (freeGraph m r p).Adj (L.label ⟨c,i⟩) (L.label ⟨c,j⟩) ↔
      i.val+1=j.val ∨ j.val+1=i.val ∨
        (L.cycle c=true ∧ ((i.val=L.edges c ∧ j.val=0) ∨ (j.val=L.edges c ∧ i.val=0))) := by
  simpa only [FreeLayout.PositionAdjacent,true_and] using hL.2 ⟨c,i⟩ ⟨c,j⟩

lemma FreeLayout.Valid.consecutive {m r p : ℕ} {L : FreeLayout m r p} (hL : L.Valid)
    (c : Fin L.count) (i : Fin (L.edges c)) :
    (freeGraph m r p).Adj (L.label ⟨c,i.castSucc⟩) (L.label ⟨c,i.succ⟩) :=
  (hL.adjacent_iff c i.castSucc i.succ).mpr (Or.inl rfl)

lemma FreeLayout.Valid.closing {m r p : ℕ} {L : FreeLayout m r p} (hL : L.Valid)
    (c : Fin L.count) (hc : L.cycle c=true) :
    (freeGraph m r p).Adj (L.label ⟨c,Fin.last _⟩) (L.label ⟨c,0⟩) :=
  (hL.adjacent_iff c (Fin.last _) 0).mpr (Or.inr (Or.inr ⟨hc,Or.inl ⟨rfl,rfl⟩⟩))

lemma FreeLayout.Valid.no_cross {m r p : ℕ} {L : FreeLayout m r p} (hL : L.Valid)
    (s t : L.Position) (h : (freeGraph m r p).Adj (L.label s) (L.label t)) : s.1=t.1 :=
  ((hL.2 s t).mp h).1

/-- Literal physical indices supplied to the interval expression compiler. -/
def FreeLayout.vertex {m r p : ℕ} (L : FreeLayout m r p) (c : Fin L.count)
    (j : Fin (L.edges c+1)) : Fin (m-1) := (L.label ⟨c,j⟩).val

end SubmittedGenus.CapFourMass.ExecutableModes
