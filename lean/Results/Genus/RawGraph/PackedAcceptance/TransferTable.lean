import Results.Genus.RawGraph.PackedAcceptance.ScalarTransfer

namespace SubmittedGenus.RawGraph.PackedAcceptance
open scoped BigOperators

section Table
variable {A R : Type*} [Fintype A] [CommSemiring R]

/-- A supplied table records one state vector per physical suffix. Its
verification uses only local semiring operations, not recursive enumeration. -/
def TableValid (n : ℕ) (w : ℕ→A→R) (edge : ℕ→A→A→R) (finish : A→R)
    (table : Fin (n+1)→A→R) : Prop :=
  (∀a,table (Fin.last n) a=w n a*finish a) ∧
  ∀j:Fin n,∀a,table j.castSucc a=w j.val a*∑b,edge j.val a b*table j.succ b

instance [DecidableEq R] (n : ℕ) (w : ℕ→A→R) (edge : ℕ→A→A→R) (finish : A→R)
    (table : Fin (n+1)→A→R) : Decidable (TableValid n w edge finish table) := by
  unfold TableValid
  infer_instance

/-- Every locally accepted transfer table equals the source-exact transfer.
The terminal state, including a cycle's fixed initial endpoint, is checked. -/
theorem table_sound (n : ℕ) (w : ℕ→A→R) (edge : ℕ→A→A→R) (finish : A→R)
    (table : Fin (n+1)→A→R) (h : TableValid n w edge finish table) (a : A) :
    table 0 a=Transfer.run n w edge finish a := by
  induction n generalizing w edge a with
  | zero => exact h.1 a
  | succ n ih =>
    let tail : Fin (n+1)→A→R := fun j=>table j.succ
    have ht : TableValid n (Transfer.shift w) (Transfer.shift edge) finish tail := by
      constructor
      · intro b
        exact h.1 b
      · intro j b
        exact h.2 j.succ b
    have hs := h.2 (0:Fin (n+1)) a
    change table 0 a=w 0 a*∑b,edge 0 a b*tail 0 b at hs
    rw [hs,Transfer.run]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [ih _ _ tail ht b]

/-- The checked path output is the sum of the initial state vector. -/
theorem path_table_sound (n : ℕ) (w : ℕ→A→R) (edge : ℕ→A→A→R)
    (table : Fin (n+1)→A→R) (h : TableValid n w edge (fun _=>1) table) :
    (∑a,table 0 a)=Transfer.pathRun n w edge := by
  unfold Transfer.pathRun
  exact Finset.sum_congr rfl (fun a _=>table_sound n w edge _ table h a)

/-- A cycle certificate keeps a separate table for each fixed first state,
then uses that same state at the actual closing edge. -/
theorem cycle_table_sound (n : ℕ) (w : ℕ→A→R) (edge : ℕ→A→A→R) (close : A→A→R)
    (table : A→Fin (n+1)→A→R)
    (h : ∀first,TableValid n w edge (fun last=>close last first) (table first)) :
    (∑first,table first 0 first)=Transfer.cycleRun n w edge close := by
  unfold Transfer.cycleRun
  exact Finset.sum_congr rfl (fun a _=>table_sound n w edge _ (table a) (h a) a)
end Table

#print axioms table_sound
#print axioms path_table_sound
#print axioms cycle_table_sound
end SubmittedGenus.RawGraph.PackedAcceptance
