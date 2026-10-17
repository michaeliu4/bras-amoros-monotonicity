import Results.Genus.CapFourMass.IntervalTables
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Locally checked signed matrix-power tables. Matrix multiplication is
verified entry by entry from two supplied finite rows, not by expanding a
recursive arithmetic expression tree. -/
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.Interval
namespace MatrixTables

abbrev Boxes (n : ℕ) := Fin n→Fin n→Box

def Encloses {n : ℕ} (bs : Boxes n) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀i j,Contains (bs i j) (A i j)

def identity (n : ℕ) : Boxes n := fun i j=>if i=j then point 1 else point 0

def product {n : ℕ} (A B : Boxes n) : Boxes n :=
  fun i j=>sumBoxes (fun k=>mul (A i k) (B k j))

def action {n : ℕ} (A : Boxes n) (v : Fin n→Box) : Fin n→Box :=
  fun i=>sumBoxes (fun j=>mul (A i j) (v j))

def trace {n : ℕ} (A : Boxes n) : Box := sumBoxes (fun i=>A i i)

theorem identity_contains (n : ℕ) : Encloses (identity n) (1:Matrix (Fin n) (Fin n) ℝ) := by
  intro i j
  by_cases h:i=j
  · subst j
    simpa [identity,Matrix.one_apply] using point_contains 1
  · simpa [identity,Matrix.one_apply,h] using point_contains 0

theorem product_contains {n : ℕ} {ab bb : Boxes n} {A B : Matrix (Fin n) (Fin n) ℝ}
    (ha : Encloses ab A) (hb : Encloses bb B) : Encloses (product ab bb) (A*B) := by
  intro i j
  exact sumBoxes_contains (fun k=>mul_contains (ha i k) (hb k j))

theorem action_contains {n : ℕ} {ab : Boxes n} {A : Matrix (Fin n) (Fin n) ℝ}
    {vb : Fin n→Box} {v : Fin n→ℝ} (ha : Encloses ab A) (hv : ∀i,Contains (vb i) (v i)) :
    ∀i,Contains (action ab vb i) ((A*ᵥ v) i) := by
  intro i
  exact sumBoxes_contains (fun j=>mul_contains (ha i j) (hv j))

theorem trace_contains {n : ℕ} {ab : Boxes n} {A : Matrix (Fin n) (Fin n) ℝ}
    (ha : Encloses ab A) : Contains (trace ab) A.trace :=
  sumBoxes_contains (fun i=>ha i i)

/-- Only local finite arithmetic is checked; no equality of dependent function
fields is used by the decision procedure. -/
def PowerValid {n : ℕ} (N : ℕ) (A : Boxes n) (ts : Fin (N+1)→Boxes n) : Prop :=
  (∀i j,ts 0 i j=identity n i j) ∧
  ∀k : Fin N,∀i j,ts k.succ i j=product (ts k.castSucc) A i j

instance {n : ℕ} (N : ℕ) (A : Boxes n) (ts : Fin (N+1)→Boxes n) :
    Decidable (PowerValid N A ts) := by unfold PowerValid; infer_instance

/-- Every accepted cached power encloses the actual power of the supplied real matrix. -/
theorem powers_contain {n N : ℕ} {ab : Boxes n} {A : Matrix (Fin n) (Fin n) ℝ}
    (ha : Encloses ab A) (ts : Fin (N+1)→Boxes n) (ht : PowerValid N ab ts)
    (k : Fin (N+1)) : Encloses (ts k) (A^k.val) := by
  have hs : ∀j : ℕ,∀hj : j≤N,Encloses (ts ⟨j,by omega⟩) (A^j) := by
    intro j
    induction j with
    | zero =>
      intro hj i k
      rw [show (⟨0,by omega⟩:Fin (N+1))=0 from rfl,ht.1,pow_zero]
      exact identity_contains n i k
    | succ j ih =>
      intro hj i k
      have hlt : j<N := by omega
      have he:=ht.2 ⟨j,hlt⟩ i k
      change ts ⟨j+1,by omega⟩ i k=product (ts ⟨j,by omega⟩) ab i k at he
      rw [he,pow_succ]
      exact product_contains (ih (by omega)) ha i k
  exact hs k.val (by omega)

end MatrixTables
end SubmittedGenus.CapFourMass.Interval
