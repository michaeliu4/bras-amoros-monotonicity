import Results.Genus.RawGraph
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Source-exact transfer along paths and cycles

This is the mathematical transfer recurrence used by the original submitted
`packed_relaxation.cpp` (blob 34048f88ee3d17e496d47c9c0fcd9c81bbc1a695).
A vertex contributes exactly one weight; unary loop restrictions belong in
that weight. Binary edges contribute compatibility factors only. A cycle
fixes its initial state and tests the closing edge against that same state.
No coefficient file or generator output is assumed correct.
-/

namespace SubmittedGenus.RawGraph.Transfer

open scoped BigOperators

variable {A R : Type*} [Fintype A] [CommSemiring R]

/-- Shift the indexed vertex weights or edge factors by one position. -/
def shift {B : Type*} (f : ℕ → B) : ℕ → B := fun i => f (i + 1)

/-- Direct physical-vertex source: one vertex factor per coordinate, one
compatibility factor per consecutive edge, and a terminal factor. -/
def sourceTerm (n : ℕ) (w : ℕ → A → R) (edge : ℕ → A → A → R)
    (finish : A → R) (x : Fin (n + 1) → A) : R :=
  (∏ i : Fin (n + 1), w i.val (x i)) *
    (∏ i : Fin n, edge i.val (x i.castSucc) (x i.succ)) * finish (x (Fin.last n))

/-- A path assignment with its first state fixed. -/
def fixedSource (n : ℕ) (w : ℕ → A → R) (edge : ℕ → A → A → R)
    (finish : A → R) (first : A) : R :=
  ∑ tail : Fin n → A, sourceTerm n w edge finish (Fin.cons first tail)

/-- Dynamic transfer, consuming one vertex weight at each recursive step. -/
def run : ℕ → (ℕ → A → R) → (ℕ → A → A → R) → (A → R) → A → R
  | 0, w, _, finish, first => w 0 first * finish first
  | n + 1, w, edge, finish, first =>
      w 0 first * ∑ next, edge 0 first next * run n (shift w) (shift edge) finish next

/-- Source sum for an open path, including the one-vertex, zero-edge case. -/
def pathSource (n : ℕ) (w : ℕ → A → R) (edge : ℕ → A → A → R) : R :=
  ∑ x : Fin (n + 1) → A, sourceTerm n w edge (fun _ => 1) x

/-- Transfer result for an open path. -/
def pathRun (n : ℕ) (w : ℕ → A → R) (edge : ℕ → A → A → R) : R :=
  ∑ first, run n w edge (fun _ => 1) first

/-- The closing compatibility uses the actual final and initial states. -/
def cycleSource (n : ℕ) (w : ℕ → A → R) (edge : ℕ → A → A → R)
    (close : A → A → R) : R :=
  ∑ x : Fin (n + 1) → A, sourceTerm n w edge (fun last => close last (x 0)) x

/-- Fix each initial state once, propagate, and close to that same state. -/
def cycleRun (n : ℕ) (w : ℕ → A → R) (edge : ℕ → A → A → R)
    (close : A → A → R) : R :=
  ∑ first, run n w edge (fun last => close last first) first

/-- Reindex all tuple assignments by their first state and remaining tuple. -/
theorem sum_cons (n : ℕ) (f : (Fin (n + 1) → A) → R) :
    (∑ x, f x) = ∑ first, ∑ tail : Fin n → A, f (Fin.cons first tail) := by
  classical
  calc
    (∑ x, f x) = ∑ y : A × (Fin n → A), f (Fin.cons y.1 y.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => A)).symm
        _ _ (fun _ => by simp)
    _ = _ := Fintype.sum_prod_type _

@[simp] theorem sourceTerm_zero (w : ℕ → A → R) (edge : ℕ → A → A → R)
    (finish : A → R) (x : Fin 1 → A) :
    sourceTerm 0 w edge finish x = w 0 (x 0) * finish (x 0) := by
  simp [sourceTerm]

theorem sourceTerm_cons (n : ℕ) (w : ℕ → A → R) (edge : ℕ → A → A → R)
    (finish : A → R) (first : A) (tail : Fin (n + 1) → A) :
    sourceTerm (n + 1) w edge finish (Fin.cons first tail) =
      w 0 first * edge 0 first (tail 0) * sourceTerm n (shift w) (shift edge) finish tail := by
  simp only [sourceTerm, Fin.prod_univ_succ, Fin.cons_zero, Fin.val_zero,
    Fin.cons_succ, Fin.val_succ, Fin.castSucc_zero, Fin.castSucc_succ,
    Fin.cons_last, shift]
  ring

/-- The transfer recurrence sums exactly the complete source, for any finite
state alphabet and any commutative-semiring weights. -/
theorem run_eq_fixedSource (n : ℕ) (w : ℕ → A → R) (edge : ℕ → A → A → R)
    (finish : A → R) (first : A) :
    run n w edge finish first = fixedSource n w edge finish first := by
  induction n generalizing w edge first with
  | zero => simp [run, fixedSource]
  | succ n ih =>
    simp only [run, fixedSource]
    rw [sum_cons]
    simp only [sourceTerm_cons, Fin.cons_zero]
    simp_rw [ih, fixedSource]
    simp only [Finset.mul_sum, mul_assoc]

/-- Exact open-path transfer, including isolated vertices and arbitrary unary
restrictions encoded in the vertex weights. -/
theorem pathRun_eq_source (n : ℕ) (w : ℕ → A → R) (edge : ℕ → A → A → R) :
    pathRun n w edge = pathSource n w edge := by
  simp only [pathRun, run_eq_fixedSource, fixedSource, pathSource]
  exact (sum_cons n _).symm

/-- Exact cycle transfer; no independent choice of the closing state is made. -/
theorem cycleRun_eq_source (n : ℕ) (w : ℕ → A → R) (edge : ℕ → A → A → R)
    (close : A → A → R) : cycleRun n w edge close = cycleSource n w edge close := by
  simp only [cycleRun, run_eq_fixedSource, fixedSource, cycleSource]
  rw [sum_cons]
  simp only [Fin.cons_zero]

/-- An isolated vertex is counted once, even if its unary domain arose from a loop. -/
theorem pathRun_zero (w : ℕ → A → R) (edge : ℕ → A → A → R) :
    pathRun 0 w edge = ∑ value, w 0 value := by
  simp [pathRun, run]

end SubmittedGenus.RawGraph.Transfer
