import Results.Genus.RawGraph.PackedAcceptance.FastScalar

/-!
# Source-exact finite-vector transfer

At each suffix this evaluator constructs one concrete finite list before
forming the preceding row. There is one recursive suffix call per step,
rather than one recursive call per possible next state. The proof is uniform
in the ordered signature, including masks, ordinary thresholds, and the
closing gate to the actual fixed first state.
-/
namespace SubmittedGenus.RawGraph.PackedAcceptance.FastScalarList
open scoped BigOperators

section Semiring
variable {R : Type*} [CommSemiring R] {k : ℕ}

/-- A list sum avoids the executable `Finset.univ` representation. -/
def sum (f : Fin k → R) : R := (List.ofFn f).sum

lemma sum_eq (f : Fin k → R) : sum f = ∑ i, f i := by
  simp [sum, List.sum_ofFn]

/-- Read a state from a materialized row. The fallback is unreachable for
rows constructed below; it keeps the evaluator free of dependent indexing. -/
def lookup (row : List R) (i : Fin k) : R := row[i.val]?.getD 0

@[simp] lemma lookup_ofFn (f : Fin k → R) (i : Fin k) :
    lookup (List.ofFn f) i = f i := by
  simp [lookup, i.isLt]

/-- A finite vector is computed once for each suffix. The terminal row
consumes its own vertex weight and the exact supplied final-state gate. -/
def run : ℕ → (ℕ → Fin k → R) → (ℕ → Fin k → Fin k → R) →
    (Fin k → R) → List R
  | 0, w, _, finish => List.ofFn (fun i => w 0 i * finish i)
  | n + 1, w, edge, finish =>
    let tail := run n (Transfer.shift w) (Transfer.shift edge) finish
    List.ofFn (fun i => w 0 i * sum (fun j => edge 0 i j * lookup tail j))

/-- Every state of the finite-vector recurrence equals the original
source-exact scalar transfer. This theorem has no restrictions on weights. -/
theorem run_eq (n : ℕ) (w : ℕ → Fin k → R) (edge : ℕ → Fin k → Fin k → R)
    (finish : Fin k → R) (i : Fin k) :
    lookup (run n w edge finish) i = Transfer.run n w edge finish i := by
  induction n generalizing w edge i with
  | zero => simp [run, Transfer.run]
  | succ n ih =>
    simp only [run, lookup_ofFn, Transfer.run, sum_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]

/-- Open paths share the complete suffix vector across all first states. -/
def path (n : ℕ) (w : ℕ → Fin k → R) (edge : ℕ → Fin k → Fin k → R) : R :=
  let row := run n w edge (fun _ => 1)
  sum (k := k) (lookup row)

/-- A cycle computes one vector per first state, with precisely that first
state used to test the terminal closing edge. -/
def cycle (n : ℕ) (w : ℕ → Fin k → R) (edge : ℕ → Fin k → Fin k → R)
    (close : Fin k → Fin k → R) : R :=
  sum (fun first => lookup (run n w edge (fun last => close last first)) first)

theorem path_eq (n : ℕ) (w : ℕ → Fin k → R) (edge : ℕ → Fin k → Fin k → R) :
    path n w edge = Transfer.pathRun n w edge := by
  simp [path, sum_eq, run_eq, Transfer.pathRun]

theorem cycle_eq (n : ℕ) (w : ℕ → Fin k → R) (edge : ℕ → Fin k → Fin k → R)
    (close : Fin k → Fin k → R) :
    cycle n w edge close = Transfer.cycleRun n w edge close := by
  simp [cycle, sum_eq, run_eq, Transfer.cycleRun]

/-- Direct executable replacement for the scalar signature evaluator. -/
def signature {a : ℕ} (s : ComponentSignature a) (z : R) : R :=
  if s.cycle then cycle s.edges (signatureVertices s z) (signatureEdges s)
    (fun last first => if s.close ≤ last.val + first.val then 1 else 0)
  else path s.edges (signatureVertices s z) (signatureEdges s)

/-- All source masks, ordinary thresholds and closing thresholds are kept;
no symmetry, normalization, or cache assertion is a premise. -/
theorem signature_eq {a : ℕ} (s : ComponentSignature a) (z : R) :
    signature s z = signatureScalar s z := by
  simp [signature, signatureScalar, path_eq, cycle_eq]

end Semiring

#print axioms run_eq
#print axioms path_eq
#print axioms cycle_eq
#print axioms signature_eq
end SubmittedGenus.RawGraph.PackedAcceptance.FastScalarList
