import Results.Genus.RawGraph.PackedAcceptance.FastScalarList

/-! Pure natural-number modular rows, with one reduction per row entry.
The kernel accepts the equivalence to the original residue-ring transfer;
compiled or external evaluation is not a correctness premise. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.FastScalarList
open scoped BigOperators

/-- Natural arithmetic only: rows are materialized once and reduced modulo
`q`. A zero modulus is also semantically supported by the cast theorem. -/
def runMod {k : ℕ} (q : ℕ) : ℕ → (ℕ → Fin k → ℕ) →
    (ℕ → Fin k → Fin k → ℕ) → (Fin k → ℕ) → List ℕ
  | 0, w, _, finish => List.ofFn (fun i => (w 0 i * finish i) % q)
  | n + 1, w, edge, finish =>
    let tail := runMod q n (Transfer.shift w) (Transfer.shift edge) finish
    List.ofFn (fun i => (w 0 i * sum (fun j => edge 0 i j * lookup tail j)) % q)

theorem runMod_cast {k : ℕ} (q n : ℕ) (w : ℕ → Fin k → ℕ)
    (edge : ℕ → Fin k → Fin k → ℕ) (finish : Fin k → ℕ) (i : Fin k) :
    ((lookup (runMod q n w edge finish) i : ℕ) : ZMod q) =
      (Transfer.run n w edge finish i : ℕ) := by
  induction n generalizing w edge i with
  | zero => simp [runMod, Transfer.run, ZMod.natCast_mod]
  | succ n ih =>
    simp only [runMod, lookup_ofFn, ZMod.natCast_mod, Transfer.run,
      Nat.cast_mul, sum_eq, Nat.cast_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]

/-- A path consumes one vector for all initial states. -/
def pathMod {k : ℕ} (q n : ℕ) (w : ℕ → Fin k → ℕ)
    (edge : ℕ → Fin k → Fin k → ℕ) : ℕ :=
  let row := runMod q n w edge (fun _ => 1)
  sum (k := k) (lookup row) % q

/-- A cycle keeps the actual first state in each terminal gate. -/
def cycleMod {k : ℕ} (q n : ℕ) (w : ℕ → Fin k → ℕ)
    (edge : ℕ → Fin k → Fin k → ℕ) (close : Fin k → Fin k → ℕ) : ℕ :=
  sum (fun first => lookup (runMod q n w edge (fun last => close last first)) first) % q

theorem pathMod_cast {k : ℕ} (q n : ℕ) (w : ℕ → Fin k → ℕ)
    (edge : ℕ → Fin k → Fin k → ℕ) :
    (pathMod q n w edge : ZMod q) = (Transfer.pathRun n w edge : ℕ) := by
  simp [pathMod, ZMod.natCast_mod, sum_eq, Nat.cast_sum, runMod_cast, Transfer.pathRun]

theorem cycleMod_cast {k : ℕ} (q n : ℕ) (w : ℕ → Fin k → ℕ)
    (edge : ℕ → Fin k → Fin k → ℕ) (close : Fin k → Fin k → ℕ) :
    (cycleMod q n w edge close : ZMod q) = (Transfer.cycleRun n w edge close : ℕ) := by
  simp [cycleMod, ZMod.natCast_mod, sum_eq, Nat.cast_sum, runMod_cast, Transfer.cycleRun]

/-- Source-exact modular signature evaluation using only Nat/List/List. -/
def signatureMod {a : ℕ} (q : ℕ) (s : ComponentSignature a) (z : ℕ) : ℕ :=
  if s.cycle then cycleMod q s.edges (signatureVertices s z) (signatureEdges s)
    (fun last first => if s.close ≤ last.val + first.val then 1 else 0)
  else pathMod q s.edges (signatureVertices s z) (signatureEdges s)

theorem signature_natCast {a : ℕ} (q : ℕ) (s : ComponentSignature a) (z : ℕ) :
    ((signatureScalar s z : ℕ) : ZMod q) = signatureScalar s (z : ZMod q) := by
  let f := Nat.castRingHom (ZMod q)
  have hv : (fun j v => f (signatureVertices s z j v)) =
      signatureVertices s (z : ZMod q) := by
    funext j v
    simp only [signatureVertices]
    split_ifs <;> simp [f]
  have he : (fun j u v => f (signatureEdges (R := ℕ) s j u v)) =
      signatureEdges (R := ZMod q) s := by
    funext j u v
    simp only [signatureEdges]
    split_ifs <;> simp [f]
  change f (signatureScalar s z) = _
  unfold signatureScalar
  split_ifs
  · rw [map_cycleRun, hv, he]
    congr 1
    funext u v
    split_ifs <;> simp [f]
  · rw [map_pathRun, hv, he]

theorem signatureMod_cast {a : ℕ} (q : ℕ) (s : ComponentSignature a) (z : ℕ) :
    (signatureMod q s z : ZMod q) = signatureScalar s (z : ZMod q) := by
  rw [← signature_natCast]
  unfold signatureMod signatureScalar
  split_ifs
  · exact cycleMod_cast _ _ _ _ _
  · exact pathMod_cast _ _ _ _

/-- The final natural number is the canonical residue for positive modulus. -/
theorem signatureMod_lt {a : ℕ} (q : ℕ) (hq : 0 < q)
    (s : ComponentSignature a) (z : ℕ) : signatureMod q s z < q := by
  unfold signatureMod pathMod cycleMod
  split_ifs <;> exact Nat.mod_lt _ hq

theorem signatureMod_eq_val {a : ℕ} (q : ℕ) (hq : 0 < q)
    (s : ComponentSignature a) (z : ℕ) :
    signatureMod q s z = (signatureScalar s (z : ZMod q)).val := by
  rw [← signatureMod_cast, ZMod.val_natCast, Nat.mod_eq_of_lt (signatureMod_lt q hq s z)]

#print axioms runMod_cast
#print axioms signature_natCast
#print axioms signatureMod_cast
#print axioms signatureMod_lt
#print axioms signatureMod_eq_val
end SubmittedGenus.RawGraph.PackedAcceptance.FastScalarList
