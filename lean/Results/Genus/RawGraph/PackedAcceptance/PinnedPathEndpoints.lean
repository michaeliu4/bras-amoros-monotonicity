import Results.Genus.RawGraph.PackedAcceptance.CompressedSignature

/-! Exact endpoint stripping for an ordered open path. The two cap-pinned
vertices contribute their weights once each; both incident gates are neutral.
The interior may be a single vertex (zero ordinary edges). -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.PinnedPathEndpoints
open CompressedSignature
open scoped BigOperators Matrix

/-- A cap-pinned source vertex followed by a neutral edge. -/
def pinStep (cap : ℕ) : Step (cap+1) :=
  ⟨fun v => decide (v = Fin.last cap), 0⟩

/-- The interior's last vertex, followed by a neutral edge to the final pin. -/
def openTerminalStep {cap : ℕ} (s : ComponentSignature cap) : Step (cap+1) :=
  ⟨s.mask (Fin.last s.edges), 0⟩

section Semiring
variable {R : Type*} [CommSemiring R] {cap : ℕ}

def capVector (z : R) : Fin (cap+1) → R :=
  fun v => if v = Fin.last cap then z^cap else 0

def openWeight (s : ComponentSignature cap) (z : R) : Fin (cap+1) → R :=
  fun v => if s.mask (Fin.last s.edges) v then z^v.val else 0

lemma terminal_open (s : ComponentSignature cap) (hs : s.cycle = false)
    (z : R) (first : Fin (cap+1)) :
    terminal s z first = openWeight s z := by
  funext last
  simp [terminal, hs, signatureVertices, openWeight, Fin.last]

lemma terminal_pinned (s : ComponentSignature cap) (hs : s.cycle = false)
    (hmask : ∀ v, s.mask (Fin.last s.edges) v = decide (v = Fin.last cap))
    (z : R) (first : Fin (cap+1)) :
    terminal s z first = capVector z := by
  rw [terminal_open s hs]
  funext v
  by_cases h : v = Fin.last cap
  · subst v; simp [openWeight, hmask, capVector]
  · simp [openWeight, hmask, capVector, h]

lemma openTerminal_mulVec (s : ComponentSignature cap) (z : R) :
    stepMatrix z (openTerminalStep s) *ᵥ capVector z =
      fun v => z^cap * openWeight s z v := by
  funext v
  simp [Matrix.mulVec, dotProduct, stepMatrix, openTerminalStep,
    capVector, openWeight, mul_comm]

lemma pin_sum_mulVec (z : R) (v : Fin (cap+1) → R) :
    (∑ first, (stepMatrix z (pinStep cap) *ᵥ v) first) =
      z^cap * ∑ i, v i := by
  simp [Matrix.mulVec, dotProduct, stepMatrix, pinStep, Finset.mul_sum]

lemma mulVec_const_mul (A : Matrix (Fin (cap+1)) (Fin (cap+1)) R)
    (c : R) (v : Fin (cap+1) → R) :
    A *ᵥ (fun i => c * v i) = fun i => c * (A *ᵥ v) i := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

lemma matrixValue_open (s : ComponentSignature cap) (hs : s.cycle = false)
    (z : R) (A : Matrix (Fin (cap+1)) (Fin (cap+1)) R) :
    matrixValue s z A = ∑ i, (A *ᵥ openWeight s z) i := by
  simp only [matrixValue, terminal_open s hs]

/-- Exact stripping from any matrix representation of the interior. -/
theorem pinned_matrixValue (outer inside : ComponentSignature cap)
    (ho : outer.cycle = false) (hi : inside.cycle = false)
    (hmask : ∀ v, outer.mask (Fin.last outer.edges) v = decide (v = Fin.last cap))
    (z : R) (A : Matrix (Fin (cap+1)) (Fin (cap+1)) R) :
    matrixValue outer z (stepMatrix z (pinStep cap) *
      (A * stepMatrix z (openTerminalStep inside))) =
      z^(2*cap) * matrixValue inside z A := by
  simp only [matrixValue, terminal_pinned outer ho hmask z,
    ← Matrix.mulVec_mulVec, openTerminal_mulVec, mulVec_const_mul]
  rw [← Finset.mul_sum, pin_sum_mulVec]
  simp only [terminal_open inside hi z]
  rw [← mul_assoc, ← pow_add]
  congr 2
  omega

/-- Ordered source-word contract. This also covers a one-vertex interior. -/
theorem strip_endpoints (outer inside : ComponentSignature cap)
    (ho : outer.cycle = false) (hi : inside.cycle = false)
    (hword : sourceSteps outer = [pinStep cap] ++ sourceSteps inside ++
      [openTerminalStep inside])
    (hmask : ∀ v, outer.mask (Fin.last outer.edges) v = decide (v = Fin.last cap))
    (z : R) :
    signatureScalar outer z = z^(2*cap) * signatureScalar inside z := by
  rw [← matrixValue_eq_signature outer, hword]
  simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one]
  rw [mul_assoc, pinned_matrixValue outer inside ho hi hmask,
    matrixValue_eq_signature]

#print axioms strip_endpoints
end Semiring
end SubmittedGenus.RawGraph.PackedAcceptance.PinnedPathEndpoints
