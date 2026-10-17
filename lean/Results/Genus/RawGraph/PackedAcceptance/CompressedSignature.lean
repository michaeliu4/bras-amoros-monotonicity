import Results.Genus.RawGraph.PackedAcceptance.FastScalarListNat
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Exact matrix-word compression of ordered physical component signatures.
The last vertex weight and cycle closure to the actual first state remain
separate from the ordinary-edge word. Repetition is represented by powers. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.CompressedSignature
open scoped BigOperators Matrix

structure Step (k : ℕ) where
  mask : Fin k → Bool
  bound : ℕ
  deriving DecidableEq

section Semiring
variable {R : Type*} [CommSemiring R] {k : ℕ}

def stepMatrix (z : R) (s : Step k) : Matrix (Fin k) (Fin k) R :=
  fun i j => if s.mask i then if s.bound ≤ i.val+j.val then z^i.val else 0 else 0

def factorList : ℕ → (ℕ → Fin k → R) → (ℕ → Fin k → Fin k → R) →
    List (Matrix (Fin k) (Fin k) R)
  | 0, _, _ => []
  | n+1, w, e => (fun i j => w 0 i * e 0 i j) ::
      factorList n (Transfer.shift w) (Transfer.shift e)

lemma factorList_eq_ofFn (n : ℕ) (w : ℕ → Fin k → R)
    (e : ℕ → Fin k → Fin k → R) :
    factorList n w e = List.ofFn (fun j : Fin n => fun i l => w j.val i * e j.val i l) := by
  induction n generalizing w e with
  | zero => simp [factorList]; rfl
  | succ n ih => simp only [factorList, List.ofFn_succ, ih]; rfl

lemma factorList_run (n : ℕ) (w : ℕ → Fin k → R)
    (e : ℕ → Fin k → Fin k → R) (finish : Fin k → R) :
    (factorList n w e).prod *ᵥ (fun i => w n i * finish i) =
      Transfer.run n w e finish := by
  induction n generalizing w e with
  | zero => simp [factorList, Transfer.run]
  | succ n ih =>
    simp only [factorList, List.prod_cons, ← Matrix.mulVec_mulVec]
    change (fun i j => w 0 i * e 0 i j) *ᵥ
      ((factorList n (Transfer.shift w) (Transfer.shift e)).prod *ᵥ
        (fun i => Transfer.shift w n i * finish i)) = _
    rw [ih]
    funext i
    simp only [Matrix.mulVec, dotProduct, Transfer.run, Finset.mul_sum, mul_assoc]

/-- An arbitrary repeated word is one exact matrix power. -/
lemma repeat_word_product (word : List (Step k)) (n : ℕ) (z : R) :
    ((List.replicate n word).flatten.map (stepMatrix z)).prod =
      (word.map (stepMatrix z)).prod ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.map_append, pow_succ', List.prod_append]

def sourceSteps {a : ℕ} (s : ComponentSignature a) : List (Step (a+1)) :=
  List.ofFn (fun j : Fin s.edges => ⟨s.mask j.castSucc, s.bound j⟩)

lemma sourceSteps_matrices {a : ℕ} (s : ComponentSignature a) (z : R) :
    ((sourceSteps s).map (stepMatrix z)) =
      factorList s.edges (signatureVertices s z) (signatureEdges s) := by
  rw [sourceSteps, List.map_ofFn, factorList_eq_ofFn]
  congr 1
  funext j i l
  change (if s.mask j.castSucc i then if s.bound j ≤ i.val+l.val then z^i.val else 0 else 0) = _
  simp only [signatureVertices, signatureEdges, j.isLt, show j.val < s.edges+1 by omega, ↓reduceDIte]
  change (if s.mask j.castSucc i then if s.bound j ≤ i.val+l.val then z^i.val else 0 else 0) =
    (if s.mask j.castSucc i then z^i.val else 0) * (if s.bound j ≤ i.val+l.val then 1 else 0)
  split_ifs <;> simp

/-- The final vertex and the actual-first cycle gate are never compressed away. -/
def terminal {a : ℕ} (s : ComponentSignature a) (z : R) (first last : Fin (a+1)) : R :=
  signatureVertices s z s.edges last *
    (if s.cycle then if s.close ≤ last.val+first.val then 1 else 0 else 1)

def matrixValue {a : ℕ} (s : ComponentSignature a) (z : R)
    (A : Matrix (Fin (a+1)) (Fin (a+1)) R) : R :=
  ∑ first, (A *ᵥ terminal s z first) first

/-- Exact source semantics for a matrix factorization of the complete word. -/
theorem matrixValue_eq_signature {a : ℕ} (s : ComponentSignature a) (z : R) :
    matrixValue s z (((sourceSteps s).map (stepMatrix z)).prod) = signatureScalar s z := by
  rw [sourceSteps_matrices]
  unfold matrixValue terminal signatureScalar
  split_ifs with hc
  · simp only [factorList_run, Transfer.cycleRun]
  · simp only [factorList_run, Transfer.pathRun]

/-- A finite word cache may be reused, provided its concatenation is exactly
this ordered source word. No rotation, reversal, or mask deletion is allowed. -/
theorem cached_word_product {κ : Type*} (words : κ → List (Step k)) (keys : List κ)
    (cache : κ → Matrix (Fin k) (Fin k) R) (z : R)
    (hcache : ∀ i, cache i = ((words i).map (stepMatrix z)).prod) :
    (keys.map cache).prod = ((keys.flatMap words).map (stepMatrix z)).prod := by
  induction keys with
  | nil => simp
  | cons i keys ih => simp only [List.map_cons, List.prod_cons, hcache, ih,
      List.flatMap_cons, List.map_append, List.prod_append]

theorem cached_signature_eq {a : ℕ} {κ : Type*}
    (s : ComponentSignature a) (words : κ → List (Step (a+1))) (keys : List κ)
    (cache : κ → Matrix (Fin (a+1)) (Fin (a+1)) R) (z : R)
    (hcache : ∀ i, cache i = ((words i).map (stepMatrix z)).prod)
    (hsource : keys.flatMap words = sourceSteps s) :
    matrixValue s z ((keys.map cache).prod) = signatureScalar s z := by
  rw [cached_word_product words keys cache z hcache, hsource, matrixValue_eq_signature]
end Semiring
end SubmittedGenus.RawGraph.PackedAcceptance.CompressedSignature
