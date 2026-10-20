import Results.Genus.RawGraph.PackedAcceptance.ReflectionPPhaseDense

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open MaterializedMatrixMonoid AdjacencySummary

/-- Explicit three-letter storage, rather than a recomputed matrix closure. -/
structure LetterTable (M : Type*) where
  a : M
  b : M
  c : M

def LetterTable.lookup {M : Type*} (t : LetterTable M) : Letter → M
  | .fullStrong => t.a
  | .carryCarry => t.b
  | .carryStrong => t.c

def LetterTable.ofFn {M : Type*} (f : Letter → M) : LetterTable M :=
  ⟨f .fullStrong,f .carryCarry,f .carryStrong⟩

@[simp] lemma LetterTable.lookup_ofFn {M : Type*} (f : Letter → M) :
    (LetterTable.ofFn f).lookup = f := by funext a; cases a <;> rfl

def densePCachedValue {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (L d q : ℕ) : Dense (cap+1) R :=
  let t := LetterTable.ofFn (fun a => LetterTable.ofFn (densePTransition cap z a))
  let transition := fun a b => (t.lookup a).lookup b
  close transition ((sourceCompile L d q).evalTuple (singleton transition))

theorem dense_p_cached_eq {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (L d q : ℕ) :
    densePCachedValue cap z L d q = densePProgramValue cap z L d q := by
  have ht : (fun a b => ((LetterTable.ofFn (fun a =>
      LetterTable.ofFn (densePTransition cap z a))).lookup a).lookup b) =
      densePTransition cap z := by
    funext a b
    cases a <;> cases b <;> rfl
  unfold densePCachedValue
  dsimp only
  rw [ht]
  rfl

def denseEvenCachedValue {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (L d q : ℕ) : Dense (cap+1) R :=
  let t := LetterTable.ofFn (fun a => ofMatrix (residualLetterMatrix cap z a))
  (sourceCompile L d q).evalTuple t.lookup

lemma dense_even_cached_eq {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (L d q : ℕ)
    (hd : 0<d) (hdL : d<L) (hq : q≤L-d) :
    toMatrix (denseEvenCachedValue cap z L d q) =
      (sourceCompile L d q).evalTuple (residualLetterMatrix cap z) := by
  simp only [denseEvenCachedValue, LetterTable.lookup_ofFn]
  rw [SourceProgram.evalTuple_eq, SourceProgram.evalTuple_eq,
    sourceCompile_correct _ L d q hd hdL hq, sourceCompile_correct _ L d q hd hdL hq,
    toMatrix_prod, List.map_map]
  simp only [Function.comp_def, toMatrix_ofMatrix]

#print axioms dense_p_cached_eq
#print axioms dense_even_cached_eq
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
