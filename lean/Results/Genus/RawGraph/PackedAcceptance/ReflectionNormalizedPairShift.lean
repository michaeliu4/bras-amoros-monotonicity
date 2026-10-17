import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairShiftCounts
import Results.Genus.RawGraph.PackedAcceptance.ReflectionNormalizedSignature
import Results.Genus.RawGraph.PackedAcceptance.PairMonomialWord

/-! The arbitrary coprime canonical source cycle has a compact exact
monomial shift. The actual terminal step is included without rotation. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift
open ReflectionThresholdWord ReflectionPairedOrbit CompressedSignature
open scoped BigOperators Matrix

def letterPair (cap : ℕ) (q : Letter) : Step (cap+1) × Step (cap+1) :=
  (⟨mask cap q,evenBound cap q⟩,⟨mask cap q,oddBound cap q⟩)

def normalizedPairs (n δ cap q : ℕ) : List (Step (cap+1) × Step (cap+1)) :=
  List.ofFn (fun k : Fin (n+2) => letterPair cap
    (reducedLetter (n+2) δ q ((δ*k.val)%(n+2))))

theorem normalized_complete_word (n δ cap q : ℕ) :
    sourceSteps (normalizedSignature n δ cap q) ++
      [closingStep (normalizedSignature n δ cap q)] =
      pairSteps (normalizedPairs n δ cap q) := by
  let f : ℕ → Step (cap+1) := fun j =>
    ⟨mask cap (reducedLetter (n+2) δ q ((δ*(j/2))%(n+2))),
      if j%2=0 then evenBound cap (reducedLetter (n+2) δ q ((δ*(j/2))%(n+2)))
      else oddBound cap (reducedLetter (n+2) δ q ((δ*(j/2))%(n+2)))⟩
  have hs : sourceSteps (normalizedSignature n δ cap q) =
      List.ofFn (fun j : Fin (2*(n+2)-1) => f j.val) := rfl
  have ht : closingStep (normalizedSignature n δ cap q) = f (2*(n+2)-1) := by
    have hdiv : (2*(n+2)-1)/2=n+1 := by omega
    have hmod : (2*(n+2)-1)%2=1 := by omega
    simp [closingStep, normalizedSignature, f, hdiv, hmod, Fin.last]
  have hf : List.ofFn (fun j : Fin ((2*(n+2)-1)+1) => f j.val) =
      List.ofFn (fun j : Fin (2*(n+2)-1) => f j.val) ++ [f (2*(n+2)-1)] := by
    rw [List.ofFn_succ_last]
    rfl
  rw [hs, ht, ← hf, List.ofFn_congr (show (2*(n+2)-1)+1=2*(n+2) by omega)]
  simp only [Fin.val_cast]
  rw [List.ofFn_mul']
  unfold pairSteps normalizedPairs
  rw [List.flatMap_def, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext k
  have h0 : (2*k.val)/2=k.val := by omega
  have h1 : (2*k.val+1)/2=k.val := by omega
  simp [List.ofFn_succ, f, letterPair, h0, h1]

lemma normalized_wordShift (n δ cap q : ℕ) :
    wordShift (normalizedPairs n δ cap q) = orbitShift (n+2) δ cap q := by
  simp only [wordShift, normalizedPairs, List.map_ofFn, List.sum_ofFn, letterPair, orbitShift, Function.comp_def]

theorem normalized_cycle_factor {R : Type*} [CommSemiring R]
    (n δ cap q : ℕ) (hδ : 0<δ) (hdL : δ<n+2)
    (hc : Nat.Coprime δ (n+2)) (hq : q≤n+2-δ) (hcap : 1≤cap) (z : R) :
    signatureScalar (normalizedSignature n δ cap q) z =
      z^((cap-1)*(n+2)+q) * Matrix.trace (shiftedWordMatrix z (normalizedPairs n δ cap q)) := by
  rw [cycle_word_factor _ rfl _ (normalized_complete_word n δ cap q),
    normalized_wordShift, paired_cycle_shift_count n δ cap q hδ hdL hc hq hcap]

variable {g : ℕ} [NeZero g]

/-- Exact original canonical source: no per-vertex source table is needed. -/
theorem canonical_cycle_factor {R : Type*} [CommSemiring R]
    (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ) (hcap : 1≤cap)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a) (z : R) :
    signatureScalar (canonicalSignature n r p δ cap hp hc a ha ha0 hpair) z =
      z^((cap-1)*(n+2)+cut g a.val r) *
        Matrix.trace (shiftedWordMatrix z (normalizedPairs n δ cap (cut g a.val r))) := by
  rw [canonicalSignature_normalized n r p δ cap hr hδ hp hpm hc a ha ha0 hpair]
  apply normalized_cycle_factor n δ cap (cut g a.val r) hδ _ hc _ hcap z
  · exact Nat.lt_of_mul_lt_mul_left (by omega : g*δ<g*(n+2))
  · exact reduced_cut_bound g (n+2) r δ a.val (NeZero.pos g) (by omega)

#print axioms normalized_complete_word
#print axioms normalized_cycle_factor
#print axioms canonical_cycle_factor
end SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift
