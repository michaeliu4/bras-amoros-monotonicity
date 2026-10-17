import Results.Genus.RawGraph.PackedAcceptance.AdjacencySummary
import Results.Genus.RawGraph.PackedAcceptance.ReflectionPPhaseShift
import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedPowerScalar

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open PairMonomialShift CompressedSignature SourceModel ReflectionFullLayout ReflectionPairedOrbit
open scoped Matrix

/-- Adjacent masks are retained separately, with the old odd bound as shift. -/
def pTransition {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (a b : Letter) :
    Matrix (Fin (cap+1)) (Fin (cap+1)) R :=
  shiftedPairMatrix z (letterPair cap a).2 (letterPair cap b).1

lemma cross_shifted_chain {R : Type*} [CommSemiring R]
    (cap : ℕ) (z : R) (first previous : Letter) (xs : List Letter) :
    shiftedWordMatrix z
      (crossPairs (letterPair cap first).1 (letterPair cap previous).2 (xs.map (letterPair cap))) =
      AdjacencySummary.chain (pTransition cap z) first previous xs := by
  induction xs generalizing previous with
  | nil => simp [crossPairs, shiftedWordMatrix, AdjacencySummary.chain, pTransition]
  | cons a xs ih =>
    change pTransition cap z previous a * shiftedWordMatrix z
      (crossPairs (letterPair cap first).1 (letterPair cap a).2 (xs.map (letterPair cap))) = _
    rw [ih]
    rfl

lemma pPhase_shifted_close {R : Type*} [CommSemiring R]
    (cap : ℕ) (z : R) (xs : List Letter) :
    shiftedWordMatrix z (pPhasePairs (xs.map (letterPair cap))) =
      AdjacencySummary.close (pTransition cap z) (AdjacencySummary.ofList (pTransition cap z) xs) := by
  rw [AdjacencySummary.close_ofList]
  cases xs with
  | nil => rfl
  | cons a xs => exact cross_shifted_chain cap z a a xs

/-- The existing source compiler runs in the endpoint-summary monoid.
Only one original-size matrix is carried; the final transition is added once. -/
def pProgramValue {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (L d q : ℕ) :
    Matrix (Fin (cap+1)) (Fin (cap+1)) R :=
  AdjacencySummary.close (pTransition cap z)
    ((sourceCompile L d q).evalTuple (AdjacencySummary.singleton (pTransition cap z)))

lemma normalized_p_residual_power {R : Type*} [CommSemiring R]
    (n d cap q : ℕ) (hd : 0<d) (hdL : d<n+2) (hq : q≤n+2-d) (z : R) :
    shiftedWordMatrix z (pPhasePairs (normalizedPairs n d cap q)) =
      pProgramValue cap z (n+2) d q := by
  unfold pProgramValue
  rw [SourceProgram.evalTuple_eq, sourceCompile_correct _ (n+2) d q hd hdL hq]
  rw [normalizedPairs_map]
  simpa only [List.map_map, Function.comp_def, AdjacencySummary.ofList] using
    pPhase_shifted_close cap z ((List.range (n+2)).map
      (fun k => reducedLetter (n+2) d q ((d*k)%(n+2))))

theorem normalized_p_scalar_power {R : Type*} [CommSemiring R]
    (n d cap q : ℕ) (hd : 0<d) (hdL : d<n+2) (hc : Nat.Coprime d (n+2))
    (hq : q≤n+2-d) (hcap : 1≤cap) (z : R) :
    signatureScalar (normalizedSignature n d cap q) z=
      z^((cap-1)*(n+2)+q+d)*Matrix.trace (pProgramValue cap z (n+2) d q) := by
  rw [normalized_pPhase_factor n d cap q hd hdL hc hq hcap,
    normalized_p_residual_power n d cap q hd hdL hq]

variable {g : ℕ} [NeZero g]

/-- Actual original layout component; this does not alter its physical phase. -/
theorem physical_p_scalar_power {R : Type*} [CommSemiring R]
    (n r p d cap : ℕ) (hr : 0<r) (hd : 0<d) (hc : Nat.Coprime d (n+2))
    (hp : p=r+g*d) (hp0 : 0<p) (hpm : p<g*(n+2)) (hcap : 1≤cap)
    (c : Fin (count (g:=g) r)) (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0) (z : R) :
    scalarComponent (layout n r p d hc hp hp0 hpm) r p cap z c=
      z^((cap-1)*(n+2)+cut g (representative r c).val r+d)*
        Matrix.trace (pProgramValue cap z (n+2) d (cut g (representative r c).val r)) := by
  rw [scalarComponent_eq_signature,
    physicalSignature_normalized n r p d cap hr hd hc hp hp0 hpm c hpair ha0]
  apply normalized_p_scalar_power n d cap _ hd _ hc _ hcap z
  · exact Nat.lt_of_mul_lt_mul_left (by omega : g*d<g*(n+2))
  · exact reduced_cut_bound g (n+2) r d (representative r c).val (NeZero.pos g) (by omega)

#print axioms normalized_p_residual_power
#print axioms physical_p_scalar_power
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
