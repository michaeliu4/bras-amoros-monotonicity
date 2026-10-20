import Results.Genus.RawGraph.PackedAcceptance.ReflectionNormalizedPairShift
import Results.Genus.RawGraph.PackedAcceptance.ReflectionNormalizedSharing
import Results.Genus.RawGraph.PackedAcceptance.ReflectionSourcePowerTuple
import Results.Genus.RawGraph.PackedAcceptance.ReflectionSourcePowerSummary

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open PairMonomialShift CompressedSignature SourceModel ReflectionFullLayout ReflectionPairedOrbit
open scoped Matrix

lemma ofFn_nat_map {A : Type*} (n : ℕ) (f : ℕ→A) :
    List.ofFn (fun k : Fin n=>f k.val)=(List.range n).map f := by
  simpa using List.ofFn_getElem_eq_map (List.range n) f

lemma normalizedPairs_map (n d cap q : ℕ) :
    normalizedPairs n d cap q=(List.range (n+2)).map
      (fun k=>letterPair cap (reducedLetter (n+2) d q ((d*k)%(n+2)))) :=
by
  simpa only [normalizedPairs] using ofFn_nat_map (n+2)
    (fun k=>letterPair cap (reducedLetter (n+2) d q ((d*k)%(n+2))))

lemma paired_step_product {M : Type*} [Monoid M] {k : ℕ}
    (f : Step k→M) (ps : List (Step k×Step k)) :
    ((pairSteps ps).map f).prod=(ps.map (fun p=>f p.1*f p.2)).prod := by
  induction ps with
  | nil=>simp [pairSteps]
  | cons p ps ih=>
    simp only [pairSteps] at ih ⊢
    simp [List.prod_append,mul_assoc,ih]

def pairLetterMatrix {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (q : Letter) :
    Matrix (Fin (cap+1)) (Fin (cap+1)) R :=
  stepMatrix z (letterPair cap q).1*stepMatrix z (letterPair cap q).2

def residualLetterMatrix {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (q : Letter) :
    Matrix (Fin (cap+1)) (Fin (cap+1)) R :=
  shiftedPairMatrix z (letterPair cap q).1 (letterPair cap q).2

/-- The accepted complete-word identity consumes terminal mask and actual
closing edge exactly once before the ordered power compiler is applied. -/
theorem normalized_scalar_power {R : Type*} [CommSemiring R]
    (n d cap q : ℕ) (hd : 0<d) (hdL : d<n+2) (hq : q≤n+2-d) (z : R) :
    signatureScalar (normalizedSignature n d cap q) z=
      Matrix.trace ((sourceCompile (n+2) d q).evalTuple (pairLetterMatrix cap z)) := by
  rw [cycle_signature_eq_trace _ rfl]
  have hw : ((sourceSteps (normalizedSignature n d cap q)).map (stepMatrix z)).prod*
      stepMatrix z (closingStep (normalizedSignature n d cap q))=
        ((pairSteps (normalizedPairs n d cap q)).map (stepMatrix z)).prod := by
    rw [←normalized_complete_word,List.map_append,List.prod_append]
    simp
  rw [hw,paired_step_product,normalizedPairs_map,List.map_map,
    SourceProgram.evalTuple_eq,sourceCompile_correct (pairLetterMatrix cap z) (n+2) d q hd hdL hq]
  simp only [List.map_map,Function.comp_def,pairLetterMatrix]

lemma normalized_residual_power {R : Type*} [CommSemiring R]
    (n d cap q : ℕ) (hd : 0<d) (hdL : d<n+2) (hq : q≤n+2-d) (z : R) :
    shiftedWordMatrix z (normalizedPairs n d cap q)=
      (sourceCompile (n+2) d q).evalTuple (residualLetterMatrix cap z) := by
  rw [SourceProgram.evalTuple_eq,sourceCompile_correct (residualLetterMatrix cap z) (n+2) d q hd hdL hq]
  simp only [shiftedWordMatrix,normalizedPairs_map,List.map_map,Function.comp_def,residualLetterMatrix]

theorem normalized_scalar_shifted_power {R : Type*} [CommSemiring R]
    (n d cap q : ℕ) (hd : 0<d) (hdL : d<n+2) (hc : Nat.Coprime d (n+2))
    (hq : q≤n+2-d) (hcap : 1≤cap) (z : R) :
    signatureScalar (normalizedSignature n d cap q) z=
      z^((cap-1)*(n+2)+q)*
        Matrix.trace ((sourceCompile (n+2) d q).evalTuple (residualLetterMatrix cap z)) := by
  rw [normalized_cycle_factor n d cap q hd hdL hc hq hcap,
    normalized_residual_power n d cap q hd hdL hq]

lemma sourceSummary_value_tuple {M : Type*} [Monoid M] (f : Letter→M)
    (L d q : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L-d) :
    (sourceSummary f L d q).value=(sourceCompile L d q).evalTuple f := by
  rw [SourceProgram.evalTuple_eq,sourceCompile_correct f L d q hd hdL hq]
  exact (sourceSummary_rep f L d q hd hdL hq).2.1

variable {g : ℕ} [NeZero g]

/-- Final original physical-component bridge, not only an arithmetic word
or a separately chosen canonical signature. -/
theorem physical_scalar_power {R : Type*} [CommSemiring R]
    (n r p d cap : ℕ) (hr : 0<r) (hd : 0<d) (hc : Nat.Coprime d (n+2))
    (hp : p=r+g*d) (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0) (z : R) :
    scalarComponent (layout n r p d hc hp hp0 hpm) r p cap z c=
      Matrix.trace ((sourceCompile (n+2) d (cut g (representative r c).val r)).evalTuple
        (pairLetterMatrix cap z)) := by
  rw [scalarComponent_eq_signature,
    physicalSignature_normalized n r p d cap hr hd hc hp hp0 hpm c hpair ha0]
  apply normalized_scalar_power n d cap _ hd _ _ z
  · exact Nat.lt_of_mul_lt_mul_left (by omega : g*d<g*(n+2))
  · exact reduced_cut_bound g (n+2) r d (representative r c).val (NeZero.pos g) (by omega)

theorem physical_scalar_shifted_power {R : Type*} [CommSemiring R]
    (n r p d cap : ℕ) (hr : 0<r) (hd : 0<d) (hc : Nat.Coprime d (n+2))
    (hp : p=r+g*d) (hp0 : 0<p) (hpm : p<g*(n+2)) (hcap : 1≤cap)
    (c : Fin (count (g:=g) r)) (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0) (z : R) :
    scalarComponent (layout n r p d hc hp hp0 hpm) r p cap z c=
      z^((cap-1)*(n+2)+cut g (representative r c).val r)*
        Matrix.trace ((sourceCompile (n+2) d (cut g (representative r c).val r)).evalTuple
          (residualLetterMatrix cap z)) := by
  rw [scalarComponent_eq_signature,
    physicalSignature_normalized n r p d cap hr hd hc hp hp0 hpm c hpair ha0]
  apply normalized_scalar_shifted_power n d cap _ hd _ hc _ hcap z
  · exact Nat.lt_of_mul_lt_mul_left (by omega : g*d<g*(n+2))
  · exact reduced_cut_bound g (n+2) r d (representative r c).val (NeZero.pos g) (by omega)

theorem physical_scalar_summary {R : Type*} [CommSemiring R]
    (n r p d cap : ℕ) (hr : 0<r) (hd : 0<d) (hc : Nat.Coprime d (n+2))
    (hp : p=r+g*d) (hp0 : 0<p) (hpm : p<g*(n+2)) (hcap : 1≤cap)
    (c : Fin (count (g:=g) r)) (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0) (z : R) :
    scalarComponent (layout n r p d hc hp hp0 hpm) r p cap z c=
      z^((cap-1)*(n+2)+cut g (representative r c).val r)*
        Matrix.trace (sourceSummary (residualLetterMatrix cap z)
          (n+2) d (cut g (representative r c).val r)).value := by
  rw [sourceSummary_value_tuple _ _ _ _ hd
    (Nat.lt_of_mul_lt_mul_left (by omega : g*d<g*(n+2)))
    (reduced_cut_bound g (n+2) r d (representative r c).val (NeZero.pos g) (by omega))]
  exact physical_scalar_shifted_power n r p d cap hr hd hc hp hp0 hpm hcap c hpair ha0 z

#print axioms normalized_scalar_power
#print axioms physical_scalar_power
#print axioms physical_scalar_shifted_power
#print axioms physical_scalar_summary
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
