import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedMatrix
import Results.Genus.RawGraph.PackedAcceptance.ReflectionShiftedSourceSummary

/-! Original zero-paired components use an exact phase-one subword of the
Euclidean power summary. Both pivot factors and the unpaired terminal remain. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
open SourceModel LayoutCompiler ReflectionPairedOrbit ReflectionFullLayout ReflectionThresholdWord CompressedSignature
open scoped BigOperators Matrix
variable {g : ℕ} [NeZero g]

lemma ofFn_nat_map {A : Type*} (n : ℕ) (f : ℕ→A) :
    List.ofFn (fun j:Fin n=>f j.val)=(List.range n).map f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Function.comp_def]
    congr 1
    exact ih (fun j=>f (j+1))

theorem free_program_product {R : Type*} [CommSemiring R]
    (n r p δ cap : ℕ) (hδ : 0<δ) (hp : p=r+g*δ) (hpm : p<g*(n+2)) (z : R) :
    shiftedSourceValue (letterMatrix cap z) (n+2) δ (cut g 0 r) 1 n=
      (List.ofFn (fun j:Fin n=>letterMatrix cap z
        (letter (g*(n+2)) r (g*δ) (g*((δ*(j.val+1))%(n+2)))))).prod := by
  have hdL : δ<n+2 := Nat.lt_of_mul_lt_mul_left (by omega : g*δ<g*(n+2))
  rw [shiftedSourceValue_eq _ _ _ _ _ _ hδ hdL
    (reduced_cut_bound g (n+2) r δ 0 (NeZero.pos g) (by omega)) (by omega) (by omega)]
  rw [ofFn_nat_map n (fun k=>letterMatrix cap z
    (letter (g*(n+2)) r (g*δ) (g*((δ*(k+1))%(n+2)))))]
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro k _
  rw [Nat.add_comm 1 k]
  apply congrArg (letterMatrix cap z)
  simpa only [zero_add,reducedLetter] using
    (affine_letter_reduced g (n+2) r δ 0 ((δ*(k+1))%(n+2)) (NeZero.pos g) (NeZero.pos g)).symm

/-- Canonical zero-paired free evaluator depends only on normalized keys.
It does not contain raw labels or expand the n source pair letters. -/
def compressedFreeValue {R : Type*} [CommSemiring R]
    (n δ cap q : ℕ) (z : R) : R :=
  ∑first,∑last,(shiftedSourceValue (letterMatrix cap z) (n+2) δ q 1 n) first last *
    (if mask cap .carryCarry last then z^last.val else 0)

theorem free_scalar_compressed {R : Type*} [CommSemiring R]
    (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (z : R) :
    signatureScalar (freeSignature n r p δ cap hp hc hpair) z=
      compressedFreeValue n δ cap (cut g 0 r) z := by
  rw [←free_matrix_value n r p δ cap hr hδ hp hpm hc hpair z,
    ←free_program_product n r p δ cap hδ hp hpm z,
    free_matrix_value_explicit n r p δ cap hδ hp hpm hc hpair z]
  rfl

theorem scalarComponent_compressed {R : Type*} [CommSemiring R]
    (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hz : representative r c=0) (hpair : (0:Fin g)≠mate r 0) (z : R) :
    scalarComponent (layout n r p δ hc hp hp0 hpm) r p cap z c=
      z^(2*cap)*compressedFreeValue n δ cap (cut g 0 r) z := by
  rw [scalarComponent_eq_pinned_free n r p δ cap hc hp hp0 hpm c hz hpair z,
    free_scalar_compressed n r p δ cap hr hδ hp hpm hc hpair z]

#print axioms ofFn_nat_map
#print axioms free_program_product
#print axioms free_scalar_compressed
#print axioms scalarComponent_compressed
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
