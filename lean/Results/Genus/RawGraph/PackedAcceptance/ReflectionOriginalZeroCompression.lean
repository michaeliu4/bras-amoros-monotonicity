import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedCompressed
import Results.Genus.RawGraph.PackedAcceptance.ReflectionOriginalLayout
import Results.Genus.RawGraph.PackedAcceptance.ReflectionShiftedSourceReuse

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
open SourceModel LayoutCompiler ReflectionPairedOrbit ReflectionFullLayout ReflectionThresholdWord
open scoped BigOperators Matrix

lemma scalar_transport {M m : ℕ} (hm : M=m) (L : Layout m)
    (r p cap : ℕ) {R : Type*} [CommSemiring R] (z : R) (c : Fin L.count) :
    scalarComponent (ReflectionGcdParameters.transportLayout hm L) r p cap z c=
      scalarComponent L r p cap z c := by
  subst M
  rfl

/-- The gcd-selected original layout has no extra factorization or geometry
premise. Only selection of its zero-paired component remains explicit. -/
theorem original_component_compressed {R : Type*} [CommSemiring R]
    (M r p cap : ℕ) (hr : 0<r) (hrp : r<p) (hpm : p<M) (z : R) :
    let C:=ReflectionOriginalLayout.coordinates M r p hrp hpm
    letI : NeZero C.g:=⟨ne_of_gt C.g_pos⟩
    ∀c:Fin (count (g:=C.g) r),representative r c=0 → (0:Fin C.g)≠mate r 0 →
      scalarComponent (ReflectionOriginalLayout.layout M r p hrp hpm) r p cap z c=
        z^(2*cap)*compressedFreeValue C.n C.δ cap (cut C.g 0 r) z := by
  let C:=ReflectionOriginalLayout.coordinates M r p hrp hpm
  letI : NeZero C.g:=⟨ne_of_gt C.g_pos⟩
  dsimp only
  intro c hz hpair
  have hd : 0<C.δ := by
    by_contra hn
    have he : C.δ=0 := by omega
    have hp:=C.gap
    rw [he,Nat.mul_zero,Nat.add_zero] at hp
    omega
  change scalarComponent (ReflectionGcdParameters.transportLayout C.modulus
    (layout C.n r p C.δ C.coprime C.gap C.pivot_pos C.pivot_lt)) r p cap z c=_
  rw [scalar_transport]
  exact scalarComponent_compressed C.n r p C.δ cap hr hd C.coprime C.gap
    C.pivot_pos C.pivot_lt c hz hpair z

/-- Explicit summary reuse avoids the unused doubled whole-word square. -/
def cachedFreeValue {R : Type*} [CommSemiring R]
    (n δ cap q : ℕ) (z : R) : R :=
  let s:=sourceSummary (letterMatrix cap z) (n+2) δ q
  ∑first,∑last,(s.cyclicSlice 1 n) first last *
    (if mask cap .carryCarry last then z^last.val else 0)

theorem cachedFreeValue_eq {R : Type*} [CommSemiring R]
    (n δ cap q : ℕ) (hδ : 0<δ) (hdL : δ<n+2) (hq : q≤n+2-δ) (z : R) :
    cachedFreeValue n δ cap q z=compressedFreeValue n δ cap q z := by
  dsimp only [cachedFreeValue,compressedFreeValue]
  rw [sourceSummary_cyclicSlice_eq (letterMatrix cap z) (n+2) δ q 1 n hδ hdL hq (by omega) (by omega)]

#print axioms scalar_transport
#print axioms original_component_compressed
#print axioms cachedFreeValue_eq
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
