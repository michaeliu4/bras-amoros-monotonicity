import Results.Genus.RawGraph.PackedAcceptance.ReflectionCachedBranchValues
import Results.Genus.RawGraph.PackedAcceptance.Checker

/-! Total source-exact cached direct-action evaluator for the original gcd-selected
raw layout, followed by the unchanged packed coefficient acceptance boundary. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCachedOriginal
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionCachedBranches Packing
open scoped BigOperators

/-- No branch witness, geometry certificate, or expanded source word is
supplied by a producer. Every original component is selected and cached. -/
def value {R : Type*} [CommSemiring R] (M r p cap : ℕ) (hrp : r<p) (hpm : p<M) (z : R) : R :=
  let C:=ReflectionOriginalLayout.coordinates M r p hrp hpm
  letI : NeZero C.g:=⟨ne_of_gt C.g_pos⟩
  ∏c:Fin (count (g:=C.g) r),componentValue C.n r p C.δ cap C.coprime C.gap C.pivot_pos C.pivot_lt c z

theorem value_eq_scalar {R : Type*} [CommSemiring R] (M r p cap : ℕ)
    (hr : 0<r) (hrp : r<p) (hpm : p<M) (z : R) :
    scalarLayout (ReflectionOriginalLayout.layout M r p hrp hpm) r p cap z=
      value M r p cap hrp hpm z := by
  let C:=ReflectionOriginalLayout.coordinates M r p hrp hpm
  letI : NeZero C.g:=⟨ne_of_gt C.g_pos⟩
  have hd : 0<C.δ := by
    by_contra hn
    have he : C.δ=0 := by omega
    have hp:=C.gap
    rw [he,Nat.mul_zero,Nat.add_zero] at hp
    omega
  change (∏c:Fin (count (g:=C.g) r),scalarComponent
    (ReflectionGcdParameters.transportLayout C.modulus
      (layout C.n r p C.δ C.coprime C.gap C.pivot_pos C.pivot_lt)) r p cap z c)=_
  apply Finset.prod_congr rfl
  intro c _
  rw [ReflectionZeroPaired.scalar_transport]
  exact componentValue_correct C.n r p C.δ cap hr hd C.coprime C.gap C.pivot_pos C.pivot_lt c z

/-- Complete original polynomial evaluation in any commutative semiring. -/
theorem original_eval {R : Type*} [CommSemiring R] {M r p cap : ℕ}
    (hp : Parameters M r p cap) (z : R) :
    Polynomial.eval₂ (Nat.castRingHom R) z (rawPolynomial M r p cap)=
      value M r p cap hp.2.1 hp.2.2.1 z := by
  rw [eval_raw_eq_scalar (ReflectionOriginalLayout.layout M r p hp.2.1 hp.2.2.1) hp
    (ReflectionOriginalLayout.covers M r p cap hp.2.1 hp.2.2.1)]
  exact value_eq_scalar M r p cap hp.1 hp.2.1 hp.2.2.1 z

/-- Original submitted packed base/modulus; only its exact numerical value
and coefficient digits remain for a finite producer to certify. -/
def residue (M r p cap H : ℕ) (hrp : r<p) (hpm : p<M) : ℕ :=
  (value M r p cap hrp hpm (digitBase H : ZMod (modulus H))).val

theorem residue_eq_eval {M r p cap : ℕ} (hp : Parameters M r p cap) (H : ℕ) :
    residue M r p cap H hp.2.1 hp.2.2.1=
      (rawPolynomial M r p cap).eval (digitBase H)%modulus H := by
  unfold residue
  rw [←original_eval hp,Polynomial.eval₂_at_natCast]
  exact ZMod.val_natCast _ _

def Accepts (M r p cap H : ℕ) (hrp : r<p) (hpm : p<M) (coeffs : Fin (H+1)→ℕ) : Prop :=
  residue M r p cap H hrp hpm=pack (digitBase H) coeffs ∧ ∀i,coeffs i<digitBase H
instance (M r p cap H : ℕ) (hrp : r<p) (hpm : p<M) (coeffs : Fin (H+1)→ℕ) :
    Decidable (Accepts M r p cap H hrp hpm coeffs) := by unfold Accepts;infer_instance

/-- Same exact original digit theorem, with all component-source semantics
discharged uniformly by the four-branch cached direct-action evaluator. -/
theorem accepted_coeff {M r p cap H : ℕ} (hp : Parameters M r p cap)
    (coeffs : Fin (H+1)→ℕ) (accepted : Accepts M r p cap H hp.2.1 hp.2.2.1 coeffs)
    (k : Fin (H+1)) : (rawPolynomial M r p cap).coeff k.val=coeffs k := by
  apply accepted_layout_coeff (ReflectionOriginalLayout.layout M r p hp.2.1 hp.2.2.1) hp
    (ReflectionOriginalLayout.covers M r p cap hp.2.1 hp.2.2.1) coeffs
  refine ⟨?_,accepted.2⟩
  rw [layoutResidue_eq_eval _ hp (ReflectionOriginalLayout.covers M r p cap hp.2.1 hp.2.2.1),
    ←residue_eq_eval hp H]
  exact accepted.1

#print axioms value_eq_scalar
#print axioms original_eval
#print axioms accepted_coeff
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCachedOriginal
