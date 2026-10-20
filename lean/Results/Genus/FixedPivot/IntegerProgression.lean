import Results.Genus.FixedPivot.PolynomialRationality
import Mathlib.Algebra.Polynomial.Reverse

/-! Integral source progression rationality and the literal monic characteristic
polynomial in Z[z,T] from the original submitted lemma. -/
namespace SubmittedGenus.FixedPivot
open Polynomial RawGraph
open scoped BigOperators
noncomputable section

abbrev integerPolynomialToRational : Polynomial ℤ →+* Polynomial ℚ :=
  Polynomial.mapRingHom (Int.castRingHom ℚ)

lemma integerPolynomialToRational_injective : Function.Injective integerPolynomialToRational :=
  Polynomial.map_injective _ Int.cast_injective

lemma sourceQ_map_rational (d : ℕ) :
    (sourceQ d).map integerPolynomialToRational=rationalSourceQ d := by
  rw [sourceQ,map_progressionPolynomial,rationalSourceQ]
  have hX : integerPolynomialToRational X=X := Polynomial.map_X _
  simp only [carryB,carryC,map_add,map_sub,map_neg,map_pow,hX]

lemma sourceQ_natDegree (d : ℕ) : (sourceQ d).natDegree≤d+1 := by
  rw [← Polynomial.natDegree_map_eq_of_injective integerPolynomialToRational_injective,
    sourceQ_map_rational]
  exact rationalSourceQ_natDegree d

/-- The actual raw partition polynomial with integer coefficients. -/
def rawPolynomialZ (m r p : ℕ) : Polynomial ℤ :=
  (rawPolynomial m r p 4).map (Nat.castRingHom ℤ)

lemma rawPolynomialZ_map (m r p : ℕ) :
    integerPolynomialToRational (rawPolynomialZ m r p)=rawPolynomialQ m r p := by
  change ((rawPolynomial m r p 4).map (Nat.castRingHom ℤ)).map (Int.castRingHom ℚ)=_
  rw [Polynomial.map_map]
  rfl

def integerProgressionSeries (r N d : ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk (fun k=>rawPolynomialZ (r+(N+k*d)) r (r+d))

lemma integerProgressionSeries_map (r N d : ℕ) :
    PowerSeries.map integerPolynomialToRational (integerProgressionSeries r N d)=
      polynomialProgressionSeries r N d := by
  apply PowerSeries.ext
  intro k
  simp only [PowerSeries.coeff_map,integerProgressionSeries,polynomialProgressionSeries,
    PowerSeries.coeff_mk,rawPolynomialZ_map]

/-- Descent uses injectivity of the integer-to-rational polynomial map and the
already source-derived identity; no recurrence assumption is introduced. -/
theorem integerProgressionSeries_coeff_zero {r N d : ℕ}
    (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : r+2*d<N) (n : ℕ) (hn : d<n) :
    PowerSeries.coeff n ((sourceQ d : PowerSeries (Polynomial ℤ))*integerProgressionSeries r N d)=0 := by
  apply integerPolynomialToRational_injective
  rw [map_zero,← PowerSeries.coeff_map,map_mul,← Polynomial.polynomial_map_coe,
    sourceQ_map_rational,integerProgressionSeries_map]
  exact polynomialProgressionSeries_coeff_zero hr hd hN hbig n hn

def integerProgressionNumerator (r N d : ℕ) : Polynomial (Polynomial ℤ) :=
  PowerSeries.trunc (d+1) ((sourceQ d : PowerSeries (Polynomial ℤ))*integerProgressionSeries r N d)

lemma integerProgressionNumerator_natDegree (r N d : ℕ) :
    (integerProgressionNumerator r N d).natDegree≤d :=
  Nat.le_of_lt_succ (PowerSeries.natDegree_trunc_lt _ _)

theorem integerProgressionSeries_rational {r N d : ℕ}
    (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : r+2*d<N) :
    (sourceQ d : PowerSeries (Polynomial ℤ))*integerProgressionSeries r N d=
      (integerProgressionNumerator r N d : PowerSeries (Polynomial ℤ)) := by
  apply PowerSeries.ext
  intro n
  rw [Polynomial.coeff_coe,integerProgressionNumerator,PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · exact integerProgressionSeries_coeff_zero hr hd hN hbig n (by omega)

/-- Literal original P_d(T,z), retaining all d+1 characteristic roots. -/
def sourceP (d : ℕ) : Polynomial (Polynomial ℤ) := (sourceQ d).reflect (d+1)

lemma sourceP_coeff (d j : ℕ) (hj : j≤d+1) :
    (sourceP d).coeff j=(sourceQ d).coeff (d+1-j) := by
  rw [sourceP,Polynomial.coeff_reflect,Polynomial.revAt_le hj]

lemma sourceP_natDegree_le (d : ℕ) : (sourceP d).natDegree≤d+1 := by
  apply Polynomial.natDegree_reflect_le.trans
  exact max_le (le_refl _) (sourceQ_natDegree d)


end
end SubmittedGenus.FixedPivot
