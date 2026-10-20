import Results.Genus.FixedPivot.SourceAlgebra
import Mathlib.RingTheory.PowerSeries.Trunc

/-! Descent of the actual progression identity to rational polynomial coefficients. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators
noncomputable section

lemma map_progressionPair {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (b c : R) (d j : ℕ) :
    (progressionPair b c d j).map f=progressionPair (f b) (f c) d j := by
  simp only [progressionPair,Polynomial.map_add,Polynomial.map_sub,Polynomial.map_one,
    Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X]
  rw [map_mul,map_pow,map_traceSum,map_pow]

lemma map_progressionPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (b c : R) (d : ℕ) :
    (progressionPolynomial b c d).map f=progressionPolynomial (f b) (f c) d := by
  classical
  unfold progressionPolynomial
  rw [Polynomial.map_mul]
  congr 1
  · change (Polynomial.mapRingHom f) (∏ j∈Finset.range ((d+1)/2),progressionPair b c d j)=_
    rw [map_prod]
    exact Finset.prod_congr rfl (fun j _ => map_progressionPair f b c d j)
  · split_ifs <;> simp only [Polynomial.map_sub,Polynomial.map_one,Polynomial.map_mul,
      Polynomial.map_C,Polynomial.map_X]
    simp only [map_pow]

def polynomialProgressionSeries (r N d : ℕ) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk (fun k => rawPolynomialQ (r+(N+k*d)) r (r+d))

lemma polynomialProgressionSeries_map (r N d : ℕ) :
    PowerSeries.map sourceEmbedding (polynomialProgressionSeries r N d)=
      sourceProgressionSeries (r := r) (N := N) (d := d) sourceZ := by
  apply PowerSeries.ext
  intro k
  simp only [PowerSeries.coeff_map,polynomialProgressionSeries,sourceProgressionSeries,
    PowerSeries.coeff_mk,source_rawPolynomialQ]

lemma rationalSourceQ_map (d : ℕ) :
    (rationalSourceQ d).map sourceEmbedding=progressionPolynomial (carryB sourceZ) (carryC sourceZ) d := by
  rw [rationalSourceQ,map_progressionPolynomial]
  simp only [carryB,carryC,map_add,map_sub,map_neg,map_pow]
  rfl

/-- The polynomial coefficient tail vanishes because the actual source identity
holds in an explicitly constructed injective quadratic localization. -/
theorem polynomialProgressionSeries_coeff_zero {r N d : ℕ}
    (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : r+2*d<N) (n : ℕ) (hn : d<n) :
    PowerSeries.coeff n ((rationalSourceQ d : PowerSeries (Polynomial ℚ))*
      polynomialProgressionSeries r N d)=0 := by
  obtain ⟨A,hdeg,hA⟩:=sourceProgressionSeries_rational hr hd hN hbig
    sourceZ sourceLambda sourceMu sourceLambdaInverse sourceMuInverse sourceDifferenceInverse
    source_roots_sum source_roots_product source_lambda_inverse source_mu_inverse source_difference_inverse
  apply sourceEmbedding_injective
  rw [map_zero,← PowerSeries.coeff_map]
  rw [map_mul,← Polynomial.polynomial_map_coe,rationalSourceQ_map,polynomialProgressionSeries_map,hA]
  simp only [Polynomial.coeff_coe]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hn)

def polynomialProgressionNumerator (r N d : ℕ) : Polynomial (Polynomial ℚ) :=
  PowerSeries.trunc (d+1) ((rationalSourceQ d : PowerSeries (Polynomial ℚ))*
    polynomialProgressionSeries r N d)

lemma polynomialProgressionNumerator_natDegree (r N d : ℕ) :
    (polynomialProgressionNumerator r N d).natDegree≤d :=
  Nat.le_of_lt_succ (PowerSeries.natDegree_trunc_lt _ _)

/-- Original source progression rationality over Q[z], with no recurrence premise. -/
theorem polynomialProgressionSeries_rational {r N d : ℕ}
    (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : r+2*d<N) :
    (rationalSourceQ d : PowerSeries (Polynomial ℚ))*polynomialProgressionSeries r N d=
      (polynomialProgressionNumerator r N d : PowerSeries (Polynomial ℚ)) := by
  apply PowerSeries.ext
  intro n
  rw [Polynomial.coeff_coe,polynomialProgressionNumerator,PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · exact polynomialProgressionSeries_coeff_zero hr hd hN hbig n (by omega)

lemma polynomialProgressionNumerator_eval_one (r N d : ℕ) :
    Polynomial.eval (1 : Polynomial ℚ) (polynomialProgressionNumerator r N d)=
      ∑ k∈Finset.range (d+1),∑ j∈Finset.range (k+1),
        (rationalSourceQ d).coeff j*rawPolynomialQ (r+(N+(k-j)*d)) r (r+d) := by
  change (PowerSeries.trunc (d+1) _).eval₂ (RingHom.id _) 1=_
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp only [RingHom.id_apply,one_pow,mul_one]
  apply Finset.sum_congr rfl
  intro k _
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe,polynomialProgressionSeries,PowerSeries.coeff_mk]

end
end SubmittedGenus.FixedPivot
