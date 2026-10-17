import Results.Genus.FixedPivot.PolynomialNorm
import Mathlib.Algebra.Polynomial.Eval.Coeff

noncomputable section
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
open WeightedSeries

/-- Absolute summability of the complete reciprocal formal series. -/
def PolynomialInverseSummable (q : ℝ) (p : Polynomial ℝ) : Prop :=
  WeightedSummable q (fun n => PowerSeries.coeff n (p : PowerSeries ℝ)⁻¹)

def polynomialInverseNorm (q : ℝ) (p : Polynomial ℝ) : ℝ :=
  weightedNorm q (fun n => PowerSeries.coeff n (p : PowerSeries ℝ)⁻¹)

lemma polynomialInverseNorm_nonneg {q : ℝ} (hq : 0 ≤ q) (p : Polynomial ℝ) :
    0 ≤ polynomialInverseNorm q p := weightedNorm_nonneg hq _

/-- The residual theorem is used with V=1, and includes every reciprocal coefficient. -/
theorem polynomial_inverse_of_residual {q a : ℝ} (hq : 0 ≤ q) (p : Polynomial ℝ)
    (hp : p.coeff 0 ≠ 0) (he : polynomialNorm q (1-p) ≤ a) (ha : a < 1) :
    PolynomialInverseSummable q p ∧ polynomialInverseNorm q p ≤ 1/(1-a) := by
  have hc : PowerSeries.constantCoeff (p : PowerSeries ℝ) ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff,Polynomial.coeff_coe] using hp
  have h1 : WeightedSummable q (fun n => PowerSeries.coeff n (1 : PowerSeries ℝ)) := by
    simpa only [← Polynomial.coe_one,Polynomial.coeff_coe] using polynomial_summable q (1 : Polynomial ℝ)
  have hseries : 1-(p : PowerSeries ℝ)*1 = ((1-p : Polynomial ℝ) : PowerSeries ℝ) := by
    simp only [mul_one,Polynomial.coe_sub,Polynomial.coe_one]
  have hE : WeightedSummable q (fun n => PowerSeries.coeff n (1-(p : PowerSeries ℝ)*1)) := by
    rw [hseries]
    simpa only [Polynomial.coeff_coe] using polynomial_summable q (1-p)
  have hnorm : weightedNorm q (fun n => PowerSeries.coeff n (1-(p : PowerSeries ℝ)*1)) =
      polynomialNorm q (1-p) := by
    rw [hseries]
    simp only [Polynomial.coeff_coe,polynomialNorm]
  have hnorm1 : weightedNorm q (fun n => PowerSeries.coeff n (1 : PowerSeries ℝ))=1 := by
    simpa only [← Polynomial.coe_one,Polynomial.coeff_coe,polynomialNorm]
      using polynomialNorm_one q
  obtain ⟨hs,hn⟩ := powerSeries_inverse_of_residual (p : PowerSeries ℝ) 1 hq hc h1 hE
    (by rw [hnorm]; exact he.trans_lt ha)
  refine ⟨hs, ?_⟩
  change polynomialInverseNorm q p ≤ _ at hn
  rw [hnorm,hnorm1] at hn
  exact hn.trans (one_div_le_one_div_of_le (sub_pos.mpr ha) (by linarith))

lemma polynomial_inverse_one : ((1 : PowerSeries ℝ)⁻¹)=1 := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).2
  simp

lemma polynomialInverseSummable_one (q : ℝ) : PolynomialInverseSummable q 1 := by
  unfold PolynomialInverseSummable
  rw [Polynomial.coe_one,polynomial_inverse_one]
  simpa only [← Polynomial.coe_one,Polynomial.coeff_coe] using polynomial_summable q (1 : Polynomial ℝ)

@[simp] lemma polynomialInverseNorm_one (q : ℝ) : polynomialInverseNorm q 1=1 := by
  unfold polynomialInverseNorm
  rw [Polynomial.coe_one,polynomial_inverse_one]
  simpa only [← Polynomial.coe_one,Polynomial.coeff_coe,polynomialNorm] using polynomialNorm_one q

lemma PolynomialInverseSummable.mul {q : ℝ} (hq : 0 ≤ q) {p t : Polynomial ℝ}
    (hp : PolynomialInverseSummable q p) (ht : PolynomialInverseSummable q t) :
    PolynomialInverseSummable q (p*t) := by
  unfold PolynomialInverseSummable at *
  simpa only [Polynomial.coe_mul,PowerSeries.mul_inv_rev,coeff_mul_eq_convolution]
    using ht.convolution hp hq

lemma polynomialInverseNorm_mul_le {q : ℝ} (hq : 0 ≤ q) {p t : Polynomial ℝ}
    (hp : PolynomialInverseSummable q p) (ht : PolynomialInverseSummable q t) :
    polynomialInverseNorm q (p*t) ≤ polynomialInverseNorm q p*polynomialInverseNorm q t := by
  unfold polynomialInverseNorm
  simp only [Polynomial.coe_mul,PowerSeries.mul_inv_rev,coeff_mul_eq_convolution]
  exact (weightedNorm_convolution_le ht hp hq).trans_eq (mul_comm _ _)

lemma PolynomialInverseSummable.prod {q : ℝ} (hq : 0 ≤ q) {ι : Type*}
    (s : Finset ι) (p : ι → Polynomial ℝ)
    (hp : ∀ i ∈ s, PolynomialInverseSummable q (p i)) :
    PolynomialInverseSummable q (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomialInverseSummable_one q
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul hq
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

lemma polynomialInverseNorm_prod_le {q : ℝ} (hq : 0 ≤ q) {ι : Type*}
    (s : Finset ι) (p : ι → Polynomial ℝ)
    (hp : ∀ i ∈ s, PolynomialInverseSummable q (p i)) :
    polynomialInverseNorm q (∏ i ∈ s, p i) ≤ ∏ i ∈ s, polynomialInverseNorm q (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    exact (polynomialInverseNorm_mul_le hq (hp i (Finset.mem_insert_self _ _))
      (PolynomialInverseSummable.prod hq s p hs)).trans
      (mul_le_mul_of_nonneg_left (ih hs) (polynomialInverseNorm_nonneg hq (p i)))

end SubmittedGenus.FixedPivot
