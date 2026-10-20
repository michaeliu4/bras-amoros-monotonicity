import Results.Genus.FixedPivot.SourcePrefix

/-! The original finite numerator and absolute signed correction norm bounds. -/
namespace SubmittedGenus.FixedPivot
open Polynomial WeightedSeries InverseCertificates
open scoped BigOperators
noncomputable section

def correctionFactor : PowerSeries ℝ := 1-PowerSeries.X-PowerSeries.X^2

lemma correctionFactor_summable : WeightedSummable q (fun n => PowerSeries.coeff n correctionFactor) := by
  have he : correctionFactor=((1-X-X^2 : Polynomial ℝ) : PowerSeries ℝ) := by simp [correctionFactor]
  rw [he]
  simpa only [Polynomial.coeff_coe] using polynomial_summable q (1-X-X^2)

lemma correctionFactor_norm : weightedNorm q (fun n => PowerSeries.coeff n correctionFactor)=2 := by
  have ha (n : ℕ) : |PowerSeries.coeff n correctionFactor|=|PowerSeries.coeff n K1| := by
    rw [K1_original]
    simp only [correctionFactor,map_sub,map_add,PowerSeries.coeff_one,PowerSeries.coeff_X,
      PowerSeries.coeff_X_pow]
    by_cases h0 : n=0 <;> by_cases h1 : n=1 <;> by_cases h2 : n=2 <;>
      simp [h0,h1,h2]
  have he : (fun n => absWeightedTerm q (fun j => PowerSeries.coeff j correctionFactor) n)=
      (fun n => absWeightedTerm q (fun j => PowerSeries.coeff j K1) n) := by
    funext n
    exact congrArg (fun x => x*q^n) (ha n)
  unfold weightedNorm
  rw [he]
  exact K1_norm

lemma correction_denominator_summable (d : ℕ) (hd : 0<d) :
    WeightedSummable q (fun n => PowerSeries.coeff n (sourceBSeries d*correctionFactor)) := by
  simp only [coeff_mul_eq_convolution]
  exact (sourceB_norm d hd).1.convolution correctionFactor_summable q_nonneg

lemma correction_denominator_norm (d : ℕ) (hd : 0<d) :
    weightedNorm q (fun n => PowerSeries.coeff n (sourceBSeries d*correctionFactor))≤20 := by
  simp only [coeff_mul_eq_convolution]
  have hh:=weightedNorm_convolution_le (sourceB_norm d hd).1 correctionFactor_summable q_nonneg
  rw [correctionFactor_norm] at hh
  linarith [(sourceB_norm d hd).2]

lemma sourceBSeries_constant {d : ℕ} (hd : 0<d) : PowerSeries.constantCoeff (sourceBSeries d)=1 := by
  rw [sourceBSeries,map_mul]
  have hK : PowerSeries.constantCoeff (sourceKSeries d)=1 := by
    unfold sourceKSeries
    split_ifs with he
    · exact K2_constant
    · exact K1_constant
  rw [hK,one_mul,sourceRSeries_eq]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,Polynomial.coeff_coe,Polynomial.coeff_zero_eq_eval_zero]
  unfold mixedDenominator
  rw [Polynomial.eval_mul,Polynomial.eval_prod]
  have hp : (∏ j∈Finset.range ((d-1)/2),Polynomial.eval (0 : ℝ) (mixedPair (X : Polynomial ℝ) d (j+1)))=1 := by
    apply Finset.prod_eq_one
    intro j _
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact mixedPair_constant hd (by omega)
  rw [hp,one_mul]
  split_ifs with he
  · have hd2 : 1≤d/2 := by have:=he.two_dvd; omega
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact central_constant hd2
  · simp

/-- The actual corrected source is the certified reciprocal times its finite numerator. -/
theorem correctedSeries_eq_numerator_inverse {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    correctedSeries r (r+d)=
      ((correctedNumerator r d hr hd).map (Rat.castHom ℝ) : PowerSeries ℝ)*(sourceBSeries d)⁻¹ := by
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by rw [sourceBSeries_constant hd]; norm_num)).2
  rw [mul_comm]
  exact fixedPivotSeries_real_corrected hr hd

/-- The original bound20 N B on the actual numerator uses only a finite prefix of F. -/
theorem correctedNumerator_norm_bound {r d : ℕ} (hr : 0<r) (hd : 0<d) (B : ℝ)
    (hB : ∀ m,r+d<m → sourceRawMass m r (r+d)≤B) :
    polynomialNorm q ((correctedNumerator r d hr hd).map (Rat.castHom ℝ))≤
      20*(3*d^2+7*(r+d)+6 : ℕ)*B := by
  let N:=3*d^2+7*(r+d)+6
  have he : (sourceBSeries d*correctionFactor)*fixedPivotSeriesReal r (r+d)=
      ((correctedNumerator r d hr hd).map (Rat.castHom ℝ) : PowerSeries ℝ) := by
    rw [mul_assoc]
    exact fixedPivotSeries_real_corrected hr hd
  have ht : ∀ n,N+1≤n → convolution
      (fun i => PowerSeries.coeff i (sourceBSeries d*correctionFactor))
      (fun i => PowerSeries.coeff i (fixedPivotSeriesReal r (r+d))) n=0 := by
    intro n hn
    rw [← coeff_mul_eq_convolution,he,Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt Polynomial.natDegree_map_le (lt_of_le_of_lt (correctedNumerator_natDegree hr hd) (by omega)))
  have hh:=finite_numerator_norm_le q_nonneg (correction_denominator_summable d hd) ht
  have hh' : polynomialNorm q ((correctedNumerator r d hr hd).map (Rat.castHom ℝ))≤
      weightedNorm q (fun i => PowerSeries.coeff i (sourceBSeries d*correctionFactor))*
        prefixNorm q (fun i => PowerSeries.coeff i (fixedPivotSeriesReal r (r+d))) (N+1) := by
    convert hh.2 using 1
    unfold polynomialNorm weightedNorm
    congr 1
    funext n
    unfold absWeightedTerm
    rw [← coeff_mul_eq_convolution,he,Polynomial.coeff_coe]
  calc
    _≤20*prefixNorm q (fun i => PowerSeries.coeff i (fixedPivotSeriesReal r (r+d))) (N+1) :=
      hh'.trans (mul_le_mul_of_nonneg_right (correction_denominator_norm d hd) (prefixNorm_nonneg q_nonneg _ _))
    _≤20*((N : ℝ)*B) := mul_le_mul_of_nonneg_left (fixedPivotSeriesReal_prefix_bound r (r+d) N B hB) (by norm_num)
    _=_ := by ring

/-- Original Lemma raw:signed, with the complete inverse tail and actual source numerator. -/
theorem correctedSeries_norm_bound {r d : ℕ} (hr : 0<r) (hd : 0<d) (B : ℝ)
    (hB : ∀ m,r+d<m → sourceRawMass m r (r+d)≤B) :
    WeightedSummable q (fun n => PowerSeries.coeff n (correctedSeries r (r+d))) ∧
      weightedNorm q (fun n => PowerSeries.coeff n (correctedSeries r (r+d)))≤
        420*(3*d^2+7*(r+d)+6 : ℕ)*B := by
  rw [correctedSeries_eq_numerator_inverse hr hd]
  simp only [coeff_mul_eq_convolution,Polynomial.coeff_coe]
  have hA:=polynomial_summable q ((correctedNumerator r d hr hd).map (Rat.castHom ℝ))
  obtain ⟨hi,hn⟩:=sourceB_inverse_norm d hd
  refine ⟨hA.convolution hi q_nonneg,?_⟩
  have hmul:=weightedNorm_convolution_le hA hi q_nonneg
  have hAN:=polynomialNorm_nonneg q_nonneg ((correctedNumerator r d hr hd).map (Rat.castHom ℝ))
  have hAB:=correctedNumerator_norm_bound hr hd B hB
  calc
    _≤polynomialNorm q ((correctedNumerator r d hr hd).map (Rat.castHom ℝ))*21 :=
      hmul.trans (mul_le_mul_of_nonneg_left hn.le hAN)
    _≤(20*(3*d^2+7*(r+d)+6 : ℕ)*B)*21 := mul_le_mul_of_nonneg_right hAB (by norm_num)
    _=_ := by push_cast; ring

end
end SubmittedGenus.FixedPivot
