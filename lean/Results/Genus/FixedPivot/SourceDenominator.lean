import Results.Genus.FixedPivot.DenominatorNorm
import Results.Genus.InverseCertificates

/-!
# The original submitted B_d denominator bounds

The integer R_d is identified with its actual mixed-factor product, and the
original K1/K2 degree80 reciprocal certificates are then applied. This file
proves the denominator bounds10 and21; it does not assume or claim the separate
all-phase cancellation theorem that places a raw fixed-pivot source over B_d.
-/
noncomputable section
set_option maxHeartbeats 800000
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
open WeightedSeries InverseCertificates
local notation "Xr" => (Polynomial.X : Polynomial ℝ)

/-- Real coefficient interpretation of the original integer polynomial R_d. -/
theorem sourceR_map (d : ℕ) :
    (sourceR d).map (Int.castRingHom ℝ) = mixedDenominator Xr d := by
  have hm := map_mixedDenominator (R := Polynomial ℤ) (S := Polynomial ℝ)
    (Polynomial.mapRingHom (Int.castRingHom ℝ)) (Polynomial.X : Polynomial ℤ) d
  change (sourceR d).map (Int.castRingHom ℝ) =
    mixedDenominator ((Polynomial.X : Polynomial ℤ).map (Int.castRingHom ℝ)) d at hm
  simpa only [Polynomial.map_X] using hm

/-- The manuscript's R_d as a full formal power series with its zero tail. -/
def sourceRSeries (d : ℕ) : PowerSeries ℝ := ((sourceR d).map (Int.castRingHom ℝ) : PowerSeries ℝ)

lemma sourceRSeries_eq (d : ℕ) : sourceRSeries d = ((mixedDenominator Xr d : Polynomial ℝ) : PowerSeries ℝ) := by
  rw [sourceRSeries,sourceR_map]

/-- K_tau with tau=2 precisely when the positive gap is even. -/
def sourceKSeries (d : ℕ) : PowerSeries ℝ := if Even d then K2 else K1

/-- Exactly B_d=K_tau R_d, with the original integer mixed polynomial. -/
def sourceBSeries (d : ℕ) : PowerSeries ℝ := sourceKSeries d*sourceRSeries d

lemma sourceRSeries_summable (d : ℕ) :
    WeightedSummable q (fun n => PowerSeries.coeff n (sourceRSeries d)) := by
  rw [sourceRSeries_eq]
  simpa only [Polynomial.coeff_coe] using polynomial_summable q (mixedDenominator Xr d)

lemma sourceRSeries_norm {d : ℕ} (hd : 0 < d) :
    weightedNorm q (fun n => PowerSeries.coeff n (sourceRSeries d)) < 10/3 := by
  rw [sourceRSeries_eq]
  simpa only [Polynomial.coeff_coe,polynomialNorm] using mixedDenominator_norm hd

lemma sourceRSeries_inverse {d : ℕ} (hd : 0 < d) :
    WeightedSummable q (fun n => PowerSeries.coeff n (sourceRSeries d)⁻¹) ∧
      weightedNorm q (fun n => PowerSeries.coeff n (sourceRSeries d)⁻¹) < 6 := by
  rw [sourceRSeries_eq]
  exact mixedDenominator_inverse_norm hd

lemma sourceKSeries_summable (d : ℕ) :
    WeightedSummable q (fun n => PowerSeries.coeff n (sourceKSeries d)) := by
  unfold sourceKSeries
  split_ifs
  · exact intSeries_summable k2Coeffs q
  · exact intSeries_summable k1Coeffs q

lemma sourceKSeries_norm (d : ℕ) :
    weightedNorm q (fun n => PowerSeries.coeff n (sourceKSeries d)) < 3 := by
  unfold sourceKSeries
  split_ifs
  · linarith [K2_norm_lt]
  · rw [K1_norm]
    norm_num

lemma sourceKSeries_inverse (d : ℕ) :
    WeightedSummable q (fun n => PowerSeries.coeff n (sourceKSeries d)⁻¹) ∧
      weightedNorm q (fun n => PowerSeries.coeff n (sourceKSeries d)⁻¹) < 7/2 := by
  unfold sourceKSeries
  split_ifs
  · exact K2_inverse_norm
  · exact K1_inverse_norm

/-- Original manuscript Lemma raw:wiener, direct denominator bound. -/
theorem sourceB_norm (d : ℕ) (hd : 0 < d) :
    WeightedSummable q (fun n => PowerSeries.coeff n (sourceBSeries d)) ∧
      weightedNorm q (fun n => PowerSeries.coeff n (sourceBSeries d)) < 10 := by
  have hsK := sourceKSeries_summable d
  have hsR := sourceRSeries_summable d
  have hnK := sourceKSeries_norm d
  have hnR := sourceRSeries_norm hd
  unfold sourceBSeries
  simp only [coeff_mul_eq_convolution]
  refine ⟨hsK.convolution hsR q_nonneg, ?_⟩
  calc
    _ ≤ weightedNorm q (fun n => PowerSeries.coeff n (sourceKSeries d))*
        weightedNorm q (fun n => PowerSeries.coeff n (sourceRSeries d)) :=
      weightedNorm_convolution_le hsK hsR q_nonneg
    _ < 3*(10/3) := mul_lt_mul_of_nonneg_of_pos hnK hnR.le
      (weightedNorm_nonneg q_nonneg _) (by norm_num)
    _ = 10 := by norm_num

/-- Original manuscript Lemma raw:wiener, complete inverse bound including its tail. -/
theorem sourceB_inverse_norm (d : ℕ) (hd : 0 < d) :
    WeightedSummable q (fun n => PowerSeries.coeff n (sourceBSeries d)⁻¹) ∧
      weightedNorm q (fun n => PowerSeries.coeff n (sourceBSeries d)⁻¹) < 21 := by
  obtain ⟨hsK,hnK⟩ := sourceKSeries_inverse d
  obtain ⟨hsR,hnR⟩ := sourceRSeries_inverse hd
  unfold sourceBSeries
  rw [PowerSeries.mul_inv_rev]
  simp only [coeff_mul_eq_convolution]
  refine ⟨hsR.convolution hsK q_nonneg, ?_⟩
  calc
    _ ≤ weightedNorm q (fun n => PowerSeries.coeff n (sourceRSeries d)⁻¹)*
        weightedNorm q (fun n => PowerSeries.coeff n (sourceKSeries d)⁻¹) :=
      weightedNorm_convolution_le hsR hsK q_nonneg
    _ < 6*(7/2) := mul_lt_mul_of_nonneg_of_pos hnR hnK.le
      (weightedNorm_nonneg q_nonneg _) (by norm_num)
    _ = 21 := by norm_num

end SubmittedGenus.FixedPivot
