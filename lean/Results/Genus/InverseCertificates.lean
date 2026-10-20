import Results.Genus.InverseCertificates.Data
import Results.Genus.InverseCertificates.Golden
import Results.Genus.InverseCertificates.MixedScalar

/-!
# Original submitted-paper fixed denominator inverse certificates

This is the degree-80 recurrence and full degree-82/86 residual route in the
submitted manuscript e04fb276, Table `raw-reciprocal-residuals` and Lemma
`raw:wiener`. No later whole-circle or arc certificate is substituted.
All finite acceptance uses kernel-checkable `decide` or `norm_num` proofs.
-/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.InverseCertificates
open WeightedSeries

def K1 : PowerSeries ℝ := intSeries k1Coeffs
def K2 : PowerSeries ℝ := intSeries k2Coeffs
def V1 : PowerSeries ℝ := intSeries v1Coeffs
def V2 : PowerSeries ℝ := intSeries v2Coeffs

lemma K1_original : K1 = 1 + PowerSeries.X + PowerSeries.X ^ 2 := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n ≤ 2
  · interval_cases n <;> norm_num [K1, k1Coeffs, PowerSeries.coeff_X,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  · have hz : PowerSeries.coeff n K1 = 0 := intSeries_support k1Coeffs n (by
      simp only [k1Coeffs, List.length_cons, List.length_nil]; omega)
    rw [hz]
    simp only [map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    split_ifs <;> (try omega) <;> norm_num

lemma K2_original : K2 = 1 + PowerSeries.X + 2 * PowerSeries.X ^ 2 +
    PowerSeries.X ^ 3 - PowerSeries.X ^ 5 - PowerSeries.X ^ 6 := by
  rw [two_mul]
  apply PowerSeries.ext
  intro n
  by_cases hn : n ≤ 6
  · interval_cases n <;> norm_num [K2, k2Coeffs, PowerSeries.coeff_X,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_one, map_ofNat]
  · have hz : PowerSeries.coeff n K2 = 0 := intSeries_support k2Coeffs n (by
      simp only [k2Coeffs, List.length_cons, List.length_nil]; omega)
    rw [hz]
    simp only [map_add, map_sub, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_one]
    split_ifs <;> (try omega) <;> norm_num

lemma K1_constant : PowerSeries.constantCoeff K1 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  norm_num [K1, k1Coeffs]

lemma K2_constant : PowerSeries.constantCoeff K2 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  norm_num [K2, k2Coeffs]

/-- This identity is an equality of complete formal series. -/
lemma K1_residual : 1 - K1 * V1 = intSeries e1Coeffs :=
  residualCheck_sound k1Coeffs v1Coeffs e1Coeffs (by decide) (by decide) k1_residual_check

/-- All coefficients beyond degree86 are also checked via the support theorem. -/
lemma K2_residual : 1 - K2 * V2 = intSeries e2Coeffs :=
  residualCheck_sound k2Coeffs v2Coeffs e2Coeffs (by decide) (by decide) k2_residual_check

lemma K1_residual_zero_prefix (n : ℕ) (hn : n ≤ 80) :
    PowerSeries.coeff n (1 - K1 * V1) = 0 := by
  rw [K1_residual, coeff_intSeries]
  have h : ∀ i : Fin 81, e1Coeffs.getD i 0 = 0 := by decide
  rw [h ⟨n, by omega⟩, Int.cast_zero]

lemma K2_residual_zero_prefix (n : ℕ) (hn : n ≤ 80) :
    PowerSeries.coeff n (1 - K2 * V2) = 0 := by
  rw [K2_residual, coeff_intSeries]
  have h : ∀ i : Fin 81, e2Coeffs.getD i 0 = 0 := by decide
  rw [h ⟨n, by omega⟩, Int.cast_zero]

lemma K1_residual_support (n : ℕ) (hn : 83 ≤ n) :
    PowerSeries.coeff n (1 - K1 * V1) = 0 := by
  rw [K1_residual]
  exact intSeries_support e1Coeffs n (by simpa [e1Coeffs] using hn)

lemma K2_residual_support (n : ℕ) (hn : 87 ≤ n) :
    PowerSeries.coeff n (1 - K2 * V2) = 0 := by
  rw [K2_residual]
  exact intSeries_support e2Coeffs n (by simpa [e2Coeffs] using hn)

lemma V1_support (n : ℕ) (hn : 81 ≤ n) : PowerSeries.coeff n V1 = 0 :=
  intSeries_support v1Coeffs n (by simpa [v1Coeffs] using hn)

lemma V2_support (n : ℕ) (hn : 81 ≤ n) : PowerSeries.coeff n V2 = 0 :=
  intSeries_support v2Coeffs n (by simpa [v2Coeffs] using hn)

/-- The listed first reciprocal is exactly the original Q(0)=1 recurrence. -/
lemma V1_recurrence_coeff (n : ℕ) (hn : n ≤ 80) :
    PowerSeries.coeff n V1 =
      (FiniteArithmetic.rationalCoeff (fun j => if j = 0 then 1 else 0)
        (fun j => k1Coeffs.getD j 0) n : ℝ) := by
  rw [V1, coeff_intSeries]
  congr 1
  exact FiniteArithmetic.validPrefix_sound _ _ _ k1_reciprocal_prefix n
    (by change n < 81; omega)

/-- The second table is linked to that same source recurrence, at every stored degree. -/
lemma V2_recurrence_coeff (n : ℕ) (hn : n ≤ 80) :
    PowerSeries.coeff n V2 =
      (FiniteArithmetic.rationalCoeff (fun j => if j = 0 then 1 else 0)
        (fun j => k2Coeffs.getD j 0) n : ℝ) := by
  rw [V2, coeff_intSeries]
  congr 1
  exact FiniteArithmetic.validPrefix_sound _ _ _ k2_reciprocal_prefix n
    (by change n < 81; omega)

lemma intSeries_norm_lt_of_rat (a : List ℤ) {r C : ℚ} {x : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ (r : ℝ)) (h : ratHorner r a < C) :
    weightedNorm x (fun n => PowerSeries.coeff n (intSeries a)) < (C : ℝ) := by
  calc
    _ ≤ weightedNorm (r : ℝ) (fun n => PowerSeries.coeff n (intSeries a)) :=
      weightedNorm_mono_radius (intSeries_summable a (r : ℝ)) hx hxr
    _ = (ratHorner r a : ℝ) := intSeries_norm_rat a r
    _ < (C : ℝ) := by exact_mod_cast h

lemma q_le_qUpper : q ≤ (qUpper : ℝ) := by simpa [qUpper] using q_upper

lemma V1_norm : weightedNorm q (fun n => PowerSeries.coeff n V1) < 212 / 100 := by
  have h := intSeries_norm_lt_of_rat v1Coeffs q_nonneg q_le_qUpper v1_norm_rational
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [V1, V2]

lemma V2_norm : weightedNorm q (fun n => PowerSeries.coeff n V2) < 343 / 100 := by
  have h := intSeries_norm_lt_of_rat v2Coeffs q_nonneg q_le_qUpper v2_norm_rational
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [V1, V2]

lemma E1_norm : weightedNorm q (fun n => PowerSeries.coeff n (1 - K1 * V1)) <
    1 / 10^16 := by
  rw [K1_residual]
  have h := intSeries_norm_lt_of_rat e1Coeffs q_nonneg q_le_qUpper e1_norm_rational
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_one] at h
  convert h using 1 <;> norm_num [V1, V2]

lemma E2_norm : weightedNorm q (fun n => PowerSeries.coeff n (1 - K2 * V2)) <
    1 / 10^8 := by
  rw [K2_residual]
  have h := intSeries_norm_lt_of_rat e2Coeffs q_nonneg q_le_qUpper e2_norm_rational
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_one] at h
  convert h using 1 <;> norm_num [V1, V2]

lemma E1_norm_lt_one :
    weightedNorm q (fun n => PowerSeries.coeff n (1-K1*V1)) < 1 :=
  E1_norm.trans (by norm_num)

lemma E2_norm_lt_one :
    weightedNorm q (fun n => PowerSeries.coeff n (1-K2*V2)) < 1 :=
  E2_norm.trans (by norm_num)

/-- The complete formal inverse is absolutely q-summable, including its infinite tail. -/
theorem K1_inverse_norm :
    WeightedSummable q (fun n => PowerSeries.coeff n K1⁻¹) ∧
    weightedNorm q (fun n => PowerSeries.coeff n K1⁻¹) < 7 / 2 := by
  have hsmall : weightedNorm q (fun n => PowerSeries.coeff n (1 - K1 * V1)) < 1 :=
    E1_norm.trans (by norm_num)
  obtain ⟨hs, hb⟩ := powerSeries_inverse_of_residual K1 V1 q_nonneg
    (by rw [K1_constant]; norm_num) (intSeries_summable v1Coeffs q)
    (by rw [K1_residual]; exact intSeries_summable e1Coeffs q) hsmall
  refine ⟨hs, hb.trans_lt ?_⟩
  apply (div_lt_iff₀ (sub_pos.mpr hsmall)).2
  nlinarith [V1_norm, E1_norm]

/-- The second original denominator also has full inverse norm below7/2. -/
theorem K2_inverse_norm :
    WeightedSummable q (fun n => PowerSeries.coeff n K2⁻¹) ∧
    weightedNorm q (fun n => PowerSeries.coeff n K2⁻¹) < 7 / 2 := by
  have hsmall : weightedNorm q (fun n => PowerSeries.coeff n (1 - K2 * V2)) < 1 :=
    E2_norm.trans (by norm_num)
  obtain ⟨hs, hb⟩ := powerSeries_inverse_of_residual K2 V2 q_nonneg
    (by rw [K2_constant]; norm_num) (intSeries_summable v2Coeffs q)
    (by rw [K2_residual]; exact intSeries_summable e2Coeffs q) hsmall
  refine ⟨hs, hb.trans_lt ?_⟩
  apply (div_lt_iff₀ (sub_pos.mpr hsmall)).2
  nlinarith [V2_norm, E2_norm]

lemma K1_norm : weightedNorm q (fun n => PowerSeries.coeff n K1) = 2 := by
  rw [K1, intSeries_norm]
  norm_num [realHorner, k1Coeffs]
  nlinarith [q_relation]

lemma K2_norm : weightedNorm q (fun n => PowerSeries.coeff n K2) = 4 - 2 * q := by
  rw [K2, intSeries_norm]
  norm_num [realHorner, k2Coeffs]
  linear_combination (q^4 + q^2 + 3) * q_relation

lemma K2_norm_lt : weightedNorm q (fun n => PowerSeries.coeff n K2) < 14 / 5 := by
  rw [K2_norm]
  linarith [q_lower]

end SubmittedGenus.InverseCertificates
