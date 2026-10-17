import Results.Genus.FiniteArithmetic.WComponentBounds

namespace SubmittedGenus.FiniteArithmetic.Analytic

open PowerSeries
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 1000

/-- All actual geometric digit sources converge at the manuscript's radius. -/
theorem digit_bound (m : ℕ) : SummableAt rho (Geometric.digitSeries m) ∧
    normAt rho (Geometric.digitSeries m) ≤ rho^m / (1 - rho) := by
  exact geometric_bound rho_nonneg (xpow_bound rho m)
    (by simpa only [pow_one] using xpow_bound rho 1) rho_lt_one
    (Geometric.digitSeries_identity m)

/-- A positive factorization of the full ordered-pair series avoids absolute
values of a signed rational numerator. -/
theorem pair_positive_factorization : OriginalTail.pairSeries =
    (X : PowerSeries ℤ)^8 * (7 * Geometric.digitSeries 0 + X * (Geometric.digitSeries 0)^2) := by
  have hg : (1 - (X : PowerSeries ℤ)) * Geometric.digitSeries 0 = 1 := by
    simpa using Geometric.digitSeries_identity 0
  have hne : (1 - (X : PowerSeries ℤ))^2 ≠ 0 := by
    intro h
    have hh := congrArg PowerSeries.constantCoeff h
    norm_num at hh
  apply mul_left_cancel₀ hne
  rw [OriginalTail.pairSeries_identity]
  calc
    7 • (X : PowerSeries ℤ)^8 - 6 • X^9 =
        7 * X^8 * ((1 - X) * Geometric.digitSeries 0) * (1 - X) +
          X^9 * ((1 - X) * Geometric.digitSeries 0)^2 := by rw [hg]; norm_num; ring
    _ = _ := by ring

theorem pair_bound : SummableAt rho OriginalTail.pairSeries ∧
    normAt rho OriginalTail.pairSeries ≤ 73 / 125 := by
  have hg := digit_bound 0
  have h7 : SummableAt rho (7 : PowerSeries ℤ) ∧ normAt rho 7 ≤ 7 := by
    simpa using monomial_bound rho 7 0
  have hx : SummableAt rho (X : PowerSeries ℤ) ∧ normAt rho X ≤ rho := by
    simpa using xpow_bound rho 1
  have hp := mul_bound rho_nonneg (xpow_bound rho 8)
    (add_bound rho_nonneg (mul_bound rho_nonneg h7 hg)
      (mul_bound rho_nonneg hx (mul_bound rho_nonneg hg hg)))
  rw [pair_positive_factorization, pow_two]
  refine ⟨hp.1, hp.2.trans ?_⟩
  norm_num [rho]

theorem relaxed_block_bound : SummableAt rho OriginalTail.blockSeries ∧
    normAt rho OriginalTail.blockSeries ≤ 713 / 208 := by
  have h4 := digit_bound 4
  have h4' : SummableAt rho (Geometric.digitSeries 4) ∧
      normAt rho (Geometric.digitSeries 4) ≤ 213 / 500 :=
    ⟨h4.1, h4.2.trans (by norm_num [rho])⟩
  have h := geometric_bound rho_nonneg (add_bound rho_nonneg (one_bound rho) h4')
    pair_bound (by norm_num) OriginalTail.blockSeries_identity
  exact ⟨h.1, h.2.trans (by norm_num)⟩

/-- The bound includes every marked pivot q≥9 and both full reflected blocks. -/
theorem m_tail_bound : SummableAt rho OriginalTail.capacityMTail ∧
    normAt rho OriginalTail.capacityMTail ≤ 1 / 2 := by
  have h := mul_bound rho_nonneg (digit_bound 9)
    (mul_bound rho_nonneg relaxed_block_bound relaxed_block_bound)
  rw [OriginalTail.capacityMTail_factorization, pow_two]
  exact ⟨h.1, h.2.trans (by norm_num [rho])⟩

theorem m_bound : SummableAt rho capacityM ∧ normAt rho capacityM ≤ 83 / 2 := by
  have h6 := mul_bound rho_nonneg (mul_bound rho_nonneg (xpow_bound rho 6) factor_6_bound) factor_5_bound
  have h7 := mul_bound rho_nonneg (mul_bound rho_nonneg (xpow_bound rho 7) factor_7_bound) factor_6_bound
  have h8 := mul_bound rho_nonneg (mul_bound rho_nonneg (xpow_bound rho 8) factor_8_bound) factor_7_bound
  have hfinite := add_bound rho_nonneg (add_bound rho_nonneg h6 h7) h8
  have hfinite' : SummableAt rho ((X : PowerSeries ℤ)^6 * Reflection.capacityFactor 6 * Reflection.capacityFactor 5 +
      X^7 * Reflection.capacityFactor 7 * Reflection.capacityFactor 6 +
      X^8 * Reflection.capacityFactor 8 * Reflection.capacityFactor 7) ∧
      normAt rho (X^6 * Reflection.capacityFactor 6 * Reflection.capacityFactor 5 +
      X^7 * Reflection.capacityFactor 7 * Reflection.capacityFactor 6 +
      X^8 * Reflection.capacityFactor 8 * Reflection.capacityFactor 7) ≤ 41 :=
    ⟨hfinite.1, hfinite.2.trans (by norm_num [rho])⟩
  rw [capacityM_source_identity]
  have h := add_bound rho_nonneg hfinite' m_tail_bound
  exact ⟨h.1, h.2.trans (by norm_num)⟩

/-- Original analytic input, with convergence established before the norm is
used. The rational upper bound 2499/50 is strictly below the stated 50. -/
theorem capacityW_summable_and_norm_lt_fifty :
    SummableAt rho capacityW ∧ normAt rho capacityW < 50 := by
  have h := add_bound rho_nonneg
    (add_bound rho_nonneg (add_bound rho_nonneg m_bound h_bound) j_bound) k_bound
  exact ⟨h.1, h.2.trans_lt (by norm_num)⟩

theorem capacityW_coeff_nonneg (n : ℕ) : 0 ≤ realCoeff capacityW n := by
  unfold realCoeff
  rw [capacityW_source_coeff]
  positivity

theorem capacityW_weighted_term_lt_fifty (n : ℕ) :
    realCoeff capacityW n * rho^n < 50 := by
  have h := capacityW_summable_and_norm_lt_fifty
  have ht := h.1.term_le rho_nonneg n
  change |realCoeff capacityW n| * rho^n ≤ normAt rho capacityW at ht
  rw [abs_of_nonneg (capacityW_coeff_nonneg n)] at ht
  exact ht.trans_lt h.2

#print axioms m_tail_bound
#print axioms capacityW_summable_and_norm_lt_fifty
#print axioms capacityW_weighted_term_lt_fifty

end
end SubmittedGenus.FiniteArithmetic.Analytic
