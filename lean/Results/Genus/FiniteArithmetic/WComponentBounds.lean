import Results.Genus.FiniteArithmetic.PolynomialBounds
import Results.Genus.FiniteArithmetic.WPolynomial

namespace SubmittedGenus.FiniteArithmetic.Analytic
open PowerSeries Reflection
noncomputable section
set_option maxHeartbeats 3000000

def rho : ℝ := 63 / 100
theorem rho_nonneg : 0 ≤ rho := by norm_num [rho]
theorem rho_lt_one : rho < 1 := by norm_num [rho]

def b23 : Sparse.Terms := [(2, 1), (3, 1)]
def b234 : Sparse.Terms := [(2, 1), (3, 1), (4, 1)]
def b2345 : Sparse.Terms := [(2, 1), (3, 1), (4, 1), (5, 1)]
def bJL : Sparse.Terms := [(5, 2), (6, 1)]
def bJR : Sparse.Terms := [(4, 3), (5, 2), (6, 1)]
def aH : Sparse.Terms := [(4, 1), (5, 1)]
def aJ : Sparse.Terms := [(12, 2), (14, 4), (15, 2)]
def aK : Sparse.Terms := [(9, 1)]
def a5 : Sparse.Terms := [(0, 1), (3, 1), (4, 1), (5, 1)]
def b5 : Sparse.Terms := [(5, 4), (6, 5), (7, 4), (8, 3), (9, 2), (10, 1)]
def a6 : Sparse.Terms := [(0, 1), (3, 1), (4, 1), (5, 1), (6, 1)]
def b6 : Sparse.Terms := [(6, 5), (7, 6), (8, 5), (9, 4), (10, 3), (11, 2), (12, 1)]
def a7 : Sparse.Terms := [(0, 1), (4, 1), (5, 1), (6, 1), (7, 1)]
def b7 : Sparse.Terms := [(7, 6), (8, 7), (9, 6), (10, 5), (11, 4), (12, 3), (13, 2), (14, 1)]
def a8 : Sparse.Terms := [(0, 1), (4, 1), (5, 1), (6, 1), (7, 1), (8, 1)]
def b8 : Sparse.Terms := [(8, 7), (9, 8), (10, 7), (11, 6), (12, 5), (13, 4), (14, 3), (15, 2), (16, 1)]

theorem b23_small : sparseAbsEval rho b23 < 1 := by norm_num [sparseAbsEval, rho, b23]

theorem b234_small : sparseAbsEval rho b234 < 1 := by norm_num [sparseAbsEval, rho, b234]

theorem b2345_small : sparseAbsEval rho b2345 < 1 := by norm_num [sparseAbsEval, rho, b2345]

theorem bJL_small : sparseAbsEval rho bJL < 1 := by norm_num [sparseAbsEval, rho, bJL]

theorem bJR_small : sparseAbsEval rho bJR < 1 := by norm_num [sparseAbsEval, rho, bJR]

theorem b5_small : sparseAbsEval rho b5 < 1 := by norm_num [sparseAbsEval, rho, b5]

theorem b6_small : sparseAbsEval rho b6 < 1 := by norm_num [sparseAbsEval, rho, b6]

theorem b7_small : sparseAbsEval rho b7 < 1 := by norm_num [sparseAbsEval, rho, b7]

theorem b8_small : sparseAbsEval rho b8 < 1 := by norm_num [sparseAbsEval, rho, b8]

theorem factor_5_sparse_identity : (1 - Sparse.series b5) * capacityFactor 5 = Sparse.series a5 := by
  have hd : factorDenominator 5 = 1 - Sparse.series b5 := by
    rw [factorDenominator_5_expanded]
    norm_num [Sparse.series, b5] <;> ring
  have hn : factorNumerator 5 = Sparse.series a5 := by
    rw [factorNumerator_5_expanded]
    norm_num [Sparse.series, a5] <;> ring
  rw [← hd, ← hn]
  exact capacityFactor_source_identity 5

theorem factor_5_bound : SummableAt rho (capacityFactor 5) ∧ normAt rho (capacityFactor 5) ≤ 88 := by
  have h := geometric_bound rho_nonneg (sparse_bound rho_nonneg a5) (sparse_bound rho_nonneg b5) b5_small factor_5_sparse_identity
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num [sparseAbsEval, rho, a5, b5]

theorem factor_6_sparse_identity : (1 - Sparse.series b6) * capacityFactor 6 = Sparse.series a6 := by
  have hd : factorDenominator 6 = 1 - Sparse.series b6 := by
    rw [factorDenominator_6_expanded]
    norm_num [Sparse.series, b6] <;> ring
  have hn : factorNumerator 6 = Sparse.series a6 := by
    rw [factorNumerator_6_expanded]
    norm_num [Sparse.series, a6] <;> ring
  rw [← hd, ← hn]
  exact capacityFactor_source_identity 6

theorem factor_6_bound : SummableAt rho (capacityFactor 6) ∧ normAt rho (capacityFactor 6) ≤ 36 / 5 := by
  have h := geometric_bound rho_nonneg (sparse_bound rho_nonneg a6) (sparse_bound rho_nonneg b6) b6_small factor_6_sparse_identity
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num [sparseAbsEval, rho, a6, b6]

theorem factor_7_sparse_identity : (1 - Sparse.series b7) * capacityFactor 7 = Sparse.series a7 := by
  have hd : factorDenominator 7 = 1 - Sparse.series b7 := by
    rw [factorDenominator_7_expanded]
    norm_num [Sparse.series, b7] <;> ring
  have hn : factorNumerator 7 = Sparse.series a7 := by
    rw [factorNumerator_7_expanded]
    norm_num [Sparse.series, a7] <;> ring
  rw [← hd, ← hn]
  exact capacityFactor_source_identity 7

theorem factor_7_bound : SummableAt rho (capacityFactor 7) ∧ normAt rho (capacityFactor 7) ≤ 17 / 5 := by
  have h := geometric_bound rho_nonneg (sparse_bound rho_nonneg a7) (sparse_bound rho_nonneg b7) b7_small factor_7_sparse_identity
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num [sparseAbsEval, rho, a7, b7]

theorem factor_8_sparse_identity : (1 - Sparse.series b8) * capacityFactor 8 = Sparse.series a8 := by
  have hd : factorDenominator 8 = 1 - Sparse.series b8 := by
    rw [factorDenominator_8_expanded]
    norm_num [Sparse.series, b8] <;> ring
  have hn : factorNumerator 8 = Sparse.series a8 := by
    rw [factorNumerator_8_expanded]
    norm_num [Sparse.series, a8] <;> ring
  rw [← hd, ← hn]
  exact capacityFactor_source_identity 8

theorem factor_8_bound : SummableAt rho (capacityFactor 8) ∧ normAt rho (capacityFactor 8) ≤ 5 / 2 := by
  have h := geometric_bound rho_nonneg (sparse_bound rho_nonneg a8) (sparse_bound rho_nonneg b8) b8_small factor_8_sparse_identity
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num [sparseAbsEval, rho, a8, b8]

theorem h_sparse_factor_identity : ((1 - Sparse.series b23) * (1 - Sparse.series b2345)) * capacityH = Sparse.series aH := by
  convert capacityH_source_identity using 1 <;>
    norm_num [Sparse.series, aH, b23, b2345, nsmul_eq_mul] <;> ring_nf <;> simp

theorem h_bound : SummableAt rho capacityH ∧ normAt rho capacityH ≤ 38 / 5 := by
  have h := two_geometric_bound rho_nonneg (sparse_bound rho_nonneg aH) (sparse_bound rho_nonneg b23) (sparse_bound rho_nonneg b2345) b23_small b2345_small h_sparse_factor_identity
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num [sparseAbsEval, rho, aH, b23, b2345]

theorem j_sparse_factor_identity : ((1 - Sparse.series bJL) * (1 - Sparse.series b23) * (1 - Sparse.series bJR)) * IsolatedFive.capacityJ = Sparse.series aJ := by
  convert IsolatedFive.capacityJ_source_identity using 1 <;>
    norm_num [Sparse.series, aJ, bJL, b23, bJR, nsmul_eq_mul] <;> ring_nf <;> simp

theorem j_bound : SummableAt rho IsolatedFive.capacityJ ∧ normAt rho IsolatedFive.capacityJ ≤ 23 / 100 := by
  have h := three_geometric_bound rho_nonneg (sparse_bound rho_nonneg aJ) (sparse_bound rho_nonneg bJL) (sparse_bound rho_nonneg b23) (sparse_bound rho_nonneg bJR) bJL_small b23_small bJR_small j_sparse_factor_identity
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num [sparseAbsEval, rho, aJ, bJL, b23, bJR]

theorem k_sparse_factor_identity : ((1 - Sparse.series b23) * (1 - Sparse.series b23) * (1 - Sparse.series b234)) * capacityK = Sparse.series aK := by
  convert capacityK_source_identity using 1 <;>
    norm_num [Sparse.series, aK, b23, b234, nsmul_eq_mul] <;> ring_nf <;> simp

theorem k_bound : SummableAt rho capacityK ∧ normAt rho capacityK ≤ 13 / 20 := by
  have h := three_geometric_bound rho_nonneg (sparse_bound rho_nonneg aK) (sparse_bound rho_nonneg b23) (sparse_bound rho_nonneg b23) (sparse_bound rho_nonneg b234) b23_small b23_small b234_small k_sparse_factor_identity
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num [sparseAbsEval, rho, aK, b23, b234]

#print axioms factor_5_bound
#print axioms h_bound
#print axioms j_bound
#print axioms k_bound
end
end SubmittedGenus.FiniteArithmetic.Analytic
