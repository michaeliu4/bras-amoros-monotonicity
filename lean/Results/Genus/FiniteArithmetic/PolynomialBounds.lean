import Results.Genus.FiniteArithmetic.SeriesBounds
import Results.Genus.FiniteArithmetic.SparseArithmetic

namespace SubmittedGenus.FiniteArithmetic.Analytic

open PowerSeries
noncomputable section

/-- Finite monomial support is an unconditional convergence witness. -/
theorem monomial_bound (r : ℝ) (c : ℤ) (k : ℕ) :
    SummableAt r (C c * X^k) ∧ normAt r (C c * X^k) ≤ |(c : ℝ)| * r^k := by
  have he : ∀ n, WeightedSeries.absWeightedTerm r (realCoeff (C c * X^k)) n =
      if n = k then |(c : ℝ)| * r^k else 0 := by
    intro n
    simp only [WeightedSeries.absWeightedTerm, realCoeff, coeff_C_mul_X_pow]
    split_ifs with hn
    · subst n; rfl
    · simp
  constructor
  · apply summable_of_ne_finset_zero (s := {k})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    rw [he, if_neg hn]
  · calc
      normAt r (C c * X^k) = ∑' n, if n = k then |(c : ℝ)| * r^k else 0 := tsum_congr he
      _ ≤ _ := by simp

theorem xpow_bound (r : ℝ) (k : ℕ) :
    SummableAt r ((X : PowerSeries ℤ)^k) ∧ normAt r ((X : PowerSeries ℤ)^k) ≤ r^k := by
  simpa using monomial_bound r 1 k

theorem one_bound (r : ℝ) : SummableAt r (1 : PowerSeries ℤ) ∧ normAt r 1 ≤ 1 := by
  simpa using xpow_bound r 0

theorem zero_bound (r : ℝ) : SummableAt r (0 : PowerSeries ℤ) ∧ normAt r 0 ≤ 0 := by
  simpa using monomial_bound r 0 0

def sparseAbsEval (r : ℝ) (terms : Sparse.Terms) : ℝ :=
  (terms.map (fun t => |(t.2 : ℝ)| * r^t.1)).sum

/-- Triangle bounds for finite exact integer polynomials; repeated exponents
remain sound and no positivity of signed coefficients is assumed. -/
theorem sparse_bound {r : ℝ} (hr : 0 ≤ r) (terms : Sparse.Terms) :
    SummableAt r (Sparse.series terms) ∧ normAt r (Sparse.series terms) ≤ sparseAbsEval r terms := by
  induction terms with
  | nil => exact zero_bound r
  | cons t terms ih =>
    rw [Sparse.series_cons]
    exact add_bound hr (monomial_bound r t.2 t.1) ih

theorem two_geometric_bound {r A B C : ℝ} {a b c f : PowerSeries ℤ} (hr : 0 ≤ r)
    (ha : SummableAt r a ∧ normAt r a ≤ A) (hb : SummableAt r b ∧ normAt r b ≤ B)
    (hc : SummableAt r c ∧ normAt r c ≤ C) (hB : B < 1) (hC : C < 1)
    (hf : ((1 - b) * (1 - c)) * f = a) :
    SummableAt r f ∧ normAt r f ≤ A / (1 - B) / (1 - C) := by
  have ht := geometric_bound hr ha hb hB (f := (1 - c) * f) (by simpa only [mul_assoc] using hf)
  exact geometric_bound hr ht hc hC rfl

theorem three_geometric_bound {r A B C D : ℝ} {a b c d f : PowerSeries ℤ} (hr : 0 ≤ r)
    (ha : SummableAt r a ∧ normAt r a ≤ A) (hb : SummableAt r b ∧ normAt r b ≤ B)
    (hc : SummableAt r c ∧ normAt r c ≤ C) (hd : SummableAt r d ∧ normAt r d ≤ D)
    (hB : B < 1) (hC : C < 1) (hD : D < 1)
    (hf : ((1 - b) * (1 - c) * (1 - d)) * f = a) :
    SummableAt r f ∧ normAt r f ≤ A / (1 - B) / (1 - C) / (1 - D) := by
  have ht := two_geometric_bound hr ha hb hc hB hC (f := (1 - d) * f)
    (by simpa only [mul_assoc] using hf)
  exact geometric_bound hr ht hd hD rfl

#print axioms sparse_bound
#print axioms three_geometric_bound

end
end SubmittedGenus.FiniteArithmetic.Analytic
