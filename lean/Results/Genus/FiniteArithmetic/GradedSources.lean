import Results.Genus.FiniteArithmetic.LocallyFiniteWords

namespace SubmittedGenus.FiniteArithmetic.Graded

open scoped BigOperators
open PowerSeries

/-- A generating series defined by cardinalities of independently given sources. -/
noncomputable def series (F : ℕ → Type) [∀ n, Fintype (F n)] : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (Fintype.card (F n) : ℤ))

@[simp] theorem coeff_series (F : ℕ → Type) [∀ n, Fintype (F n)] (n : ℕ) :
    coeff n (series F) = (Fintype.card (F n) : ℤ) := by simp [series]

/-- Independent source pairs with their exact weight split retained. -/
abbrev Product (F G : ℕ → Type) (n : ℕ) := Σ i : Fin (n + 1), F i.val × G (n - i.val)

noncomputable instance productFintype (F G : ℕ → Type) [∀ n, Fintype (F n)]
    [∀ n, Fintype (G n)] (n : ℕ) : Fintype (Product F G n) := inferInstance

theorem product_series (F G : ℕ → Type) [∀ n, Fintype (F n)] [∀ n, Fintype (G n)] :
    series (Product F G) = series F * series G := by
  apply PowerSeries.ext
  intro n
  rw [coeff_series, coeff_mul_eq_convolution]
  simp only [Product, Fintype.card_sigma, Fintype.card_prod, Nat.cast_sum,
    Nat.cast_mul, coeff_series, convolution]
  exact Fin.sum_univ_eq_sum_range
    (fun i => (Fintype.card (F i) : ℤ) * (Fintype.card (G (n - i)) : ℤ)) (n + 1)

abbrev Sum (F G : ℕ → Type) (n : ℕ) := F n ⊕ G n

noncomputable instance sumFintype (F G : ℕ → Type) [∀ n, Fintype (F n)]
    [∀ n, Fintype (G n)] (n : ℕ) : Fintype (Sum F G n) := inferInstance

theorem sum_series (F G : ℕ → Type) [∀ n, Fintype (F n)] [∀ n, Fintype (G n)] :
    series (Sum F G) = series F + series G := by
  apply PowerSeries.ext
  intro n
  simp [Sum]

/-- Add a fixed weight, with no source at a negative residual index. -/
def Shift (m : ℕ) (F : ℕ → Type) (n : ℕ) : Type := if m ≤ n then F (n - m) else PEmpty

noncomputable instance shiftFintype (m : ℕ) (F : ℕ → Type) [∀ n, Fintype (F n)]
    (n : ℕ) : Fintype (Shift m F n) := by unfold Shift; split_ifs <;> infer_instance

theorem shift_series (m : ℕ) (F : ℕ → Type) [∀ n, Fintype (F n)] :
    series (Shift m F) = (X : PowerSeries ℤ)^m * series F := by
  apply PowerSeries.ext
  intro n
  rw [coeff_series, coeff_X_pow_mul', coeff_series]
  by_cases hn : m ≤ n
  · simp only [Shift, if_pos hn]
  · simp only [Shift, if_neg hn, Fintype.card_pempty, Nat.cast_zero]

/-- An equivalence at every weight is sufficient to identify source series. -/
theorem series_congr (F G : ℕ → Type) [∀ n, Fintype (F n)] [∀ n, Fintype (G n)]
    (e : ∀ n, F n ≃ G n) : series F = series G := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_series]
  exact congrArg (fun x : ℕ => (x : ℤ)) (Fintype.card_congr (e n))

end SubmittedGenus.FiniteArithmetic.Graded
