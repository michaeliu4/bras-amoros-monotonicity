import Results.Genus.FiniteArithmetic.GradedSources

namespace SubmittedGenus.FiniteArithmetic.Geometric

open PowerSeries

/-- A single actual natural-number letter, at least the specified threshold. -/
abbrev Digits (minimum n : ℕ) := {d : ℕ // minimum ≤ d ∧ d = n}

noncomputable instance digitsFintype (minimum n : ℕ) : Fintype (Digits minimum n) :=
  Fintype.ofInjective (fun _ : Digits minimum n => ()) (by
    intro a b _
    exact Subtype.ext (a.property.2.trans b.property.2.symm))

theorem digits_card (minimum n : ℕ) :
    Fintype.card (Digits minimum n) = if minimum ≤ n then 1 else 0 := by
  by_cases hn : minimum ≤ n
  · rw [if_pos hn]
    letI : Unique (Digits minimum n) :=
      ⟨⟨⟨n, hn, rfl⟩⟩, fun d => Subtype.ext d.property.2⟩
    exact Fintype.card_unique
  · rw [if_neg hn]
    haveI : IsEmpty (Digits minimum n) := ⟨fun d => hn (d.property.2 ▸ d.property.1)⟩
    exact Fintype.card_eq_zero

noncomputable def digitSeries (minimum : ℕ) : PowerSeries ℤ := Graded.series (Digits minimum)

@[simp] theorem coeff_digitSeries (minimum n : ℕ) :
    coeff n (digitSeries minimum) = if minimum ≤ n then 1 else 0 := by
  simp [digitSeries, digits_card]

/-- Geometric identity proved for the actual all-length letter source. -/
theorem digitSeries_identity (minimum : ℕ) :
    (1 - (X : PowerSeries ℤ)) * digitSeries minimum = X^minimum := by
  apply PowerSeries.ext
  intro n
  have hx : (X : PowerSeries ℤ) * digitSeries minimum = X^1 * digitSeries minimum := by simp
  rw [sub_mul, one_mul, map_sub, hx, coeff_X_pow_mul']
  simp only [coeff_digitSeries, coeff_X_pow]
  split_ifs <;> omega

#print axioms digitSeries_identity

end SubmittedGenus.FiniteArithmetic.Geometric
