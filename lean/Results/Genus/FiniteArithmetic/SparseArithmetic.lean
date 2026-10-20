import Results.Genus.FiniteArithmetic

namespace SubmittedGenus.FiniteArithmetic.Sparse

open PowerSeries

abbrev Terms := List (ℕ × ℤ)

/-- A finite integer polynomial, stored by exponent and coefficient. -/
noncomputable def series (terms : Terms) : PowerSeries ℤ :=
  (terms.map (fun t => C t.2 * X^t.1)).sum

def coefficient (terms : Terms) (n : ℕ) : ℤ :=
  (terms.map (fun t => if n = t.1 then t.2 else 0)).sum

def feedback (terms : Terms) (values : ℕ → ℤ) (n : ℕ) : ℤ :=
  (terms.map (fun t => if t.1 ≤ n then t.2 * values (n - t.1) else 0)).sum

@[simp] theorem series_nil : series [] = 0 := rfl
@[simp] theorem series_cons (t : ℕ × ℤ) (terms : Terms) :
    series (t :: terms) = C t.2 * X^t.1 + series terms := rfl

theorem coeff_series (terms : Terms) (n : ℕ) : coeff n (series terms) = coefficient terms n := by
  induction terms with
  | nil => simp [series, coefficient]
  | cons t terms ih =>
    rw [series_cons, map_add, coeff_C_mul_X_pow, ih]
    simp only [coefficient, List.map_cons, List.sum_cons]

theorem coeff_series_mul (terms : Terms) (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (series terms * f) = feedback terms (fun i => coeff i f) n := by
  induction terms with
  | nil => simp [series, feedback]
  | cons t terms ih =>
    rw [series_cons, add_mul, map_add, mul_assoc, coeff_C_mul, coeff_X_pow_mul', ih]
    simp only [feedback, List.map_cons, List.sum_cons]
    congr 1
    split_ifs <;> simp_all

/-- The source identity itself supplies the sparse recurrence. -/
theorem source_recurrence (p q : Terms) (f : PowerSeries ℤ)
    (hf : (1 + series q) * f = series p) (n : ℕ) :
    coeff n f = coefficient p n - feedback q (fun i => coeff i f) n := by
  have h := congrArg (coeff n) hf
  rw [add_mul, one_mul, map_add, coeff_series_mul, coeff_series] at h
  omega

/-- Array lookup has a specified zero value outside the accepted prefix. -/
def entry (values : Array ℤ) (n : ℕ) : ℤ := values[n]?.getD 0

/-- A local, exact sparse recurrence certificate. The denominator's constant
coefficient is represented by the separate leading 1. -/
def ValidPrefix (p q : Terms) (values : Array ℤ) : Prop :=
  ∀ n : Fin values.size, entry values n = coefficient p n - feedback q (entry values) n

instance (p q : Terms) (values : Array ℤ) : Decidable (ValidPrefix p q values) :=
  inferInstanceAs (Decidable (∀ n : Fin values.size, _))

/-- Accepted entries equal independently defined source coefficients; neither
an external table nor the checker defines the mathematical source. -/
theorem validPrefix_source (p q : Terms) (values : Array ℤ)
    (hq : ∀ t ∈ q, 0 < t.1) (h : ValidPrefix p q values)
    (f : PowerSeries ℤ) (hf : (1 + series q) * f = series p) :
    ∀ n < values.size, entry values n = coeff n f := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hv := h ⟨n, hn⟩
    change entry values n = coefficient p n - feedback q (entry values) n at hv
    rw [hv, source_recurrence p q f hf n]
    congr 1
    unfold feedback
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    by_cases htn : t.1 ≤ n
    · rw [if_pos htn, if_pos htn]
      have hj : n - t.1 < n := by have := hq t ht; omega
      rw [ih (n - t.1) hj (hj.trans hn)]
    · rw [if_neg htn, if_neg htn]

#print axioms validPrefix_source

end SubmittedGenus.FiniteArithmetic.Sparse
