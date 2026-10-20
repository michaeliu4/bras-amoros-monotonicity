import Results.Genus.FiniteArithmetic.SparseArithmetic

namespace SubmittedGenus.FiniteArithmetic.Sparse

open PowerSeries

/-- Exact certificates may use any total integer lookup implementation. -/
def LookupValidPrefix (p q : Terms) (values : ℕ → ℤ) (length : ℕ) : Prop :=
  ∀ n : Fin length, values n = coefficient p n - feedback q values n

instance (p q : Terms) (values : ℕ → ℤ) (length : ℕ) :
    Decidable (LookupValidPrefix p q values length) :=
  inferInstanceAs (Decidable (∀ n : Fin length, _))

/-- Lookup representation does not enter the semantic argument: every accepted
row is proved equal to the independently defined source coefficient. -/
theorem lookupValidPrefix_source (p q : Terms) (values : ℕ → ℤ) (length : ℕ)
    (hq : ∀ t ∈ q, 0 < t.1) (h : LookupValidPrefix p q values length)
    (f : PowerSeries ℤ) (hf : (1 + series q) * f = series p) :
    ∀ n < length, values n = coeff n f := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hv := h ⟨n, hn⟩
    change values n = coefficient p n - feedback q values n at hv
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

#print axioms lookupValidPrefix_source

end SubmittedGenus.FiniteArithmetic.Sparse
