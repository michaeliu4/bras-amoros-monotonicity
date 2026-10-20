import Results.Genus.FiniteArithmetic.GradedSources

namespace SubmittedGenus.FiniteArithmetic.Graded

open scoped BigOperators
open PowerSeries

abbrev Atoms {α : Type} (weight : α → ℕ) (n : ℕ) := {a : α // weight a = n}

noncomputable def atomSeries {α : Type} (weight : α → ℕ)
    [∀ n, Fintype (Atoms weight n)] : PowerSeries ℤ := series (Atoms weight)

/-- Exact finite weighted partition semantics for any finite source alphabet. -/
theorem atomSeries_eq_sum {α : Type} [Fintype α] (weight : α → ℕ)
    [∀ n, Fintype (Atoms weight n)] :
    atomSeries weight = ∑ a : α, (X : PowerSeries ℤ)^weight a := by
  classical
  apply PowerSeries.ext
  intro n
  simp only [atomSeries, coeff_series, map_sum, coeff_X_pow]
  rw [Finset.sum_boole]
  rw [Fintype.card_subtype]
  congr 2
  ext a
  simp [eq_comm]

def atomsEquiv {α β : Type} (e : α ≃ β) (wa : α → ℕ) (wb : β → ℕ)
    (hw : ∀ a, wb (e a) = wa a) (n : ℕ) : Atoms wa n ≃ Atoms wb n where
  toFun a := ⟨e a.val, (hw a.val).trans a.property⟩
  invFun b := ⟨e.symm b.val, by rw [← hw, e.apply_symm_apply]; exact b.property⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv b := Subtype.ext (e.apply_symm_apply b.val)

theorem atomSeries_congr {α β : Type} (e : α ≃ β) (wa : α → ℕ) (wb : β → ℕ)
    [∀ n, Fintype (Atoms wa n)] [∀ n, Fintype (Atoms wb n)]
    (hw : ∀ a, wb (e a) = wa a) : atomSeries wa = atomSeries wb :=
  series_congr _ _ (atomsEquiv e wa wb hw)

theorem atomSeries_subtype {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P]
    (weight : α → ℕ) [∀ n, Fintype (Atoms (fun a : {a // P a} => weight a.val) n)] :
    atomSeries (fun a : {a // P a} => weight a.val) =
      ∑ a : α, if P a then (X : PowerSeries ℤ)^weight a else 0 := by
  rw [atomSeries_eq_sum]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) (fun a => (X : PowerSeries ℤ)^weight a)]
  exact Finset.sum_filter _ _

end SubmittedGenus.FiniteArithmetic.Graded
