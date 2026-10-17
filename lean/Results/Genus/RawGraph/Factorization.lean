import Results.Genus.RawGraph.Transfer
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Equiv.Basic

namespace SubmittedGenus.RawGraph.Factorization

open scoped BigOperators

/-- Products of zero-or-weight factors impose all local restrictions exactly. -/
theorem prod_gate {I R : Type*} [Fintype I] [CommMonoidWithZero R]
    (P : I → Prop) [DecidablePred P] (f : I → R) :
    (∏ i, if P i then f i else 0) = if ∀ i, P i then ∏ i, f i else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- A monomial weight is attached once to each coordinate, irrespective of
how many edge or loop restrictions refer to that coordinate. -/
theorem prod_gated_powers {I : Type*} [Fintype I]
    (P : I → Prop) [DecidablePred P] (cost : I → ℕ) :
    (∏ i, if P i then (Polynomial.X : Polynomial ℕ) ^ cost i else 0) =
      if ∀ i, P i then Polynomial.X ^ (∑ i, cost i) else 0 := by
  rw [prod_gate, Finset.prod_pow_eq_pow_sum]

/-- Independent finite components multiply exactly; no assignment is omitted
or duplicated when the vertex type is a disjoint union of component positions. -/
theorem sum_product_components {C A R : Type*} {V : C → Type*}
    [Fintype C] [DecidableEq C] [∀ c, Fintype (V c)]
    [∀ c, DecidableEq (V c)] [Fintype A] [CommSemiring R]
    (f : ∀ c, (V c → A) → R) :
    (∑ x : (Σ c, V c) → A, ∏ c, f c (fun v => x ⟨c, v⟩)) =
      ∏ c, ∑ y : V c → A, f c y := by
  classical
  rw [Fintype.prod_sum]
  exact Fintype.sum_equiv (Equiv.piCurry (fun (_ : C) (_ : V _) => A))
    _ _ (fun _ => rfl)

/-- Transporting an assignment along a vertex bijection preserves its sum.
This is the formal one-weight-per-physical-coordinate coverage check. -/
theorem sum_cost_reindex {C V : Type*} {P : C → Type*}
    [Fintype C] [∀ c, Fintype (P c)] [Fintype V]
    (label : (Σ c, P c) ≃ V) (x : V → ℕ) :
    (∑ v, x v) = ∑ c, ∑ j, x (label ⟨c, j⟩) := by
  calc
    (∑ v, x v) = ∑ y : Σ c, P c, x (label y) := (label.sum_comp x).symm
    _ = _ := Fintype.sum_sigma _

/-- Reindex the full source polynomial by a verified bijection of physical
vertices with component positions. -/
theorem sum_assignments_reindex {V W A R : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype A] [AddCommMonoid R]
    (label : W ≃ V) (f : (V → A) → R) :
    (∑ x : V → A, f x) = ∑ y : W → A, f (fun v => y (label.symm v)) := by
  classical
  exact Fintype.sum_equiv (Equiv.arrowCongr label.symm (Equiv.refl A))
    _ _ (fun x => by simp [Equiv.arrowCongr])

end SubmittedGenus.RawGraph.Factorization
