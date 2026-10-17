import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Exact arithmetic for the original submitted genus paper

Source: submitted manuscript e04fb276, equation `cmb:coefficient-recurrence`.
This module separates a generic formal-series soundness theorem, a counted-source
identity, and kernel-checked concrete finite acceptance. No external output or
hash is used as a mathematical assumption.
-/

namespace SubmittedGenus.FiniteArithmetic

open scoped BigOperators

/-- Cauchy convolution, with all indices explicitly finite. -/
def convolution {R : Type*} [Semiring R] (a b : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

/-- Truncation through (and including) the stated degree. -/
def truncate {R : Type*} [Zero R] (degree : ℕ) (a : ℕ → R) (n : ℕ) : R :=
  if n ≤ degree then a n else 0

theorem truncated_add {R : Type*} [AddMonoid R] (degree : ℕ) (a b : ℕ → R) :
    truncate degree (fun n => a n + b n) =
      fun n => truncate degree a n + truncate degree b n := by
  funext n
  simp only [truncate]
  split_ifs <;> simp

/-- No discarded high coefficient can affect a retained product coefficient. -/
theorem truncated_convolution {R : Type*} [Semiring R] (degree : ℕ)
    (a b : ℕ → R) :
    truncate degree (convolution (truncate degree a) (truncate degree b)) =
      truncate degree (convolution a b) := by
  funext n
  by_cases hn : n ≤ degree
  · simp only [truncate, if_pos hn, convolution]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ n := by simpa using (Finset.mem_range.mp hi)
    have hleft : i ≤ degree := hi'.trans hn
    have hright : n - i ≤ degree := (Nat.sub_le n i).trans hn
    simp [hleft, hright]
  · simp [truncate, hn]

/-- The executable convolution is the usual formal power-series product. -/
theorem coeff_mul_eq_convolution {R : Type*} [Semiring R]
    (a b : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (a * b) =
      convolution (fun i => PowerSeries.coeff i a)
        (fun i => PowerSeries.coeff i b) n := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

/-- The exact `Q(0)=1` recurrence. Coefficients may be signed integers. -/
def rationalCoeff (p q : ℕ → ℤ) (n : ℕ) : ℤ :=
  p n - ∑ i : Fin n, q (i.val + 1) * rationalCoeff p q (n - 1 - i.val)
termination_by n
decreasing_by
  have := i.isLt
  omega

theorem rationalCoeff_spec (p q : ℕ → ℤ) (n : ℕ) :
    rationalCoeff p q n =
      p n - ∑ i ∈ Finset.range n, q (i + 1) * rationalCoeff p q (n - 1 - i) := by
  rw [rationalCoeff]
  exact congrArg (fun z => p n - z)
    (Fin.sum_univ_eq_sum_range (fun i => q (i + 1) * rationalCoeff p q (n - 1 - i)) n)

theorem convolution_head_tail (q f : ℕ → ℤ) (n : ℕ) :
    convolution q f n = q 0 * f n +
      ∑ i ∈ Finset.range n, q (i + 1) * f (n - 1 - i) := by
  rw [convolution, Finset.sum_range_succ']
  simp only [Nat.sub_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have he : n - (i + 1) = n - 1 - i := by omega
  rw [he]

/-- Soundness of the recurrence as the coefficient equation `Q F = P`. -/
theorem rationalCoeff_sound (p q : ℕ → ℤ) (hq : q 0 = 1) (n : ℕ) :
    convolution q (rationalCoeff p q) n = p n := by
  rw [convolution_head_tail, hq, one_mul, rationalCoeff_spec]
  omega

/-- Uniqueness is what licenses applying the executable recurrence to a source. -/
theorem rationalCoeff_unique (p q f : ℕ → ℤ) (hq : q 0 = 1)
    (hf : ∀ n, convolution q f n = p n) : f = rationalCoeff p q := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hs := hf n
    rw [convolution_head_tail, hq, one_mul] at hs
    rw [rationalCoeff_spec]
    have ht : (∑ i ∈ Finset.range n, q (i + 1) * f (n - 1 - i)) =
        ∑ i ∈ Finset.range n, q (i + 1) * rationalCoeff p q (n - 1 - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (n - 1 - i) (by have := Finset.mem_range.mp hi; omega)]
    rw [ht] at hs
    omega

noncomputable def rationalSeries (p q : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (rationalCoeff (fun n => PowerSeries.coeff n p)
    (fun n => PowerSeries.coeff n q))

theorem rationalSeries_sound (p q : PowerSeries ℤ)
    (hq : PowerSeries.coeff 0 q = 1) : q * rationalSeries p q = p := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mul_eq_convolution]
  simpa only [rationalSeries, PowerSeries.coeff_mk] using
    rationalCoeff_sound (fun n => PowerSeries.coeff n p)
      (fun n => PowerSeries.coeff n q) hq n

theorem source_coefficients_eq_recurrence (p q f : PowerSeries ℤ)
    (hq : PowerSeries.coeff 0 q = 1) (hf : q * f = p) (n : ℕ) :
    PowerSeries.coeff n f = rationalCoeff
      (fun i => PowerSeries.coeff i p) (fun i => PowerSeries.coeff i q) n := by
  have h := rationalCoeff_unique (fun i => PowerSeries.coeff i p)
    (fun i => PowerSeries.coeff i q) (fun i => PowerSeries.coeff i f) hq
    (fun i => by rw [← coeff_mul_eq_convolution, hf])
  exact congrFun h n

/-- A finite certificate checks the defining recurrence at every stored index.
It does not assert that any external generator computed the source correctly. -/
def ValidPrefix (p q : ℕ → ℤ) (values : List ℤ) : Prop :=
  ∀ n : Fin values.length, values.getD n 0 =
    p n - ∑ i ∈ Finset.range n, q (i + 1) * values.getD (n - 1 - i) 0

instance (p q : ℕ → ℤ) (values : List ℤ) : Decidable (ValidPrefix p q values) :=
  inferInstanceAs (Decidable (∀ n : Fin values.length, _))

/-- Acceptance of a finite table entails equality to every corresponding exact
recurrence coefficient. Only the local integer equations are evaluated. -/
theorem validPrefix_sound (p q : ℕ → ℤ) (values : List ℤ)
    (h : ValidPrefix p q values) :
    ∀ n < values.length, values.getD n 0 = rationalCoeff p q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hs := h ⟨n, hn⟩
    change values.getD n 0 = p n -
      ∑ i ∈ Finset.range n, q (i + 1) * values.getD (n - 1 - i) 0 at hs
    rw [rationalCoeff_spec, hs]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hj : n - 1 - i < n := by have := Finset.mem_range.mp hi; omega
    rw [ih (n - 1 - i) hj (hj.trans hn)]

end SubmittedGenus.FiniteArithmetic
