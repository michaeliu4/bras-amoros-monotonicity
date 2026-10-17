import Results.Genus.GoldenTail.Numeric
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-! The submitted quadratic geometric-tail formula bounds every finite tail.
The proof telescopes its exact one-step identity and discards only a nonnegative
terminal value. It assumes no convergence or source-graph assertion. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.GoldenTail

/-- Real interpretation of the exact submitted quadratic tail expression. -/
def quadraticTailReal (x : ℝ) (K : ℕ) (a b c : ℝ) : ℝ :=
  x^K * ((a*(K:ℝ)^2 + b*K + c)/(1-x) +
    (2*a*K+b)*x/(1-x)^2 + a*x*(1+x)/(1-x)^3)

lemma quadraticTail_cast (x : ℚ) (K : ℕ) (a b c : ℚ) :
    ((quadraticTail x K a b c : ℚ) : ℝ) =
      quadraticTailReal (x:ℝ) K (a:ℝ) (b:ℝ) (c:ℝ) := by
  simp [quadraticTail,quadraticTailReal]

lemma quadraticTailReal_nonneg (x : ℝ) (K : ℕ) (a b c : ℝ)
    (hx : 0 ≤ x) (hx1 : x < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ quadraticTailReal x K a b c := by
  have hd : 0 < 1-x := sub_pos.mpr hx1
  unfold quadraticTailReal
  positivity

/-- Exact one-step recurrence, valid without positivity assumptions. -/
lemma quadraticTailReal_step (x : ℝ) (K : ℕ) (a b c : ℝ) (hx : x ≠ 1) :
    quadraticTailReal x K a b c =
      (a*(K:ℝ)^2+b*K+c)*x^K + quadraticTailReal x (K+1) a b c := by
  have hd : 1-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  unfold quadraticTailReal
  rw [pow_succ]
  push_cast
  field_simp
  <;> ring

/-- Finite telescoping identity with its exact terminal correction retained. -/
lemma quadraticTailReal_finite_identity (x : ℝ) (K M : ℕ) (a b c : ℝ)
    (hx : x ≠ 1) (hKM : K ≤ M) :
    (∑ k ∈ Finset.Ico K M, (a*(k:ℝ)^2+b*k+c)*x^k) +
      quadraticTailReal x M a b c = quadraticTailReal x K a b c := by
  induction M, hKM using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
    rw [Finset.sum_Ico_succ_top hKM]
    have hs := quadraticTailReal_step x M a b c hx
    linarith

/-- The original formula bounds any finite horizon, including an empty one. -/
theorem quadraticTailReal_finite_le (x : ℝ) (K M : ℕ) (a b c : ℝ)
    (hx : 0 ≤ x) (hx1 : x < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∑ k ∈ Finset.Ico K M, (a*(k:ℝ)^2+b*k+c)*x^k) ≤
      quadraticTailReal x K a b c := by
  by_cases hKM : K ≤ M
  · have hi := quadraticTailReal_finite_identity x K M a b c (ne_of_lt hx1) hKM
    have hn := quadraticTailReal_nonneg x M a b c hx hx1 ha hb hc
    linarith
  · rw [Finset.Ico_eq_empty_of_le (by omega : M ≤ K)]
    simpa only [Finset.sum_empty] using quadraticTailReal_nonneg x K a b c hx hx1 ha hb hc

/-- Direct client of the kernel-accepted rational closed formula. -/
theorem quadraticTail_finite_le (x : ℚ) (K M : ℕ) (a b c : ℚ)
    (hx : 0 ≤ x) (hx1 : x < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∑ k ∈ Finset.Ico K M, ((a:ℝ)*(k:ℝ)^2+(b:ℝ)*k+(c:ℝ))*(x:ℝ)^k) ≤
      ((quadraticTail x K a b c : ℚ) : ℝ) := by
  rw [quadraticTail_cast]
  apply quadraticTailReal_finite_le
  · exact_mod_cast hx
  · exact_mod_cast hx1
  · exact_mod_cast ha
  · exact_mod_cast hb
  · exact_mod_cast hc

end SubmittedGenus.GoldenTail
