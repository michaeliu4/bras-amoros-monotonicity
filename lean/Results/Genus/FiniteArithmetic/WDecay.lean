import Results.Genus.FiniteArithmetic.WTailBound
import Results.Genus.TailComparison.Scalar
import Mathlib.Data.Nat.Fib.Basic

namespace SubmittedGenus.FiniteArithmetic.Analytic

open PowerSeries
open SubmittedGenus.TailComparison (rStar)
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 2000

/-- The evaluated nonnegative source series, with convergence already proved. -/
theorem capacityW_mass_lt_fifty :
    Summable (fun n => realCoeff capacityW n * rho^n) ∧
    (∑' n, realCoeff capacityW n * rho^n) < 50 := by
  have h := capacityW_summable_and_norm_lt_fifty
  refine ⟨h.1.summable rho_nonneg, ?_⟩
  calc
    (∑' n, realCoeff capacityW n * rho^n) ≤ |∑' n, realCoeff capacityW n * rho^n| := le_abs_self _
    _ ≤ normAt rho capacityW := h.1.abs_tsum_le rho_nonneg
    _ < 50 := h.2

/-- Elementary Fibonacci induction for the submitted lower base 809/500. -/
theorem rStar_pow_le_fib (n : ℕ) (hn : 1 ≤ n) :
    rStar^n ≤ rStar^2 * (Nat.fib n : ℝ) := by
  have hp : 0 < rStar := by norm_num [rStar]
  have hr : rStar^2 ≤ 1 + rStar := by norm_num [rStar]
  have hall : ∀ k : ℕ, rStar^(k+1) ≤ rStar^2 * (Nat.fib (k+1) : ℝ) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => norm_num [rStar]
    | one => simp
    | more k ih0 ih1 =>
      have hrec : Nat.fib (k + 2 + 1) = Nat.fib (k + 1) + Nat.fib (k + 1 + 1) := by
        simpa [Nat.add_assoc] using (Nat.fib_add_two (n := k + 1))
      rw [hrec, Nat.cast_add, mul_add]
      calc
        rStar^(k+2+1) = rStar^(k+1) * rStar^2 := by rw [← pow_add]
        _ ≤ rStar^(k+1) * (1+rStar) := mul_le_mul_of_nonneg_left hr (pow_nonneg hp.le _)
        _ = rStar^(k+1) + rStar^(k+1+1) := by rw [pow_succ]; ring
        _ ≤ _ := add_le_add ih0 ih1
  simpa only [Nat.sub_add_cancel hn] using hall (n - 1)

/-- The original uniform decay estimate, proved for actual W coefficients. -/
theorem original_W_decay (n : ℕ) (hn : 1 ≤ n) :
    realCoeff capacityW n / (Nat.fib n : ℝ) < 50 * rStar^2 / (rho * rStar)^n := by
  have hr : 0 < rStar := by norm_num [rStar]
  have hρ : 0 < rho := by norm_num [rho]
  have hf : 0 < (Nat.fib n : ℝ) := by exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < n))
  apply (div_lt_div_iff₀ hf (pow_pos (mul_pos hρ hr) n)).mpr
  rw [mul_pow]
  calc
    realCoeff capacityW n * (rho^n * rStar^n) =
        (realCoeff capacityW n * rho^n) * rStar^n := by ring
    _ < 50 * rStar^n := mul_lt_mul_of_pos_right (capacityW_weighted_term_lt_fifty n) (pow_pos hr n)
    _ ≤ 50 * (rStar^2 * (Nat.fib n : ℝ)) := mul_le_mul_of_nonneg_left (rStar_pow_le_fib n hn) (by norm_num)
    _ = _ := by ring

/-- Exact rational threshold check at the original joining index 500. -/
theorem original_W_tail_scalar : 50 * rStar^2 / (rho * rStar)^500 < (13 : ℝ) / 1000 := by
  norm_num [rStar, rho]

theorem original_W_sharp_tail (n : ℕ) (hn : 500 ≤ n) :
    realCoeff capacityW n / (Nat.fib n : ℝ) < (13 : ℝ) / 1000 := by
  have hbase : 1 ≤ rho * rStar := by norm_num [rho, rStar]
  have hpow : (rho * rStar)^500 ≤ (rho * rStar)^n := pow_le_pow_right₀ hbase hn
  have hden : 0 < (rho * rStar)^500 := by positivity
  have hnum : 0 ≤ 50 * rStar^2 := by positivity
  exact (original_W_decay n (by omega)).trans_le
    ((div_le_div_of_nonneg_left hnum hden hpow).trans original_W_tail_scalar.le)

#print axioms capacityW_mass_lt_fifty
#print axioms rStar_pow_le_fib
#print axioms original_W_decay
#print axioms original_W_tail_scalar
#print axioms original_W_sharp_tail

end
end SubmittedGenus.FiniteArithmetic.Analytic
