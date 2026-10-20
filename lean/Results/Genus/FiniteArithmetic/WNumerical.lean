import Results.Genus.FiniteArithmetic.WFinite
import Results.Genus.FiniteArithmetic.WDecay

namespace SubmittedGenus.FiniteArithmetic

open PowerSeries OriginalSources
open Analytic

/-- The submitted sharper bound, including the exact finite-to-infinite join. -/
theorem original_W_sharp_all (n : ℕ) (hn : 141 ≤ n) :
    1000 * coeff n capacityW ≤ 13 * (Nat.fib n : ℤ) := by
  by_cases hfinite : n ≤ 499
  · exact original_W_sharp_finite n hn hfinite
  · have htail := original_W_sharp_tail n (by omega)
    have hf : 0 < (Nat.fib n : ℝ) := by exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < n))
    have h := (div_lt_iff₀ hf).mp htail
    change ((coeff n capacityW : ℤ) : ℝ) < (13 / 1000 : ℝ) * (Nat.fib n : ℝ) at h
    have he : (1000 : ℝ) * ((coeff n capacityW : ℤ) : ℝ) ≤ 13 * (Nat.fib n : ℝ) := by linarith
    exact_mod_cast he

/-- The original 13/25 binary numerical bound holds at every genus. -/
theorem original_W_weak_all (n : ℕ) :
    25 * coeff n capacityW ≤ 13 * (Nat.fib n : ℤ) := by
  by_cases hfinite : n ≤ 499
  · exact original_W_weak_finite n hfinite
  · have h := original_W_sharp_all n (by omega)
    have hp : 0 ≤ coeff n capacityW := by rw [capacityW_source_coeff]; positivity
    omega

/-- Actual W demand fits within the original Fibonacci supply. -/
theorem original_W_le_fib (n : ℕ) : coeff n capacityW ≤ (Nat.fib n : ℤ) := by
  have h := original_W_weak_all n
  have hf : (0 : ℤ) ≤ Nat.fib n := by positivity
  omega

/-- Unconditional population premise for the genuine joint D/I allocation. -/
theorem original_binary_source_capacity (n : ℕ) :
    Fintype.card (SourceClass n .D) + Fintype.card (SourceClass n .I) +
      Fintype.card (SourceClass n .B) ≤ Nat.fib n :=
  original_binary_capacity_of_W n (original_W_le_fib n)

#print axioms original_W_sharp_all
#print axioms original_W_weak_all
#print axioms original_W_le_fib
#print axioms original_binary_source_capacity

end SubmittedGenus.FiniteArithmetic
