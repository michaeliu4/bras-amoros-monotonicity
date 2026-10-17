import Results.Genus.FiniteArithmetic.Reservoir.RadiusErrors
import Results.Genus.FiniteArithmetic.WDecay

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries Analytic SubmittedGenus.TailComparison
noncomputable section
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2000

/-- Original scalar threshold, factored into a small exact power check. -/
theorem reservoir_tail_scalar : 78*rStar^2*((800:ℝ)/809)^1500 < 1/10000 := by
  have h100 : ((800:ℝ)/809)^100 ≤ 33/100 := by norm_num
  have hpow := pow_le_pow_left₀ (by positivity : 0≤((800:ℝ)/809)^100) h100 15
  rw [←pow_mul] at hpow
  change ((800:ℝ)/809)^1500≤(33/100)^15 at hpow
  calc
    _ ≤ 78*rStar^2*((33:ℝ)/100)^15 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ < _ := by norm_num [rStar]

/-- The two original finite Fibonacci checks propagate by their exact common
second-order recurrence. -/
theorem fibonacci_main_term (g : ℕ) (hg : 16≤g) :
    18541*Nat.fib g ≤ 10000*(Nat.fib (g+1)+Nat.fib (g-3)) := by
  have hall (n : ℕ) : 18541*Nat.fib (n+16) ≤
      10000*(Nat.fib (n+17)+Nat.fib (n+13)) := by
    induction n using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more n ih0 ih1 =>
      have h1 := Nat.fib_add_two (n:=n+17)
      have h2 := Nat.fib_add_two (n:=n+13)
      have h3 := Nat.fib_add_two (n:=n+16)
      simp only [Nat.add_assoc,Nat.reduceAdd] at h1 h2 h3 ih0 ih1 ⊢
      omega
  have h := hall (g-16)
  have h1 : g-16+16=g := by omega
  have h2 : g-16+17=g+1 := by omega
  have h3 : g-16+13=g-3 := by omega
  simpa only [h1,h2,h3] using h

/-- Generic analytic tail client for the actual nonnegative original error
series once its independently proved mass below 78 is supplied. -/
theorem reservoir_error_tail {S : PowerSeries ℤ} {x : ℝ}
    (hS : PositiveEval radius S x) (hx : x<78) (n : ℕ) (hn : 1500≤n) :
    realCoeff S n/(Nat.fib n : ℝ) < 1/10000 := by
  have hr : 0<rStar := by norm_num [rStar]
  have hρ : 0<radius := by norm_num [radius]
  have hf : 0<(Nat.fib n : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega : 0<n)
  have ht := hS.summable.term_le radius_nonneg n
  have hp : 0≤realCoeff S n := by unfold realCoeff; exact_mod_cast hS.nonnegative n
  change |realCoeff S n| * radius^n≤normAt radius S at ht
  rw [abs_of_nonneg hp,hS.norm] at ht
  have hdec : realCoeff S n/(Nat.fib n : ℝ) < 78*rStar^2/(radius*rStar)^n := by
    apply (div_lt_div_iff₀ hf (pow_pos (mul_pos hρ hr) n)).mpr
    rw [mul_pow]
    calc
      _ = (realCoeff S n*radius^n)*rStar^n := by ring
      _ < 78*rStar^n := mul_lt_mul_of_pos_right (ht.trans_lt hx) (pow_pos hr n)
      _ ≤ 78*(rStar^2*(Nat.fib n : ℝ)) :=
        mul_le_mul_of_nonneg_left (rStar_pow_le_fib n (by omega)) (by norm_num)
      _ = _ := by ring
  have hb : 1≤radius*rStar := by norm_num [radius,rStar]
  have hpow := pow_le_pow_right₀ hb hn
  have hbound : 78*rStar^2/(radius*rStar)^n ≤ 78*rStar^2/(radius*rStar)^1500 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
  have he : 78*rStar^2/(radius*rStar)^1500 = 78*rStar^2*((800:ℝ)/809)^1500 := by
    have hi : (radius*rStar)⁻¹=(800:ℝ)/809 := by norm_num [radius,rStar]
    rw [div_eq_mul_inv,←inv_pow,hi]
  exact hdec.trans_le (hbound.trans (he.le.trans reservoir_tail_scalar.le))

#print axioms reservoir_tail_scalar
#print axioms fibonacci_main_term
#print axioms reservoir_error_tail
end
end SubmittedGenus.FiniteArithmetic.Reservoir
