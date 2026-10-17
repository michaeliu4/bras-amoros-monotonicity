import Results.Genus.GoldenTail.ParityRows
import Results.Genus.GoldenTail.ParityIntervals

/-! The entire original omitted-pivot coefficient multiplier is bounded by
its exact submitted quadratic geometric-tail expression at every finite horizon. -/
namespace SubmittedGenus.GoldenTail
open GoldenSpectral GoldenGraph.Source
open scoped BigOperators
noncomputable section

local notation "R₀" => GoldenSpectral.strongBound
local notation "χ₀" => GoldenSpectral.gapDecay
local notation "t₀" => GoldenSpectral.tiltBound

def rowTailBound (K : ℕ) : ℝ :=
  (((quadraticTail X K (12*chi+12*chi^2) (26*chi+38*chi^2) (16*chi+32*chi^2) / U +
     quadraticTail Y K (12*t+12*t^2) (26*t+38*t^2) (16*t+32*t^2) / V : ℚ) : ℝ))/(R₀*t₀^2)

/-- The exact quadratic formula bounds every finite collection of omitted
parity rows, including incomplete last pairs and empty horizons. -/
theorem rowMajorant_sum_le (K N : ℕ) :
    (∑ p ∈ Finset.Ico (2*K+1) N,rowMajorant p)≤rowTailBound K := by
  have hx:=quadraticTail_finite_le X K N (12*chi+12*chi^2) (26*chi+38*chi^2) (16*chi+32*chi^2)
    X_pos.le (X_lt_Y.trans Y_lt_one) (by norm_num [chi]) (by norm_num [chi]) (by norm_num [chi])
  have hy:=quadraticTail_finite_le Y K N (12*t+12*t^2) (26*t+38*t^2) (16*t+32*t^2)
    (X_pos.trans X_lt_Y).le Y_lt_one (by norm_num [t]) (by norm_num [t]) (by norm_num [t])
  have hu : 0≤(U : ℝ) := by exact_mod_cast U_pos.le
  have hv : 0≤(V : ℝ) := by exact_mod_cast V_pos.le
  have hd : 0≤R₀*t₀^2 := mul_nonneg strongBound_pos.le (sq_nonneg _)
  apply (sum_Ico_le_odd_even rowMajorant K N rowMajorant_nonneg).trans
  calc
    _=((∑ k ∈ Finset.Ico K N,
        (((12*chi+12*chi^2 : ℚ) : ℝ)*(k : ℝ)^2+
        ((26*chi+38*chi^2 : ℚ) : ℝ)*k+((16*chi+32*chi^2 : ℚ) : ℝ))*(X : ℝ)^k)/(U : ℝ)+
       (∑ k ∈ Finset.Ico K N,
        (((12*t+12*t^2 : ℚ) : ℝ)*(k : ℝ)^2+
        ((26*t+38*t^2 : ℚ) : ℝ)*k+((16*t+32*t^2 : ℚ) : ℝ))*(Y : ℝ)^k)/(V : ℝ))/(R₀*t₀^2) := by
      simp_rw [rowMajorant_pair]
      simp only [div_eq_mul_inv,add_mul,Finset.sum_mul,Finset.sum_add_distrib]
    _≤rowTailBound K := by
      unfold rowTailBound
      push_cast at hx hy ⊢
      exact div_le_div_of_nonneg_right
        (add_le_add (div_le_div_of_nonneg_right hx hu) (div_le_div_of_nonneg_right hy hv)) hd

lemma rowTailBound_nonneg (K : ℕ) : 0≤rowTailBound K := by
  have h:=rowMajorant_sum_le K K
  simpa only [Finset.Ico_eq_empty_of_le (show K≤2*K+1 by omega),Finset.sum_empty] using h

lemma upperPrefactor_mul_rowTail (K : ℕ) : upperPrefactor*rowTailBound K=(B K : ℝ) := by
  unfold upperPrefactor rowTailBound B
  push_cast
  rw [k0_cast,chi_cast,R_cast,t_cast]
  ring

/-- Complete original geometric majorant before numerical substitution. This
is a theorem about the actual source-derived coefficient multiplier. -/
theorem coefficientMultiplier_sum_le_B (K N : ℕ) :
    (∑ p ∈ Finset.Ico (2*K+1) N,∑ r ∈ Finset.Ico 1 p,coefficientMultiplier r p)≤(B K : ℝ) := by
  calc
    _≤∑ p ∈ Finset.Ico (2*K+1) N,coefficientPrefactor*rowMajorant p := by
      apply Finset.sum_le_sum
      intro p hp
      exact coefficientMultiplier_row p (by have:=(Finset.mem_Ico.mp hp).1; omega)
    _=coefficientPrefactor*∑ p ∈ Finset.Ico (2*K+1) N,rowMajorant p := (Finset.mul_sum _ _ _).symm
    _≤coefficientPrefactor*rowTailBound K :=
      mul_le_mul_of_nonneg_left (rowMajorant_sum_le K N) coefficientPrefactor_nonneg
    _≤upperPrefactor*rowTailBound K :=
      mul_le_mul_of_nonneg_right coefficientPrefactor_le_upper (rowTailBound_nonneg K)
    _=(B K : ℝ) := upperPrefactor_mul_rowTail K

/-- Literal original 221715/10^6 omitted-pivot bound, valid at every horizon. -/
theorem omitted_multiplier_sum_le (N : ℕ) :
    (∑ p ∈ Finset.Ico 301 N,∑ r ∈ Finset.Ico 1 p,coefficientMultiplier r p)≤(221715 : ℝ)/1000000 := by
  have h:=coefficientMultiplier_sum_le_B 150 N
  apply h.trans
  simpa only [show (10 : ℝ)^6=1000000 by norm_num] using B150_cast_lt.le

/-- The multiplier is already proved for the actual raw fixed-pivot source. -/
theorem coefficientMultiplier_source_bound (g p r : ℕ) (hr : 1≤r) (hrp : r<p) :
    (RawGraph.SignedCounterexample.fixedPivotCoeff r p g : ℝ)≤coefficientMultiplier r p*(Nat.fib g : ℝ) :=
  fixedPivotCoeff_le_uniform hr hrp g

end
end SubmittedGenus.GoldenTail
