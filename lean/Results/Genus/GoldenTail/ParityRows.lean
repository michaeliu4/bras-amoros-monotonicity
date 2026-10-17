import Results.Genus.GoldenTail.Multiplier

/-! Exact odd/even grouping in the submitted omitted-pivot formula. -/
namespace SubmittedGenus.GoldenTail
open GoldenSpectral GoldenGraph.Source
open scoped BigOperators
noncomputable section

local notation "R₀" => GoldenSpectral.strongBound
local notation "χ₀" => GoldenSpectral.gapDecay
local notation "t₀" => GoldenSpectral.tiltBound

lemma X_cast : (X : ℝ)=R₀*t₀*χ₀ := by simp only [X,Rat.cast_mul,R_cast,t_cast,chi_cast]
lemma Y_cast : (Y : ℝ)=R₀*t₀^2 := by simp only [Y,Rat.cast_mul,Rat.cast_pow,R_cast,t_cast]
lemma U_cast : (U : ℝ)=1-lowRatio := by
  simp only [U,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,R_cast,t_cast,chi_cast,lowRatio]
lemma V_cast : (V : ℝ)=t₀/χ₀-1 := by
  simp only [V,Rat.cast_sub,Rat.cast_one,Rat.cast_div,t_cast,chi_cast]

lemma pivotRegionBound_odd (k : ℕ) :
    pivotRegionBound (2*k+1)=
      (χ₀*(X : ℝ)^k/(U : ℝ)+t₀*(Y : ℝ)^k/(V : ℝ))/(R₀*t₀^2) := by
  have hJ : (2*k+1-1)/2=k := by omega
  have hs : 2*k+1-k=k+1 := by omega
  simp only [pivotRegionBound,lowPrefactor,highPrefactor,hJ,hs,X_cast,Y_cast,U_cast,V_cast,
    pow_add,mul_pow,pow_mul,pow_one,div_eq_mul_inv,mul_inv_rev]
  ring

lemma pivotRegionBound_even (k : ℕ) :
    pivotRegionBound (2*k+2)=
      (χ₀^2*(X : ℝ)^k/(U : ℝ)+t₀^2*(Y : ℝ)^k/(V : ℝ))/(R₀*t₀^2) := by
  have hJ : (2*k+2-1)/2=k := by omega
  have hs : 2*k+2-k=k+2 := by omega
  simp only [pivotRegionBound,lowPrefactor,highPrefactor,hJ,hs,X_cast,Y_cast,U_cast,V_cast,
    pow_add,mul_pow,pow_mul,div_eq_mul_inv,mul_inv_rev]
  ring

lemma pivotPolynomial_odd (k : ℕ) :
    pivotPolynomial (2*k+1)=12*(k : ℝ)^2+26*k+16 := by
  unfold pivotPolynomial
  push_cast
  ring

lemma pivotPolynomial_even (k : ℕ) :
    pivotPolynomial (2*k+2)=12*(k : ℝ)^2+38*k+32 := by
  unfold pivotPolynomial
  push_cast
  ring

/-- The two quadratic rows are exactly the submitted Po and Pe combination. -/
theorem rowMajorant_pair (k : ℕ) :
    rowMajorant (2*k+1)+rowMajorant (2*k+2)=
      ((((12*chi+12*chi^2 : ℚ) : ℝ)*(k : ℝ)^2+
        ((26*chi+38*chi^2 : ℚ) : ℝ)*k+((16*chi+32*chi^2 : ℚ) : ℝ))*(X : ℝ)^k/(U : ℝ)+
       (((12*t+12*t^2 : ℚ) : ℝ)*(k : ℝ)^2+
        ((26*t+38*t^2 : ℚ) : ℝ)*k+((16*t+32*t^2 : ℚ) : ℝ))*(Y : ℝ)^k/(V : ℝ))/(R₀*t₀^2) := by
  unfold rowMajorant
  rw [pivotPolynomial_odd,pivotPolynomial_even,pivotRegionBound_odd,pivotRegionBound_even]
  push_cast
  rw [chi_cast,t_cast]
  ring

end
end SubmittedGenus.GoldenTail
