import Results.Genus.FiniteArithmetic.Reservoir.ActualMass
import Results.Genus.FiniteArithmetic.Reservoir.NumericalTail
import Results.Genus.FiniteArithmetic.BinaryWords

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries Analytic OriginalReservoir
noncomputable section
attribute [local instance] Classical.propDecidable

theorem binaryTailSeries_coeff (g : ℕ) : coeff g binaryTailSeries=(Nat.fib (g+1):ℤ) := by
  rw [binaryTailSeries,Graded.coeff_series]
  have h : Fintype.card (BinaryTailSource g)=Fintype.card (BinaryWords g) :=
    Fintype.card_congr (Equiv.refl _)
  rw [h,binaryWords_card]

theorem earlyGain_coeff_nonneg (g : ℕ) : 0≤coeff g earlyGainSeries := by
  have hx : PositiveEval radius (X : PowerSeries ℤ) radius := by simpa using positiveEval_xpow radius 1
  have hU := wU_evaluates unitDecoration 1 unit_decoration_evaluates (Or.inl rfl) 0 (by omega)
  have hUU := wUU_evaluates unitDecoration 1 unit_decoration_evaluates (Or.inl rfl) 0 (by omega)
  have h2 := positiveEval_nat radius 2
  have h := (((positiveEval_xpow radius 9).mul radius_nonneg
    ((h2.add radius_nonneg (h2.mul radius_nonneg hx)).add radius_nonneg
      (positiveEval_xpow radius 2))).mul radius_nonneg hU).mul radius_nonneg hUU
  exact h.nonnegative g

theorem nonbinary_unclipped_le (g : ℕ) :
    coeff g safeCandidateSeries+coeff g earlyCandidateSeries-
      coeff g (actualFailureSeries safeFamily)-coeff g (actualFailureSeries earlyFamily) ≤
        (nonbinaryLowerBound g : ℤ) := by
  rw [safeCandidateSeries_coeff,earlyCandidateSeries_coeff,actualFailureSeries_coeff,actualFailureSeries_coeff]
  dsimp only [SafeBaseAt,EarlyBaseAt]
  have hs := familyLowerBound_eq_clip safeFamily g
  have he := familyLowerBound_eq_clip earlyFamily g
  simp only [nonbinaryLowerBound,Nat.cast_add]
  omega

/-- The two actual separately clipped families dominate the original
Fibonacci main terms minus the actual error coefficients. -/
theorem nonbinary_main_term (g : ℕ) (hg : 4≤g) :
    (Nat.fib (g+1):ℤ)+Nat.fib (g-3)-coeff g actualErrorSeries ≤ (nonbinaryLowerBound g:ℤ) := by
  have hs := congrArg (coeff g) safe_candidate_error_identity
  have he := congrArg (coeff g) early_candidate_error_identity
  rw [map_add,binaryTailSeries_coeff] at hs
  rw [map_add,map_add,coeff_X_pow_mul',if_pos hg,binaryTailSeries_coeff] at he
  have hi : g-4+1=g-3 := by omega
  rw [hi] at he
  have hgain := earlyGain_coeff_nonneg g
  have hl := nonbinary_unclipped_le g
  simp only [actualErrorSeries,map_add]
  omega

/-- Original nonbinary capacity for the complete infinite tail. -/
theorem original_nonbinary_tail (g : ℕ) (hg : 1500≤g) :
    927*Nat.fib g ≤ 500*nonbinaryLowerBound g := by
  have herror := reservoir_error_tail actual_error_evaluates totalErrorValue_lt_seventy_eight g hg
  have hf : 0<(Nat.fib g:ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega : 0<g)
  have hscaled : (10000:ℝ)*realCoeff actualErrorSeries g < (Nat.fib g:ℝ) := by
    have h := (div_lt_iff₀ hf).mp herror
    linarith
  have herrorZ : (10000:ℤ)*coeff g actualErrorSeries < (Nat.fib g:ℤ) := by
    unfold realCoeff at hscaled
    exact_mod_cast hscaled
  have hfibZ : (18541:ℤ)*(Nat.fib g:ℤ) ≤
      10000*((Nat.fib (g+1):ℤ)+(Nat.fib (g-3):ℤ)) := by
    exact_mod_cast fibonacci_main_term g (by omega)
  have hl := nonbinary_main_term g (by omega)
  have hz : (927:ℤ)*(Nat.fib g:ℤ) ≤ 500*(nonbinaryLowerBound g:ℤ) := by omega
  exact_mod_cast hz

#print axioms nonbinary_main_term
#print axioms original_nonbinary_tail
end
end SubmittedGenus.FiniteArithmetic.Reservoir
