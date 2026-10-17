import Results.Genus.FixedPivot.FibonacciConversion

/-! Original-parameter interfaces for the source-exact correction and signed coefficient bounds. -/
namespace SubmittedGenus.FixedPivot
open Polynomial WeightedSeries InverseCertificates
noncomputable section

/-- Original Proposition raw:correction, with original r,p parameters and exact
K_tau R_d certificate denominator. The numerator and its degree are proved. -/
theorem original_fixedPivot_correction {r p : ℕ} (hr : 0<r) (hrp : r<p) :
    ∃ A : Polynomial ℚ,A.natDegree≤3*(p-r)^2+7*p+6 ∧
      sourceBSeries (p-r)*correctedSeries r p=(A.map (Rat.castHom ℝ) : PowerSeries ℝ) := by
  have hd : 0<p-r := Nat.sub_pos_of_lt hrp
  refine ⟨correctedNumerator r (p-r) hr hd,?_,?_⟩
  · simpa only [Nat.add_sub_of_le hrp.le] using correctedNumerator_natDegree hr hd
  · simpa only [Nat.add_sub_of_le hrp.le] using fixedPivotSeries_real_corrected hr hd

/-- Original uniform signed norm bound from an actual per-multiplicity graph-mass bound. -/
theorem original_fixedPivot_norm {r p : ℕ} (hr : 0<r) (hrp : r<p) (B : ℝ)
    (hB : ∀ m,p<m → sourceRawMass m r p≤B) :
    WeightedSummable q (fun n => PowerSeries.coeff n (correctedSeries r p)) ∧
      weightedNorm q (fun n => PowerSeries.coeff n (correctedSeries r p))≤
        420*(3*(p-r)^2+7*p+6 : ℕ)*B := by
  have hd : 0<p-r := Nat.sub_pos_of_lt hrp
  have hb : ∀ m,r+(p-r)<m → sourceRawMass m r (r+(p-r))≤B := by
    simpa only [Nat.add_sub_of_le hrp.le] using hB
  simpa only [Nat.add_sub_of_le hrp.le] using correctedSeries_norm_bound hr hd B hb

lemma fixedPivotSeriesReal_coeff_count (r p g : ℕ) :
    PowerSeries.coeff g (fixedPivotSeriesReal r p)=
      (RawGraph.SignedCounterexample.fixedPivotCoeff r p g : ℝ) := by
  simp [fixedPivotSeriesReal,fixedPivotSeriesQ,RawGraph.SignedCounterexample.fixedPivotSeries]

/-- The submitted signed conversion and numerator bound together, for the actual
raw fixed-pivot coefficient. A source mass envelope is the only analytic premise. -/
theorem original_fixedPivot_coefficient_bound {r p : ℕ} (hr : 0<r) (hrp : r<p) (B : ℝ)
    (hB : ∀ m,p<m → sourceRawMass m r p≤B) (g : ℕ) :
    (RawGraph.SignedCounterexample.fixedPivotCoeff r p g : ℝ)≤
      945*(3*(p-r)^2+7*p+6 : ℕ)*B*(Nat.fib g : ℝ) := by
  obtain ⟨hs,hn⟩:=original_fixedPivot_norm hr hrp B hB
  rw [← fixedPivotSeriesReal_coeff_count]
  calc
    _≤(9/4 : ℝ)*weightedNorm q (fun n => PowerSeries.coeff n (correctedSeries r p))*(Nat.fib g : ℝ) :=
      fixedPivotSeriesReal_fibonacci_bound hr hrp hs g
    _≤(9/4 : ℝ)*(420*(3*(p-r)^2+7*p+6 : ℕ)*B)*(Nat.fib g : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (by positivity)
    _=_ := by push_cast; ring

end
end SubmittedGenus.FixedPivot
