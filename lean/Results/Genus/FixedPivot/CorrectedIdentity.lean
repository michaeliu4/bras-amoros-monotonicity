import Results.Genus.FixedPivot.SourceCancellation
import Results.Genus.FixedPivot.SourceDenominator

/-! The complete original corrected fixed-pivot identity and its actual numerator degree. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators
noncomputable section

/-- The quotient is selected only after actual source divisibility has been proved. -/
def correctedNumerator (r d : ℕ) (hr : 0<r) (hd : 0<d) : Polynomial ℚ :=
  Classical.choose (originalInitialNumerator_divisible hr hd)

lemma correctedNumerator_spec {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    originalInitialNumerator r (r+d) d=sourceL d*correctedNumerator r d hr hd :=
  Classical.choose_spec (originalInitialNumerator_divisible hr hd)

lemma correctedNumerator_natDegree {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    (correctedNumerator r d hr hd).natDegree≤3*d^2+7*(r+d)+6 :=
  original_numerator_degree_descent (by omega) (by omega) _ _
    (correctedNumerator_spec hr hd) (originalInitialNumerator_natDegree (by omega))

def sourceKPolynomial (d : ℕ) : Polynomial ℚ :=
  if Even d then 1+X+2*X^2+X^3-X^5-X^6 else 1+X+X^2

def sourceBPolynomial (d : ℕ) : Polynomial ℚ := sourceKPolynomial d*mixedDenominator X d

lemma sourceE_tau_factor (d : ℕ) :
    sourceE (sourceTau d)=(1-X-X^2)*sourceKPolynomial d := by
  unfold sourceTau sourceKPolynomial
  split_ifs <;> simp only [sourceE,pureDenominator,traceSum,carryB,carryC] <;> ring

/-- The cancelled rational identity for the actual complete fixed-pivot series. -/
theorem fixedPivotSeriesQ_cancelled {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    (((sourceE (sourceTau d)*mixedDenominator X d : Polynomial ℚ)) : PowerSeries ℚ)*
      fixedPivotSeriesQ r (r+d)=(correctedNumerator r d hr hd : PowerSeries ℚ) := by
  have hh:=originalInitialNumerator_identity hr hd
  rw [rationalSourceQ_eval_one hd,correctedNumerator_spec hr hd] at hh
  change ((sourceE d*mixedDenominator X d : Polynomial ℚ) : PowerSeries ℚ)*
    fixedPivotSeriesQ r (r+d)=_ at hh
  rw [sourceE_factor_sourceL,Polynomial.coe_mul,Polynomial.coe_mul,Polynomial.coe_mul] at hh
  apply mul_left_cancel₀ (a := (sourceL d : PowerSeries ℚ))
    (by
      intro h
      apply sourceL_ne_zero hd
      apply Polynomial.coe_injective ℚ
      exact h.trans Polynomial.coe_zero.symm)
  rw [Polynomial.coe_mul]
  calc
    _=((sourceE (sourceTau d) : PowerSeries ℚ)*(sourceL d : PowerSeries ℚ)*
        ((mixedDenominator X d : Polynomial ℚ) : PowerSeries ℚ))*fixedPivotSeriesQ r (r+d) := by ring
    _=_ := hh

/-- Original Proposition raw:correction, including the bound on the actual A. -/
theorem fixedPivotSeriesQ_corrected {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    (sourceBPolynomial d : PowerSeries ℚ)*
      ((1-PowerSeries.X-PowerSeries.X^2)*fixedPivotSeriesQ r (r+d))=
      (correctedNumerator r d hr hd : PowerSeries ℚ) := by
  have hh:=fixedPivotSeriesQ_cancelled hr hd
  rw [sourceE_tau_factor,Polynomial.coe_mul,Polynomial.coe_mul,
    Polynomial.coe_sub,Polynomial.coe_sub,Polynomial.coe_one,Polynomial.coe_X,Polynomial.coe_pow] at hh
  simp only [Polynomial.coe_X] at hh
  change ((1-PowerSeries.X-PowerSeries.X^2)*(sourceKPolynomial d : PowerSeries ℚ)*
    ((mixedDenominator X d : Polynomial ℚ) : PowerSeries ℚ))*fixedPivotSeriesQ r (r+d)=_ at hh
  unfold sourceBPolynomial
  rw [Polynomial.coe_mul]
  calc
    _=((1-PowerSeries.X-PowerSeries.X^2)*(sourceKPolynomial d : PowerSeries ℚ)*
      ((mixedDenominator X d : Polynomial ℚ) : PowerSeries ℚ))*fixedPivotSeriesQ r (r+d) := by ring
    _=_ := hh

lemma sourceBPolynomial_map (d : ℕ) :
    ((sourceBPolynomial d).map (Rat.castHom ℝ) : PowerSeries ℝ)=sourceBSeries d := by
  rw [sourceBPolynomial,Polynomial.map_mul,Polynomial.coe_mul,sourceBSeries,sourceRSeries_eq]
  congr 1
  · unfold sourceKPolynomial sourceKSeries
    split_ifs <;> norm_num [InverseCertificates.K1_original,InverseCertificates.K2_original]
    change Polynomial.coeToPowerSeries.ringHom (2 : Polynomial ℝ)=2
    exact map_ofNat _ _
  · have hm:=map_mixedDenominator (Polynomial.mapRingHom (Rat.castHom ℝ)) (X : Polynomial ℚ) d
    change (mixedDenominator (X : Polynomial ℚ) d).map (Rat.castHom ℝ)=
      mixedDenominator ((X : Polynomial ℚ).map (Rat.castHom ℝ)) d at hm
    rw [Polynomial.map_X] at hm
    exact congrArg (fun p : Polynomial ℝ => (p : PowerSeries ℝ)) hm

def fixedPivotSeriesReal (r p : ℕ) : PowerSeries ℝ :=
  PowerSeries.map (Rat.castHom ℝ) (fixedPivotSeriesQ r p)

def correctedSeries (r p : ℕ) : PowerSeries ℝ :=
  (1-PowerSeries.X-PowerSeries.X^2)*fixedPivotSeriesReal r p

/-- Direct connection to the original K1/K2 and R_d inverse-certificate clients. -/
theorem fixedPivotSeries_real_corrected {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    sourceBSeries d*correctedSeries r (r+d)=
      ((correctedNumerator r d hr hd).map (Rat.castHom ℝ) : PowerSeries ℝ) := by
  have hh:=congrArg (PowerSeries.map (Rat.castHom ℝ)) (fixedPivotSeriesQ_corrected hr hd)
  simp only [map_mul,map_sub,map_one,map_pow,PowerSeries.map_X,
    ← Polynomial.polynomial_map_coe,sourceBPolynomial_map] at hh
  exact hh

end
end SubmittedGenus.FixedPivot
