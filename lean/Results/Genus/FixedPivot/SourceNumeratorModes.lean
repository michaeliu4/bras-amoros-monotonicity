import Results.Genus.FixedPivot.PolynomialRationality
import Results.Genus.FixedPivot.PhaseGenerating
import Results.Genus.FixedPivot.ModeEndpoints

/-! Actual finite initial numerators identified with their signed mode numerators. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators
noncomputable section

lemma polynomialProgressionNumerator_map {r N d : ℕ}
    (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : r+2*d<N) :
    (polynomialProgressionNumerator r N d).map sourceEmbedding=
      modeNumerator (sourceRates sourceLambda sourceMu d)
        (sourceModeCoefficient (r := r) hN sourceZ sourceLambda sourceMu
          sourceLambdaInverse sourceMuInverse sourceDifferenceInverse)
        (fun pair => sourceModeIndex hN pair.2) := by
  apply Polynomial.coe_injective SourceQuadratic
  rw [Polynomial.polynomial_map_coe,← polynomialProgressionSeries_rational hr hd hN hbig,
    map_mul,← Polynomial.polynomial_map_coe,rationalSourceQ_map,polynomialProgressionSeries_map]
  rw [sourceProgressionSeries_modes hr hd hN hbig sourceZ sourceLambda sourceMu
    sourceLambdaInverse sourceMuInverse sourceDifferenceInverse source_roots_sum source_roots_product
    source_lambda_inverse source_mu_inverse source_difference_inverse,
    ← sourceRates_denominator sourceZ sourceLambda sourceMu source_roots_sum source_roots_product]
  exact finiteModeSeries_rational _ _ _

def phaseModeNumerator (r d k : ℕ) : Polynomial SourceQuadratic :=
  modeNumerator (sourceRates sourceLambda sourceMu d)
    (sourceModeCoefficient (r := r) (show d<r+2*d+1+k by omega) sourceZ sourceLambda sourceMu
      sourceLambdaInverse sourceMuInverse sourceDifferenceInverse)
    (fun pair => sourceModeIndex (show d<r+2*d+1+k by omega) pair.2)

/-- Finite mode numerators are exactly the original source initial-data numerators. -/
theorem phaseInitialNumerator_modes {r d : ℕ} (hr : 0<r) (hd : 0<d) (k : ℕ) :
    sourceEmbedding (phaseInitialNumerator r (r+d) d (k+1))=
      Polynomial.eval 1 (phaseModeNumerator r d k) := by
  rw [← phaseNumerator_eq,show r+2*d+(k+1)=r+2*d+1+k by omega]
  have hm:=Polynomial.eval_map_apply (f := sourceEmbedding)
    (p := polynomialProgressionNumerator r (r+2*d+1+k) d) (1 : Polynomial ℚ)
  rw [map_one] at hm
  rw [← hm,polynomialProgressionNumerator_map hr hd (by omega) (by omega)]
  rfl

end
end SubmittedGenus.FixedPivot
