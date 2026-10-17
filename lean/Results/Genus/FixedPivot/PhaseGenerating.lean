import Results.Genus.FixedPivot.PolynomialRationality
import Results.Genus.FixedPivot.FiniteEvaluation

/-! Exact y=1 identities for each original multiplicity phase. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators PowerSeries.WithPiTopology
noncomputable section

lemma phaseNumerator_eq {r d s : ℕ} :
    Polynomial.eval (1 : Polynomial ℚ) (polynomialProgressionNumerator r (r+2*d+s) d)=
      phaseInitialNumerator r (r+d) d s := by
  rw [polynomialProgressionNumerator_eval_one]
  unfold phaseInitialNumerator
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  omega

/-- A phase identity for the actual genus polynomials, with all formal
specialization and local finiteness obligations discharged. -/
theorem phaseInitialNumerator_identity {r d s : ℕ} (hr : 0<r) (hd : 0<d) (hs : 0<s) :
    ((Polynomial.eval (1 : Polynomial ℚ) (rationalSourceQ d) : Polynomial ℚ) : PowerSeries ℚ)*
      locallyFinitePolynomialSum (fun k => rawPolynomialQ (2*(r+d)+s+k*d) r (r+d))=
      (phaseInitialNumerator r (r+d) d s : PowerSeries ℚ) := by
  have hN : d<r+2*d+s := by omega
  have hbig : r+2*d<r+2*d+s := by omega
  have he : (fun k => rawPolynomialQ (r+(r+2*d+s+k*d)) r (r+d))=
      (fun k => rawPolynomialQ (2*(r+d)+s+k*d) r (r+d)) := by
    funext k
    congr 1
    omega
  have hidentity:=polynomialProgressionSeries_rational hr hd hN hbig
  change (rationalSourceQ d : PowerSeries (Polynomial ℚ))*
    PowerSeries.mk (fun k => rawPolynomialQ (r+(r+2*d+s+k*d)) r (r+d))=_ at hidentity
  rw [he] at hidentity
  have hc : ∀ n k,n<k → (rawPolynomialQ (2*(r+d)+s+k*d) r (r+d)).coeff n=0 := by
    intro n k hnk
    have hk : k≤k*d := Nat.le_mul_of_pos_right k hd
    simp only [rawPolynomialQ,Polynomial.coeff_map]
    rw [RawGraph.SignedCounterexample.coeff_zero_of_multiplicity (by omega),map_zero]
  have hh:=evaluate_formal_rational (rationalSourceQ d)
    (polynomialProgressionNumerator r (r+2*d+s) d) _ _ hc
    (rawProgression_hasSum (2*(r+d)+s) r (r+d) d hd) hidentity
  rw [phaseNumerator_eq] at hh
  exact hh

end
end SubmittedGenus.FixedPivot
