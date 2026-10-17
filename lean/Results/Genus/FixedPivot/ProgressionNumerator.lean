import Results.Genus.FixedPivot.GeometricRationality
import Mathlib.Algebra.Polynomial.BigOperators

/-! Finite initial-data degree of the formal progression numerator. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
noncomputable section
section Ring
variable {R I : Type*} [CommRing R] [Fintype I]

lemma linearModeDenominator_natDegree (rate : R) : (linearModeDenominator rate).natDegree≤1 := by
  unfold linearModeDenominator
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · apply Polynomial.natDegree_mul_le.trans
    simpa only [Polynomial.natDegree_C,zero_add] using (Polynomial.natDegree_X_le (R := R))

lemma modeNumerator_natDegree {d : ℕ} (rates : Fin (d+1)→R) (A : I→R) (index : I→Fin (d+1)) :
    (modeNumerator rates A index).natDegree≤d := by
  classical
  unfold modeNumerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C,zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    (∑ j ∈ Finset.univ.erase (index i),(linearModeDenominator (rates j)).natDegree)≤
        ∑ _j ∈ Finset.univ.erase (index i),1 :=
      Finset.sum_le_sum (fun j _ => linearModeDenominator_natDegree (rates j))
    _ = d := by simp

/-- All coefficients beyond the original d initial phases vanish exactly. -/
theorem finiteModeSeries_numerator_support {d : ℕ} (rates : Fin (d+1)→R) (A : I→R)
    (index : I→Fin (d+1)) {n : ℕ} (hn : d<n) :
    PowerSeries.coeff n ((modeDenominator rates : PowerSeries R)*finiteModeSeries rates A index)=0 := by
  rw [finiteModeSeries_rational,Polynomial.coeff_coe]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt ((modeNumerator_natDegree rates A index).trans_lt hn)

end Ring
end
end SubmittedGenus.FixedPivot
