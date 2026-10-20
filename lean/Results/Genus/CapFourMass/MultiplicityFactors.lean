import Results.Genus.CapFourMass.NormalizedFeedback
import Results.Genus.CapFourMass.ThreeEvaluation
import Mathlib.Algebra.Field.GeomSum

/-! Exact short and paired mixed multiplicity factors from the submitted source envelope. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

lemma short_multiplicity_sum (p : ℕ) (hp : 2 ≤ p) :
    (∑ j : Fin p, lambdaBound^(p+1+j.val-3)) =
      (lambdaBound^(2*p)-lambdaBound^p)/(lambdaBound^2*(lambdaBound-1)) := by
  have he (j : Fin p) : p+1+j.val-3=(p-2)+j.val := by omega
  simp only [he,pow_add,← Finset.mul_sum]
  have hs : (∑ j : Fin p, lambdaBound^j.val) =
      (lambdaBound^p-1)/(lambdaBound-1) := by
    rw [Fin.sum_univ_eq_sum_range]
    exact geom_sum_eq (ne_of_gt lambdaBound_gt_one) p
  rw [hs]
  have hL : lambdaBound ≠ 0 := ne_of_gt lambdaBound_pos
  have hL1 : lambdaBound-1 ≠ 0 := ne_of_gt (sub_pos.mpr lambdaBound_gt_one)
  have hp2 : p-2+2=p := by omega
  have hpow : lambdaBound^(p-2)*lambdaBound^2=lambdaBound^p := by rw [← pow_add,hp2]
  have hdouble : lambdaBound^(2*p)=lambdaBound^p*lambdaBound^p := by
    rw [show 2*p=p+p by omega,pow_add]
  field_simp
  rw [hdouble]
  linear_combination (lambdaBound^p-1)*hpow

lemma mixed_geometric_factor (d : ℕ) :
    (∑ j ∈ Finset.range d, mixedJ^j)/(1-negativeSquare*mixedJ^d) =
      mixedFactor mixedJ negativeSquare d := by
  have hJ : 1-mixedJ ≠ 0 := ne_of_gt (sub_pos.mpr mixedJ_bounds.2)
  have hsum : (∑ j ∈ Finset.range d, mixedJ^j)=(1-mixedJ^d)/(1-mixedJ) := by
    apply (eq_div_iff hJ).mpr
    exact geom_sum_mul_neg mixedJ d
  rw [hsum,mixedFactor,div_div]

/-- The paired normalized base envelope in the exact original w, not β. -/
lemma mixed_base_pair (p j : ℕ) (hp : 2 ≤ p) :
    normalizer^(2*j)*lambdaBound^(2*p+(2*j+1)-3)+
      normalizer^(2*j)*lambdaBound^(2*p+(2*j+2)-3) =
      (1+lambdaBound)*lambdaBound^(2*p-2)*mixedJ^j := by
  have he1 : 2*p+(2*j+1)-3=(2*p-2)+2*j := by omega
  have he2 : 2*p+(2*j+2)-3=(2*p-2)+2*j+1 := by omega
  rw [he1,he2,pow_add,pow_add,pow_one,mixedJ,← pow_mul,mul_pow]
  ring

lemma actual_mixed_ratio_le (d : ℕ) :
    (normalizer*lam)^(2*d)*rho^2 ≤ mixedJ^d*negativeSquare := by
  have h1 : (normalizer*lam)^(2*d) ≤ mixedJ^d := by
    have hh := pow_le_pow_left₀ (mul_nonneg normalizer_bounds.1.le lam_pos.le)
      (mul_le_mul_of_nonneg_left lam_lt_bound.le normalizer_bounds.1.le) (2*d)
    simpa only [mixedJ,← pow_mul] using hh
  have h2 : rho^2 ≤ negativeSquare := by
    unfold negativeSquare
    exact pow_le_pow_left₀ rho_bounds.1.le rho_bounds.2.le 2
  exact mul_le_mul h1 h2 (sq_nonneg _) (pow_nonneg mixedJ_bounds.1.le _)

lemma mixed_majorant_denominator_pos (d : ℕ) :
    0 < 1-negativeSquare*mixedJ^d := by
  have hp : mixedJ^d ≤ 1 := pow_le_one₀ mixedJ_bounds.1.le mixedJ_bounds.2.le
  have h := mul_le_of_le_one_right negativeSquare_bounds.1.le hp
  linarith [negativeSquare_bounds.2]

lemma actual_mixed_denominator_reciprocal (d : ℕ) :
    1/(1-(normalizer*lam)^(2*d)*rho^2) ≤ 1/(1-negativeSquare*mixedJ^d) := by
  apply one_div_le_one_div_of_le (mixed_majorant_denominator_pos d)
  have h := actual_mixed_ratio_le d
  nlinarith

end SubmittedGenus.CapFourMass
