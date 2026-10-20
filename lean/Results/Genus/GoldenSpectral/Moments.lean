import Results.Genus.GoldenSpectral.CarryModes

/-! Seven exact original golden-q source moments, followed by their rational
bounds. Polynomial quotient identities are checked in Lean's kernel. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.GoldenSpectral
open CapFiveMass.MatrixBounds

def rationalIter (n : ℕ) (v : State→ℝ) : State→ℝ :=
  match n with
  | 0 => v
  | n+1 => rationalTransfer 4 4 *ᵥ rationalIter n v

def rawMoment (n : ℕ) (v w : State→ℝ) : ℝ :=
  ∑ i,radius^(i.val+1)*v i*rationalIter n w i

lemma strong_power_halfScale (n : ℕ) (v : State→ℝ) :
    (strongMatrix^n)*ᵥ halfScale v=halfScale (rationalIter n v) := by
  induction n with
  | zero => simp [rationalIter]
  | succ n ih =>
    rw [pow_succ',← Matrix.mulVec_mulVec,ih]
    exact transfer_halfScale 4 4 _
lemma rawMoment_source (n : ℕ) (v w : State→ℝ) :
    halfScale v ⬝ᵥ ((strongMatrix^n)*ᵥ halfScale w)=rawMoment n v w := by
  rw [strong_power_halfScale,halfScale_dot]
  rfl
lemma dot_div_div (v w : State→ℝ) (c : ℝ) :
    (fun i => v i/c) ⬝ᵥ (fun i => w i/c)=(v ⬝ᵥ w)/(c*c) := by
  simp only [dotProduct,div_mul_div_comm,Finset.sum_div]
lemma plus_moment_eq (n : ℕ) :
    qplus ⬝ᵥ ((strongMatrix^n)*ᵥ qplus)=rawMoment n plusVector plusVector/modeNorm := by
  unfold qplus
  rw [matrix_mulVec_div,dot_div_div,← pow_two,Real.sq_sqrt modeNorm_pos.le,plusRaw,rawMoment_source]
lemma minus_moment_eq (n : ℕ) :
    qminus ⬝ᵥ ((strongMatrix^n)*ᵥ qminus)=rawMoment n minusVector minusVector/modeNorm := by
  unfold qminus
  rw [matrix_mulVec_div,dot_div_div,← pow_two,Real.sq_sqrt modeNorm_pos.le,minusRaw,rawMoment_source]
lemma cross_moment_eq (n : ℕ) :
    qplus ⬝ᵥ ((strongMatrix^n)*ᵥ qminus)=rawMoment n plusVector minusVector/modeNorm := by
  unfold qplus qminus
  rw [matrix_mulVec_div,dot_div_div,← pow_two,Real.sq_sqrt modeNorm_pos.le,plusRaw,minusRaw,rawMoment_source]

set_option maxHeartbeats 1000000 in
lemma alpha_one_polynomial : rawMoment 1 plusVector plusVector=radius^6 + 4*radius^5 + radius^4 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,Fin.sum_univ_succ]
  <;> ring

lemma alpha_one_exact : qplus ⬝ᵥ ((strongMatrix^1)*ᵥ qplus)=7/5 - 6*radius/5 := by
  rw [plus_moment_eq,alpha_one_polynomial]
  apply (div_eq_iff (ne_of_gt modeNorm_pos)).mpr
  unfold modeNorm
  linear_combination (radius^4 + 3*radius^3 + radius^2/5 + 7*radius/5)*radius_relation

set_option maxHeartbeats 1000000 in
lemma alpha_two_polynomial : rawMoment 2 plusVector plusVector=radius^10 + 5*radius^9 + 9*radius^8 + 7*radius^7 + radius^6 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,Fin.sum_univ_succ]
  <;> ring

lemma alpha_two_exact : qplus ⬝ᵥ ((strongMatrix^2)*ᵥ qplus)=7/5 - 6*radius/5 := by
  rw [plus_moment_eq,alpha_two_polynomial]
  apply (div_eq_iff (ne_of_gt modeNorm_pos)).mpr
  unfold modeNorm
  linear_combination (radius^8 + 4*radius^7 + 6*radius^6 + 5*radius^5 + 2*radius^4 + 3*radius^3 + radius^2/5 + 7*radius/5)*radius_relation

set_option maxHeartbeats 1000000 in
lemma omega_one_polynomial : rawMoment 1 plusVector minusVector=-radius^7 - 3*radius^6 - radius^5 + radius^4 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,Fin.sum_univ_succ]
  <;> ring

lemma omega_one_exact : qplus ⬝ᵥ ((strongMatrix^1)*ᵥ qminus)=1/5 - 3*radius/5 := by
  rw [cross_moment_eq,omega_one_polynomial]
  apply (div_eq_iff (ne_of_gt modeNorm_pos)).mpr
  unfold modeNorm
  linear_combination (-radius^5 - 2*radius^4 - 2*radius^2/5 + radius/5)*radius_relation

set_option maxHeartbeats 1000000 in
lemma omega_two_polynomial : rawMoment 2 plusVector minusVector=-radius^11 - 4*radius^10 - 6*radius^9 - 4*radius^8 + 2*radius^7 + 2*radius^6 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,Fin.sum_univ_succ]
  <;> ring

lemma omega_two_exact : qplus ⬝ᵥ ((strongMatrix^2)*ᵥ qminus)=11/5 - 18*radius/5 := by
  rw [cross_moment_eq,omega_two_polynomial]
  apply (div_eq_iff (ne_of_gt modeNorm_pos)).mpr
  unfold modeNorm
  linear_combination (-radius^9 - 3*radius^8 - 4*radius^7 - 3*radius^6 + radius^5 - 2*radius^4 + 3*radius^3 - 7*radius^2/5 + 11*radius/5)*radius_relation

set_option maxHeartbeats 1000000 in
lemma beta_one_polynomial : rawMoment 1 minusVector minusVector=radius^8 + 2*radius^7 + radius^6 - 2*radius^5 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,Fin.sum_univ_succ]
  <;> ring

lemma beta_one_exact : qminus ⬝ᵥ ((strongMatrix^1)*ᵥ qminus)=11*radius/5 - 7/5 := by
  rw [minus_moment_eq,beta_one_polynomial]
  apply (div_eq_iff (ne_of_gt modeNorm_pos)).mpr
  unfold modeNorm
  linear_combination (radius^6 + radius^5 + radius^4 - 2*radius^3 + 4*radius^2/5 - 7*radius/5)*radius_relation

set_option maxHeartbeats 1000000 in
lemma beta_two_polynomial : rawMoment 2 minusVector minusVector=radius^12 + 3*radius^11 + 4*radius^10 + 2*radius^9 - 3*radius^8 - 2*radius^7 + radius^6 + radius^5 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,Fin.sum_univ_succ]
  <;> ring

lemma beta_two_exact : qminus ⬝ᵥ ((strongMatrix^2)*ᵥ qminus)=3/5 - 4*radius/5 := by
  rw [minus_moment_eq,beta_two_polynomial]
  apply (div_eq_iff (ne_of_gt modeNorm_pos)).mpr
  unfold modeNorm
  linear_combination (radius^10 + 2*radius^9 + 3*radius^8 + radius^7 - radius^6 + radius^3 - radius^2/5 + 3*radius/5)*radius_relation

set_option maxHeartbeats 1000000 in
lemma beta_four_polynomial : rawMoment 4 minusVector minusVector=radius^20 + 5*radius^19 + 13*radius^18 + 23*radius^17 + 28*radius^16 + 20*radius^15 + radius^14 - 14*radius^13 - 11*radius^12 + 3*radius^10 + radius^9 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,Fin.sum_univ_succ]
  <;> ring

lemma beta_four_exact : qminus ⬝ᵥ ((strongMatrix^4)*ᵥ qminus)=293*radius/5 - 181/5 := by
  rw [minus_moment_eq,beta_four_polynomial]
  apply (div_eq_iff (ne_of_gt modeNorm_pos)).mpr
  unfold modeNorm
  linear_combination (radius^18 + 4*radius^17 + 10*radius^16 + 17*radius^15 + 21*radius^14 + 16*radius^13 + 6*radius^12 - 4*radius^11 - radius^10 - 3*radius^9 + 5*radius^8 - 7*radius^7 + 12*radius^6 - 19*radius^5 + 31*radius^4 - 50*radius^3 + 112*radius^2/5 - 181*radius/5)*radius_relation

lemma alpha_one_bound : |qplus ⬝ᵥ ((strongMatrix^1)*ᵥ qplus)|<823/1250 := by
  rw [alpha_one_exact,abs_lt]
  constructor <;> linarith [radius_lower,radius_upper]

lemma alpha_two_bound : |qplus ⬝ᵥ ((strongMatrix^2)*ᵥ qplus)|<823/1250 := by
  rw [alpha_two_exact,abs_lt]
  constructor <;> linarith [radius_lower,radius_upper]

lemma omega_one_bound : |qplus ⬝ᵥ ((strongMatrix^1)*ᵥ qminus)|<171/1000 := by
  rw [omega_one_exact,abs_lt]
  constructor <;> linarith [radius_lower,radius_upper]

lemma omega_two_bound : |qplus ⬝ᵥ ((strongMatrix^2)*ᵥ qminus)|<1/40 := by
  rw [omega_two_exact,abs_lt]
  constructor <;> linarith [radius_lower,radius_upper]

lemma beta_one_bound : |qminus ⬝ᵥ ((strongMatrix^1)*ᵥ qminus)|<41/1000 := by
  rw [beta_one_exact,abs_lt]
  constructor <;> linarith [radius_lower,radius_upper]

lemma beta_two_bound : |qminus ⬝ᵥ ((strongMatrix^2)*ᵥ qminus)|<66/625 := by
  rw [beta_two_exact,abs_lt]
  constructor <;> linarith [radius_lower,radius_upper]

lemma beta_four_bound : |qminus ⬝ᵥ ((strongMatrix^4)*ᵥ qminus)|<17/1000 := by
  rw [beta_four_exact,abs_lt]
  constructor <;> linarith [radius_lower,radius_upper]

end SubmittedGenus.GoldenSpectral
