import Results.Genus.CapFourMass.CarrySpectrum

/-!
# Finite source-matrix moment certificates

Every moment below is evaluated on the actual four-state strong transfer.
The seven submitted rational moment bounds are deduced from exact polynomial
identities and a proved rational enclosure for the positive carry root.
-/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

def rationalIter (n : ℕ) (v : State → ℝ) : State → ℝ :=
  match n with
  | 0 => v
  | n+1 => rationalTransfer 4 4 *ᵥ rationalIter n v

def rawMoment (n : ℕ) (v w : State → ℝ) : ℝ :=
  ∑ i, radius^(i.val+1)*v i*rationalIter n w i

lemma strong_power_halfScale (n : ℕ) (v : State → ℝ) :
    (strongMatrix^n) *ᵥ halfScale v = halfScale (rationalIter n v) := by
  induction n with
  | zero => simp [rationalIter]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    exact transfer_halfScale 4 4 _

lemma rawMoment_source (n : ℕ) (v w : State → ℝ) :
    halfScale v ⬝ᵥ ((strongMatrix^n) *ᵥ halfScale w) = rawMoment n v w := by
  rw [strong_power_halfScale, halfScale_dot]
  rfl

lemma mulVec_div (A : Matrix State State ℝ) (v : State → ℝ) (c : ℝ) :
    A *ᵥ (fun i => v i/c) = fun i => (A *ᵥ v) i/c := by
  funext i
  simp only [Matrix.mulVec, dotProduct, mul_div_assoc, Finset.sum_div]

lemma dot_div_div (v w : State → ℝ) (c d : ℝ) :
    (fun i => v i/c) ⬝ᵥ (fun i => w i/d) = (v ⬝ᵥ w)/(c*d) := by
  simp only [dotProduct, div_mul_div_comm, Finset.sum_div]

lemma plus_moment_eq (n : ℕ) :
    qplus ⬝ᵥ ((strongMatrix^n) *ᵥ qplus) = rawMoment n plusVector plusVector/plusNorm := by
  unfold qplus
  rw [mulVec_div,dot_div_div,← pow_two,Real.sq_sqrt plusNorm_pos.le]
  rw [plusRaw,rawMoment_source]

lemma minus_moment_eq (n : ℕ) :
    qminus ⬝ᵥ ((strongMatrix^n) *ᵥ qminus) = rawMoment n minusVector minusVector/minusNorm := by
  unfold qminus
  rw [mulVec_div,dot_div_div,← pow_two,Real.sq_sqrt minusNorm_pos.le]
  rw [minusRaw,rawMoment_source]

lemma cross_moment_eq (n : ℕ) :
    qplus ⬝ᵥ ((strongMatrix^n) *ᵥ qminus) =
      rawMoment n plusVector minusVector/(Real.sqrt plusNorm*Real.sqrt minusNorm) := by
  unfold qplus qminus
  rw [mulVec_div,dot_div_div,plusRaw,minusRaw,rawMoment_source]

set_option maxHeartbeats 1000000 in
lemma alpha_one_polynomial : rawMoment 1 plusVector plusVector =
    ((12209025744185655022063 : ℝ)/64000000000000000000000)*lam^1 + ((25493554436900893729 : ℝ)/64000000000000000000)*lam^2 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,carryA,carryB,radius,Fin.sum_univ_succ]
  <;> ring

lemma alpha_one_raw_bound : |rawMoment 1 plusVector plusVector| < 61/100 := by
  rw [alpha_one_polynomial,abs_lt]
  have hq := lam_quadratic
  have hlo := lam_bounds.1
  have hhi := lam_bounds.2
  norm_num [carryA,carryB,radius] at hq
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
lemma alpha_two_polynomial : rawMoment 2 plusVector plusVector =
    ((249600210449816713332330622568245319441 : ℝ)/4096000000000000000000000000000000000000)*lam^0 + ((200160553688706265703553025315353103 : ℝ)/1024000000000000000000000000000000000)*lam^1 + ((356595201498942455973984487236049 : ℝ)/1024000000000000000000000000000000)*lam^2 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,carryA,carryB,radius,Fin.sum_univ_succ]
  <;> ring

lemma alpha_two_raw_bound : |rawMoment 2 plusVector plusVector| < 621/1000 := by
  rw [alpha_two_polynomial,abs_lt]
  have hq := lam_quadratic
  have hlo := lam_bounds.1
  have hhi := lam_bounds.2
  norm_num [carryA,carryB,radius] at hq
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
lemma omega_one_polynomial : rawMoment 1 plusVector minusVector =
    ((-15224655102999511812512561 : ℝ)/256000000000000000000000000)*lam^0 + ((-31790462382815414480063 : ℝ)/128000000000000000000000)*lam^1 + ((2418052990081 : ℝ)/16000000000000)*lam^2 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,carryA,carryB,radius,Fin.sum_univ_succ]
  <;> ring

lemma omega_one_raw_bound : |rawMoment 1 plusVector minusVector| < 4/25 := by
  rw [omega_one_polynomial,abs_lt]
  have hq := lam_quadratic
  have hlo := lam_bounds.1
  have hhi := lam_bounds.2
  norm_num [carryA,carryB,radius] at hq
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
lemma omega_two_polynomial : rawMoment 2 plusVector minusVector =
    ((-249600210449816713332330622568245319441 : ℝ)/4096000000000000000000000000000000000000)*lam^0 + ((-246936395791423583178645513315353103 : ℝ)/2048000000000000000000000000000000000)*lam^1 + ((39642706591370821856638561 : ℝ)/256000000000000000000000000)*lam^2 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,carryA,carryB,radius,Fin.sum_univ_succ]
  <;> ring

lemma omega_two_raw_bound : |rawMoment 2 plusVector minusVector| < 13/500 := by
  rw [omega_two_polynomial,abs_lt]
  have hq := lam_quadratic
  have hlo := lam_bounds.1
  have hhi := lam_bounds.2
  norm_num [carryA,carryB,radius] at hq
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
lemma nu_one_polynomial : rawMoment 1 minusVector minusVector =
    ((39642706591370821856638561 : ℝ)/256000000000000000000000000)*lam^0 + ((-3015312078631007 : ℝ)/16000000000000000)*lam^1 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,carryA,carryB,radius,Fin.sum_univ_succ]
  <;> ring

lemma nu_one_raw_bound : |rawMoment 1 minusVector minusVector| < 1/25 := by
  rw [nu_one_polynomial,abs_lt]
  have hq := lam_quadratic
  have hlo := lam_bounds.1
  have hhi := lam_bounds.2
  norm_num [carryA,carryB,radius] at hq
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
lemma nu_two_polynomial : rawMoment 2 minusVector minusVector =
    ((554508747687669009521649643512441319441 : ℝ)/4096000000000000000000000000000000000000)*lam^0 + ((-49434455119439414855228285567 : ℝ)/256000000000000000000000000000)*lam^1 + ((9790718319314879729 : ℝ)/64000000000000000000)*lam^2 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,carryA,carryB,radius,Fin.sum_univ_succ]
  <;> ring

lemma nu_two_raw_bound : |rawMoment 2 minusVector minusVector| < 489/5000 := by
  rw [nu_two_polynomial,abs_lt]
  have hq := lam_quadratic
  have hlo := lam_bounds.1
  have hhi := lam_bounds.2
  norm_num [carryA,carryB,radius] at hq
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
lemma nu_four_polynomial : rawMoment 4 minusVector minusVector =
    ((121009748861586034214678685200039492451811131160842746027791564401 : ℝ)/1048576000000000000000000000000000000000000000000000000000000000000)*lam^0 + ((-12041795380971928320170921984830412992785874456355949087 : ℝ)/65536000000000000000000000000000000000000000000000000000)*lam^1 + ((1386531415450625890911516599342205863702629969 : ℝ)/16384000000000000000000000000000000000000000000)*lam^2 := by
  norm_num [rawMoment,rationalIter,rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,minusVector,carryA,carryB,radius,Fin.sum_univ_succ]
  <;> ring

lemma nu_four_raw_bound : |rawMoment 4 minusVector minusVector| < 17/1000 := by
  rw [nu_four_polynomial,abs_lt]
  have hq := lam_quadratic
  have hlo := lam_bounds.1
  have hhi := lam_bounds.2
  norm_num [carryA,carryB,radius] at hq
  constructor <;> nlinarith

lemma alpha_one_bound : |qplus ⬝ᵥ ((strongMatrix^1) *ᵥ qplus)| < 68/100 := by
  rw [plus_moment_eq,abs_div,abs_of_pos plusNorm_pos]
  apply (div_lt_iff₀ plusNorm_pos).mpr
  have h := alpha_one_raw_bound
  have hn := plusNorm_lower
  nlinarith

lemma alpha_two_bound : |qplus ⬝ᵥ ((strongMatrix^2) *ᵥ qplus)| < 69/100 := by
  rw [plus_moment_eq,abs_div,abs_of_pos plusNorm_pos]
  apply (div_lt_iff₀ plusNorm_pos).mpr
  have h := alpha_two_raw_bound
  have hn := plusNorm_lower
  nlinarith

lemma nu_one_bound : |qminus ⬝ᵥ ((strongMatrix^1) *ᵥ qminus)| < 5/100 := by
  rw [minus_moment_eq,abs_div,abs_of_pos minusNorm_pos]
  apply (div_lt_iff₀ minusNorm_pos).mpr
  have h := nu_one_raw_bound
  have hn := minusNorm_lower
  nlinarith

lemma nu_two_bound : |qminus ⬝ᵥ ((strongMatrix^2) *ᵥ qminus)| < 11/100 := by
  rw [minus_moment_eq,abs_div,abs_of_pos minusNorm_pos]
  apply (div_lt_iff₀ minusNorm_pos).mpr
  have h := nu_two_raw_bound
  have hn := minusNorm_lower
  nlinarith

lemma nu_four_bound : |qminus ⬝ᵥ ((strongMatrix^4) *ᵥ qminus)| < 2/100 := by
  rw [minus_moment_eq,abs_div,abs_of_pos minusNorm_pos]
  apply (div_lt_iff₀ minusNorm_pos).mpr
  have h := nu_four_raw_bound
  have hn := minusNorm_lower
  nlinarith

lemma omega_one_bound : |qplus ⬝ᵥ ((strongMatrix^1) *ᵥ qminus)| < 18/100 := by
  rw [cross_moment_eq,abs_div,abs_of_pos (mul_pos
    (Real.sqrt_pos.mpr plusNorm_pos) (Real.sqrt_pos.mpr minusNorm_pos))]
  apply (div_lt_iff₀ (mul_pos (Real.sqrt_pos.mpr plusNorm_pos)
    (Real.sqrt_pos.mpr minusNorm_pos))).mpr
  have h := omega_one_raw_bound
  have hn := mul_lt_mul plusNorm_lower minusNorm_lower.le (by norm_num) plusNorm_pos.le
  have hs : (Real.sqrt plusNorm*Real.sqrt minusNorm)^2 = plusNorm*minusNorm := by
    rw [mul_pow,Real.sq_sqrt plusNorm_pos.le,Real.sq_sqrt minusNorm_pos.le]
  have hd : 0 < Real.sqrt plusNorm*Real.sqrt minusNorm :=
    mul_pos (Real.sqrt_pos.mpr plusNorm_pos) (Real.sqrt_pos.mpr minusNorm_pos)
  nlinarith [sq_abs (rawMoment 1 plusVector minusVector),
    abs_nonneg (rawMoment 1 plusVector minusVector)]

lemma omega_two_bound : |qplus ⬝ᵥ ((strongMatrix^2) *ᵥ qminus)| < 3/100 := by
  rw [cross_moment_eq,abs_div,abs_of_pos (mul_pos
    (Real.sqrt_pos.mpr plusNorm_pos) (Real.sqrt_pos.mpr minusNorm_pos))]
  apply (div_lt_iff₀ (mul_pos (Real.sqrt_pos.mpr plusNorm_pos)
    (Real.sqrt_pos.mpr minusNorm_pos))).mpr
  have h := omega_two_raw_bound
  have hn := mul_lt_mul plusNorm_lower minusNorm_lower.le (by norm_num) plusNorm_pos.le
  have hs : (Real.sqrt plusNorm*Real.sqrt minusNorm)^2 = plusNorm*minusNorm := by
    rw [mul_pow,Real.sq_sqrt plusNorm_pos.le,Real.sq_sqrt minusNorm_pos.le]
  have hd : 0 < Real.sqrt plusNorm*Real.sqrt minusNorm :=
    mul_pos (Real.sqrt_pos.mpr plusNorm_pos) (Real.sqrt_pos.mpr minusNorm_pos)
  nlinarith [sq_abs (rawMoment 2 plusVector minusVector),
    abs_nonneg (rawMoment 2 plusVector minusVector)]

end SubmittedGenus.CapFourMass
