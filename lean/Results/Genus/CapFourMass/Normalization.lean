import Results.Genus.CapFourMass.CarrySpectrum
import Results.Genus.CapFourMass.LocalWeights

/-! Exact original normalization and convergence parameters for all cap-four sectors. -/
noncomputable section
namespace SubmittedGenus.CapFourMass

def feedbackBeta : ℝ := 1-LocalWeights.epsilon radius
def feedbackGamma : ℝ := 1-LocalWeights.delta radius
def feedbackT : ℝ := feedbackGamma/feedbackBeta

def normalizer : ℝ := 70651823329321825/72057594037927936
def tBound : ℝ := 252061464497/250000000000
def eta : ℝ := strongBound/lambdaBound
def sigma : ℝ := restrictedBound/strongBound
def mixedJ : ℝ := (normalizer*lambdaBound)^2
def pureJ : ℝ := lambdaBound^2*feedbackBeta
def negativeSquare : ℝ := (39/100)^2

def mixedA (x : ℝ) : ℝ := eta/x^2
def mixedB (x : ℝ) : ℝ := eta*lambdaBound^4*x^2
def pureA : ℝ := eta/tBound^2
def pureB : ℝ := eta*pureJ*feedbackBeta^(-2:ℤ)*tBound^2

def convergenceDomain (A B : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧ A*B < 1 ∧ A*B^2 < 1 ∧ B*sigma < 1 ∧ B ≠ 1

lemma feedbackBeta_bounds : 0 < feedbackBeta ∧ feedbackBeta < 1 := by
  have h0 := LocalWeights.epsilon_pos radius_pos
  have h1 := LocalWeights.epsilon_lt_one radius_pos
  dsimp [feedbackBeta]
  constructor <;> linarith
lemma feedbackGamma_bounds : 0 < feedbackGamma ∧ feedbackGamma < 1 := by
  have h0 := LocalWeights.delta_pos radius_pos
  have h1 := LocalWeights.delta_lt_one radius_pos
  dsimp [feedbackGamma]
  constructor <;> linarith

lemma feedbackT_interval :
    73854862990399022/72057594037927936 ≤ feedbackT ∧
    feedbackT ≤ 73854862990399023/72057594037927936 := by
  norm_num [feedbackT,feedbackGamma,feedbackBeta,LocalWeights.delta,LocalWeights.epsilon,
    LocalWeights.s,LocalWeights.a,LocalWeights.b,radius]

lemma normalizer_bounds : 0 < normalizer ∧ normalizer < 1 := by norm_num [normalizer]
lemma normalizer_square_ge_beta : feedbackBeta ≤ normalizer^2 := by
  norm_num [feedbackBeta,LocalWeights.epsilon,LocalWeights.s,LocalWeights.a,LocalWeights.b,
    radius,normalizer]
lemma normalizer_lambdaBound_lt_one : normalizer*lambdaBound < 1 := by
  norm_num [normalizer,lambdaBound]
lemma lambdaBound_gt_one : 1 < lambdaBound := by norm_num [lambdaBound]
lemma lambdaBound_pos : 0 < lambdaBound := by norm_num [lambdaBound]
lemma normalizer_lam_lt_one : normalizer*lam < 1 :=
  (mul_lt_mul_of_pos_left lam_lt_bound normalizer_bounds.1).trans normalizer_lambdaBound_lt_one

lemma mixedJ_bounds : 0 < mixedJ ∧ mixedJ < 1 := by
  norm_num [mixedJ,normalizer,lambdaBound]
lemma pureJ_bounds : 0 < pureJ ∧ pureJ < 1 := by
  norm_num [pureJ,lambdaBound,feedbackBeta,LocalWeights.epsilon,LocalWeights.s,
    LocalWeights.a,LocalWeights.b,radius]
lemma negativeSquare_bounds : 0 < negativeSquare ∧ negativeSquare < 1 := by
  norm_num [negativeSquare]
lemma eta_bounds : 0 < eta ∧ eta < 1 := by norm_num [eta,strongBound,lambdaBound]
lemma sigma_bounds : 0 < sigma ∧ sigma < 1 := by norm_num [sigma,strongBound,restrictedBound]
lemma tBound_gt_one : 1 < tBound := by norm_num [tBound]
lemma feedbackT_le_tBound_cube : feedbackT ≤ tBound^3 := by
  norm_num [feedbackT,feedbackGamma,feedbackBeta,LocalWeights.delta,LocalWeights.epsilon,
    LocalWeights.s,LocalWeights.a,LocalWeights.b,radius,tBound]

lemma short_convergence_two : convergenceDomain eta (eta*lambdaBound^2) := by
  norm_num [convergenceDomain,eta,sigma,strongBound,restrictedBound,lambdaBound]
lemma short_convergence_four : convergenceDomain eta (eta*lambdaBound^4) := by
  norm_num [convergenceDomain,eta,sigma,strongBound,restrictedBound,lambdaBound]
lemma mixed_convergence_zero : convergenceDomain (mixedA tBound) (mixedB tBound) := by
  norm_num [convergenceDomain,mixedA,mixedB,eta,sigma,strongBound,restrictedBound,lambdaBound,tBound]
lemma mixed_convergence_one : convergenceDomain (mixedA (tBound*mixedJ)) (mixedB (tBound*mixedJ)) := by
  norm_num [convergenceDomain,mixedA,mixedB,eta,sigma,strongBound,restrictedBound,lambdaBound,
    tBound,mixedJ,normalizer]
lemma mixed_convergence_two : convergenceDomain (mixedA (tBound*mixedJ^2)) (mixedB (tBound*mixedJ^2)) := by
  norm_num [convergenceDomain,mixedA,mixedB,eta,sigma,strongBound,restrictedBound,lambdaBound,
    tBound,mixedJ,normalizer]
lemma pure_convergence : convergenceDomain pureA pureB := by
  norm_num [convergenceDomain,pureA,pureB,pureJ,eta,sigma,strongBound,restrictedBound,lambdaBound,
    tBound,feedbackBeta,LocalWeights.epsilon,LocalWeights.s,LocalWeights.a,LocalWeights.b,radius]

/-- Original normalization inequality, before any source partition is enlarged. -/
lemma feedback_power_le_normalized (N : ℕ) : feedbackBeta^N ≤ normalizer^(2*N) := by
  have h := pow_le_pow_left₀ feedbackBeta_bounds.1.le normalizer_square_ge_beta N
  simpa only [← pow_mul] using h

/-- The manuscript's T^(1+floor(d/3)) enlargement retains exact T. -/
lemma feedback_gap_bound (d : ℕ) : feedbackT^(1+d/3) ≤ feedbackT*tBound^d := by
  have hT : 0 ≤ feedbackT := div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le
  have ht : 0 ≤ tBound := (lt_trans (by norm_num) tBound_gt_one).le
  have hp := pow_le_pow_left₀ hT feedbackT_le_tBound_cube (d/3)
  have hpow : tBound^(3*(d/3)) ≤ tBound^d := by
    apply pow_le_pow_right₀ tBound_gt_one.le
    omega
  rw [pow_add,pow_one]
  apply mul_le_mul_of_nonneg_left _ hT
  exact hp.trans (by simpa only [← pow_mul] using hpow)

end SubmittedGenus.CapFourMass
