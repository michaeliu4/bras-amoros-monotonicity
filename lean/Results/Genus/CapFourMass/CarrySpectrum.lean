import Results.Genus.CapFourMass.SpectralMatrices
import Mathlib.Tactic

/-! The actual real carry roots and normalized source eigenvectors. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

def carryA : ℝ := radius
def carryB : ℝ := radius^2+radius^3
def discriminant : ℝ := carryB^2+4*carryA*carryB
def lam : ℝ := (carryB+Real.sqrt discriminant)/2
def mu : ℝ := carryB-lam
def rho : ℝ := |mu|/lam

lemma carryA_pos : 0 < carryA := radius_pos
lemma carryB_pos : 0 < carryB := by unfold carryB; have := radius_pos; positivity
lemma discriminant_pos : 0 < discriminant := by
  unfold discriminant
  have := carryA_pos
  have := carryB_pos
  positivity
lemma lam_pos : 0 < lam := by
  unfold lam
  have := carryB_pos
  have := Real.sqrt_nonneg discriminant
  positivity
lemma lam_quadratic : lam^2-carryB*lam-carryA*carryB=0 := by
  have h := Real.sq_sqrt discriminant_pos.le
  dsimp [lam, discriminant] at *
  nlinarith

/-- Rational enclosure sufficient for all finite moment certificates. -/
lemma lam_bounds : 101778/100000 < lam ∧ lam < 101778011/100000000 := by
  have h := lam_quadratic
  have hp := lam_pos
  norm_num [carryA,carryB,radius] at h
  constructor <;> nlinarith

lemma lam_gt_one : 1 < lam := by have := lam_bounds.1; linarith
lemma lam_lt_bound : lam < lambdaBound := lam_bounds.2
lemma mu_neg : mu < 0 := by
  unfold mu
  have h := lam_gt_one
  have hb : carryB < 1 := by norm_num [carryB,radius]
  linarith
lemma rho_bounds : 0 < rho ∧ rho < 39/100 := by
  unfold rho
  rw [abs_of_neg mu_neg]
  constructor
  · exact div_pos (neg_pos.mpr mu_neg) lam_pos
  · apply (div_lt_iff₀ lam_pos).mpr
    unfold mu
    have h := lam_bounds.2
    norm_num [carryB,radius] at *
    linarith

/-- The paper's y+ scaled by lambda, and y- scaled by a. Positive scalings
do not alter the normalized eigenvectors. -/
def plusVector : State → ℝ := ![carryB,lam,lam,0]
def minusVector : State → ℝ := ![lam,-carryA,-carryA,0]
def plusRaw : State → ℝ := halfScale plusVector
def minusRaw : State → ℝ := halfScale minusVector
def plusNorm : ℝ := vectorEnergy plusRaw
def minusNorm : ℝ := vectorEnergy minusRaw

def qplus : State → ℝ := fun i => plusRaw i / Real.sqrt plusNorm
def qminus : State → ℝ := fun i => minusRaw i / Real.sqrt minusNorm

lemma halfScale_dot (v w : State → ℝ) :
    halfScale v ⬝ᵥ halfScale w = ∑ i, radius^(i.val+1)*v i*w i := by
  unfold dotProduct halfScale
  apply Finset.sum_congr rfl
  intro i _
  calc
    halfWeight i*v i*(halfWeight i*w i) = (halfWeight i)^2*v i*w i := by ring
    _ = _ := by rw [halfWeight_sq]

lemma vectorEnergy_eq_dot (v : State → ℝ) : vectorEnergy v = v ⬝ᵥ v := by
  simp [vectorEnergy,dotProduct,pow_two]

lemma plusNorm_eq : plusNorm = carryA*carryB^2+carryB*lam^2 := by
  rw [plusNorm, vectorEnergy_eq_dot, plusRaw, halfScale_dot]
  norm_num [plusVector, Fin.sum_univ_succ, carryA, carryB]
  ring
lemma minusNorm_eq : minusNorm = carryA*lam^2+carryA^2*carryB := by
  rw [minusNorm, vectorEnergy_eq_dot, minusRaw, halfScale_dot]
  norm_num [minusVector, Fin.sum_univ_succ, carryA, carryB]
  ring
lemma plusNorm_lower : 9/10 < plusNorm := by
  rw [plusNorm_eq]
  have h := lam_bounds.1
  have hl := lam_pos
  norm_num [carryA,carryB,radius] at *
  nlinarith
lemma minusNorm_lower : 89/100 < minusNorm := by
  rw [minusNorm_eq]
  have h := lam_bounds.1
  have hl := lam_pos
  norm_num [carryA,carryB,radius] at *
  nlinarith
lemma plusNorm_pos : 0 < plusNorm := lt_trans (by norm_num) plusNorm_lower
lemma minusNorm_pos : 0 < minusNorm := lt_trans (by norm_num) minusNorm_lower
lemma plusRaw_minusRaw : plusRaw ⬝ᵥ minusRaw = 0 := by
  rw [plusRaw, minusRaw, halfScale_dot]
  norm_num [plusVector,minusVector,carryA,carryB,Fin.sum_univ_succ]
  ring

lemma normalized_energy (v : State → ℝ) (hv : 0 < vectorEnergy v) :
    vectorEnergy (fun i => v i/Real.sqrt (vectorEnergy v)) = 1 := by
  simp only [vectorEnergy,div_pow,← Finset.sum_div]
  change vectorEnergy v / (Real.sqrt (vectorEnergy v))^2 = 1
  rw [Real.sq_sqrt hv.le]
  exact div_self (ne_of_gt hv)
lemma qplus_energy : vectorEnergy qplus = 1 := normalized_energy plusRaw plusNorm_pos
lemma qminus_energy : vectorEnergy qminus = 1 := normalized_energy minusRaw minusNorm_pos
lemma qplus_qminus : qplus ⬝ᵥ qminus = 0 := by
  simp only [qplus,qminus,dotProduct,div_mul_div_comm,← Finset.sum_div]
  change (plusRaw ⬝ᵥ minusRaw)/_ = 0
  rw [plusRaw_minusRaw,zero_div]
lemma qplus_nonneg (i : State) : 0 ≤ qplus i := by
  apply div_nonneg _ (Real.sqrt_nonneg _)
  unfold plusRaw halfScale plusVector
  apply mul_nonneg (halfWeight_pos i).le
  fin_cases i <;> simp <;> first | exact carryB_pos.le | exact lam_pos.le

end SubmittedGenus.CapFourMass
