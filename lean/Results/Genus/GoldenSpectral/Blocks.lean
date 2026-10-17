import Results.Genus.GoldenSpectral.PowerMoments

/-! The original golden-q rank-one transfer block for every k,n≥1. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.GoldenSpectral
open CapFiveMass.MatrixBounds

abbrev Mode := Fin 2
def modeVector : Mode→State→ℝ := ![qplus,qminus]
def modeRoot : Mode→ℝ := ![1,mu]
def modeMatrix : Matrix State Mode ℝ := fun i j => modeVector j i
def modeU : Mode→ℝ := ![1,13/50]
def modeV : Mode→ℝ := ![823/1250,97/625]
def projected (A : Matrix State State ℝ) : Matrix Mode Mode ℝ :=
  modeMatrix.transpose*A*modeMatrix
def coupledBlock (A : Matrix State State ℝ) (n : ℕ) : Matrix Mode Mode ℝ :=
  projected A*Matrix.diagonal (fun j => modeRoot j^n)

lemma projected_entry (A : Matrix State State ℝ) (i j : Mode) :
    projected A i j=modeVector i ⬝ᵥ (A*ᵥ modeVector j) := by
  rw [projected,Matrix.mul_assoc]
  rfl
lemma coupledBlock_entry (A : Matrix State State ℝ) (n : ℕ) (i j : Mode) :
    coupledBlock A n i j=(modeVector i ⬝ᵥ (A*ᵥ modeVector j))*modeRoot j^n := by
  rw [coupledBlock,Matrix.mul_diagonal,projected_entry]
lemma strong_moment_comm (n : ℕ) :
    qminus ⬝ᵥ ((strongMatrix^n)*ᵥ qplus)=qplus ⬝ᵥ ((strongMatrix^n)*ᵥ qminus) := by
  have h:=Matrix.dotProduct_transpose_mulVec (strongMatrix^n) qminus qplus
  rwa [strong_power_symmetric] at h

lemma mu_power_abs_le (n : ℕ) (hn : 1≤n) : |mu^n|≤191/500 := by
  rw [abs_pow]
  have hm : |mu|≤1 := mu_abs_lt.le.trans (by norm_num)
  have hh:=pow_le_pow_of_le_one (abs_nonneg mu) hm hn
  have hh' : |mu|^n≤|mu| := by simpa only [pow_one] using hh
  exact hh'.trans mu_abs_lt.le

/-- Uniform transfer block (raw:block-bound), with the genuine golden-q
matrices and the exact submitted rank-one vectors. -/
theorem actual_strong_block (k n : ℕ) (hk : 1≤k) (hn : 1≤n) (i j : Mode) :
    |coupledBlock (strongMatrix^k) n i j|≤
      strongBound^(k-3)*modeU i*modeV j := by
  rw [coupledBlock_entry,abs_mul]
  fin_cases i <;> fin_cases j <;> norm_num [modeVector,modeRoot,modeU,modeV]
  · exact alpha_all k hk
  · have h:=mul_le_mul (omega_all k hk) (mu_power_abs_le n hn)
      (abs_nonneg _) (mul_nonneg (pow_nonneg strongBound_pos.le _) (by norm_num))
    simp only [abs_pow] at h
    have hp:=pow_nonneg strongBound_pos.le (k-3)
    nlinarith
  · rw [strong_moment_comm]
    simpa only [mul_assoc] using omega_all k hk
  · have h:=mul_le_mul (beta_all k hk) (mu_power_abs_le n hn)
      (abs_nonneg _) (mul_nonneg (pow_nonneg strongBound_pos.le _) (by norm_num))
    simp only [abs_pow] at h
    have hp:=pow_nonneg strongBound_pos.le (k-3)
    nlinarith

lemma qplus_last : qplus 3=0 := by norm_num [qplus,plusRaw,halfScale,plusVector,Matrix.cons_val_three,Matrix.cons_val_zero]
lemma qminus_last : qminus 3=0 := by norm_num [qminus,minusRaw,halfScale,minusVector,Matrix.cons_val_three,Matrix.cons_val_zero]
lemma modeVector_last (j : Mode) : modeVector j 3=0 := by
  fin_cases j <;> simp [modeVector,qplus_last,qminus_last]

/-- E deletes only the fourth row/column, which vanish in both carry modes. -/
lemma projected_restricted_eq : projected restrictedMatrix=projected strongMatrix := by
  ext i j
  rw [projected_entry,projected_entry]
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  norm_num [restrictedMatrix,strongMatrix,transfer,gate,modeVector_last,
    show (Fin.succ (2 : Fin 3) : Fin 4)=3 from rfl]

lemma mode_rank_inner : modeV ⬝ᵥ modeU=10918/15625 := by
  norm_num [modeV,modeU,dotProduct,Fin.sum_univ_succ]

end SubmittedGenus.GoldenSpectral
