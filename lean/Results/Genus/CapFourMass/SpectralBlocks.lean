import Results.Genus.CapFourMass.PowerMoments

/-!
# The submitted source-coupled block lemma

The carry length hypothesis is n≥1. No bare strong-block assertion is made.
The matrices in the conclusion are the actual D, E, orthonormal Q and carry
roots, whose finite numeric and all-power estimates have already been proved.
-/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

abbrev Mode := Fin 2
def modeVector : Mode → State → ℝ := ![qplus,qminus]
def modeRoot : Mode → ℝ := ![lam,mu]
def modeMatrix : Matrix State Mode ℝ := fun i j => modeVector j i
def modeU : Mode → ℝ := ![1,7/25]
def modeV : Mode → ℝ := ![47/50,9/50]
def projected (A : Matrix State State ℝ) : Matrix Mode Mode ℝ :=
  modeMatrix.transpose*A*modeMatrix

def coupledBlock (A : Matrix State State ℝ) (n : ℕ) : Matrix Mode Mode ℝ :=
  projected A*Matrix.diagonal (fun j => (modeRoot j)^n)

lemma projected_entry (A : Matrix State State ℝ) (i j : Mode) :
    projected A i j = modeVector i ⬝ᵥ (A *ᵥ modeVector j) := by
  rw [projected,Matrix.mul_assoc]
  rfl
lemma coupledBlock_entry (A : Matrix State State ℝ) (n : ℕ) (i j : Mode) :
    coupledBlock A n i j = (modeVector i ⬝ᵥ (A *ᵥ modeVector j))*(modeRoot j)^n := by
  rw [coupledBlock,Matrix.mul_diagonal,projected_entry]

lemma strong_moment_comm (n : ℕ) :
    qminus ⬝ᵥ ((strongMatrix^n) *ᵥ qplus) =
      qplus ⬝ᵥ ((strongMatrix^n) *ᵥ qminus) := by
  have h := Matrix.dotProduct_transpose_mulVec (strongMatrix^n) qminus qplus
  rwa [strong_power_symmetric] at h

lemma mu_abs_le : |mu| ≤ lam*(39/100) := by
  have h := rho_bounds.2.le
  change |mu|/lam ≤ 39/100 at h
  have hh := (div_le_iff₀ lam_pos).mp h
  simpa only [mul_comm] using hh

/-- Positive carry length gives the essential extra factor, uniformly. -/
lemma mu_power_abs_le (n : ℕ) (hn : 1 ≤ n) : |mu^n| ≤ lam^n*(39/100) := by
  have hm : |mu| ≤ lam := mu_abs_le.trans (by nlinarith [lam_pos])
  obtain ⟨k,rfl⟩ : ∃ k, n=k+1 := ⟨n-1,by omega⟩
  rw [abs_pow,pow_succ,pow_succ]
  calc
    |mu|^k*|mu| ≤ lam^k*(lam*(39/100)) := mul_le_mul
      (pow_le_pow_left₀ (abs_nonneg _) hm k) mu_abs_le (abs_nonneg _) (pow_nonneg lam_pos.le _)
    _ = _ := by ring

lemma carry_scaled_of {a c : ℝ} (ha : 0 ≤ a) (hc : a*(39/100) ≤ c)
    (n : ℕ) (hn : 1 ≤ n) : a*|mu^n| ≤ c*lam^n := by
  calc
    a*|mu^n| ≤ a*(lam^n*(39/100)) := mul_le_mul_of_nonneg_left (mu_power_abs_le n hn) ha
    _ = (a*(39/100))*lam^n := by ring
    _ ≤ c*lam^n := mul_le_mul_of_nonneg_right hc (pow_nonneg lam_pos.le _)

/-- Original equation (mass:actual-block), with both strict source length
conditions explicit and all matrix/numeric premises discharged. -/
theorem actual_strong_block (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (i j : Mode) :
    |coupledBlock (strongMatrix^k) n i j| ≤
      strongBound^k*lam^n*modeU i*modeV j := by
  rw [coupledBlock_entry,abs_mul]
  fin_cases i <;> fin_cases j <;> norm_num [modeVector,modeRoot,modeU,modeV,abs_of_pos (pow_pos lam_pos n)]
  · have h := mul_le_mul_of_nonneg_right (alpha_all k hk) (pow_nonneg lam_pos.le n)
    nlinarith
  · rw [← abs_pow]
    apply (carry_scaled_of (abs_nonneg _) ?_ n hn).trans_eq
      (by ring : (strongBound^k*(9/50))*lam^n=strongBound^k*lam^n*(9/50))
    have h := mul_le_mul_of_nonneg_right (omega_all k hk) (by norm_num : (0:ℝ)≤39/100)
    have hp := pow_nonneg strongBound_pos.le k
    nlinarith
  · rw [strong_moment_comm]
    have h := mul_le_mul_of_nonneg_right (omega_all k hk) (pow_nonneg lam_pos.le n)
    nlinarith
  · rw [← abs_pow]
    have h := carry_scaled_of (abs_nonneg _) (nu_all_scaled k hk) n hn
    nlinarith

lemma qplus_four : qplus 3 = 0 := by simp [qplus,plusRaw,halfScale,plusVector]
lemma qminus_four : qminus 3 = 0 := by simp [qminus,minusRaw,halfScale,minusVector]

lemma modeVector_four (i : Mode) : modeVector i 3 = 0 := by
  fin_cases i <;> simp [modeVector,qplus_four,qminus_four]

/-- Endpoint projection equality is exact on the actual q± support. -/
lemma restricted_moment_eq (x y : State → ℝ) (hx : x 3=0) (hy : y 3=0) :
    x ⬝ᵥ (restrictedMatrix *ᵥ y) = x ⬝ᵥ (strongMatrix *ᵥ y) := by
  norm_num [restrictedMatrix,strongMatrix,transfer,gate,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,Fin.succ,hx,hy]
  have hx' : x (⟨3, by decide⟩ : Fin 4) = 0 := hx
  have hy' : y (⟨3, by decide⟩ : Fin 4) = 0 := hy
  simp only [hx',hy',mul_zero,zero_mul,add_zero]

/-- The sharper one-edge restricted source bound, again followed by a
strictly positive carry run. -/
theorem actual_restricted_block (n : ℕ) (hn : 1 ≤ n) (i j : Mode) :
    |coupledBlock restrictedMatrix n i j| ≤
      restrictedBound*lam^n*modeU i*modeV j := by
  rw [coupledBlock_entry,restricted_moment_eq _ _ (modeVector_four i) (modeVector_four j),abs_mul]
  have ha : |qplus ⬝ᵥ (strongMatrix *ᵥ qplus)| ≤ 68/100 := by simpa using alpha_one_bound.le
  have ho : |qplus ⬝ᵥ (strongMatrix *ᵥ qminus)| ≤ 18/100 := by simpa using omega_one_bound.le
  have hn0 : |qminus ⬝ᵥ (strongMatrix *ᵥ qminus)| ≤ 5/100 := by simpa using nu_one_bound.le
  have hc : qminus ⬝ᵥ (strongMatrix *ᵥ qplus) = qplus ⬝ᵥ (strongMatrix *ᵥ qminus) := by
    simpa using strong_moment_comm 1
  fin_cases i <;> fin_cases j <;> norm_num [modeVector,modeRoot,modeU,modeV,abs_of_pos (pow_pos lam_pos n)]
  · have h := mul_le_mul_of_nonneg_right (ha.trans (by norm_num [restrictedBound] :
        (68:ℝ)/100 ≤ restrictedBound*(47/50))) (pow_nonneg lam_pos.le n)
    nlinarith
  · rw [← abs_pow]
    have hs : |qplus ⬝ᵥ (strongMatrix *ᵥ qminus)| * (39/100) ≤ restrictedBound*(9/50) :=
      (mul_le_mul_of_nonneg_right ho (by norm_num)).trans (by norm_num [restrictedBound])
    have h := carry_scaled_of (abs_nonneg _) hs n hn
    nlinarith
  · rw [hc]
    have h := mul_le_mul_of_nonneg_right (ho.trans (by norm_num [restrictedBound] :
        (18:ℝ)/100 ≤ restrictedBound*(7/25)*(47/50))) (pow_nonneg lam_pos.le n)
    nlinarith
  · rw [← abs_pow]
    have hs : |qminus ⬝ᵥ (strongMatrix *ᵥ qminus)| * (39/100) ≤ restrictedBound*(7/25)*(9/50) :=
      (mul_le_mul_of_nonneg_right hn0 (by norm_num)).trans (by norm_num [restrictedBound])
    have h := carry_scaled_of (abs_nonneg _) hs n hn
    nlinarith

lemma mode_norm_product : vectorEnergy modeU*vectorEnergy modeV = 77173/78125 := by
  norm_num [vectorEnergy,modeU,modeV,Fin.sum_univ_succ]
lemma mode_overlap : modeV ⬝ᵥ modeU = 619/625 := by
  norm_num [dotProduct,modeU,modeV,Fin.sum_univ_succ]
lemma mode_norm_product_lt_one : vectorEnergy modeU*vectorEnergy modeV < 1 := by
  rw [mode_norm_product]; norm_num
lemma mode_overlap_lt_one : modeV ⬝ᵥ modeU < 1 := by rw [mode_overlap]; norm_num

end SubmittedGenus.CapFourMass
