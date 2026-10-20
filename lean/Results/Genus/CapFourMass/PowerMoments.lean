import Results.Genus.CapFourMass.SpectralMoments
import Results.Genus.CapFourMass.CarryModes

/-! All-power source moment estimates from the submitted finite certificates. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

lemma strong_symmetric : strongMatrix.transpose = strongMatrix := transfer_symmetric 4 4
lemma strong_power_symmetric (n : ℕ) : (strongMatrix^n).transpose = strongMatrix^n := by
  rw [Matrix.transpose_pow,strong_symmetric]
lemma strongBound_pos : 0 < strongBound := by norm_num [strongBound]

lemma strong_bilinear_shift (a n b : ℕ) (x y : State → ℝ) :
    x ⬝ᵥ ((strongMatrix^(a+n+b)) *ᵥ y) =
      ((strongMatrix^a) *ᵥ x) ⬝ᵥ ((strongMatrix^n) *ᵥ ((strongMatrix^b) *ᵥ y)) := by
  rw [pow_add,pow_add,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  have h := Matrix.dotProduct_transpose_mulVec (strongMatrix^a) x
    ((strongMatrix^n) *ᵥ ((strongMatrix^b) *ᵥ y))
  rw [strong_power_symmetric] at h
  exact h.trans (dotProduct_comm _ _)

lemma strong_power_energy_eq (n : ℕ) (x : State → ℝ) :
    vectorEnergy ((strongMatrix^n) *ᵥ x) = x ⬝ᵥ ((strongMatrix^(2*n)) *ᵥ x) := by
  rw [vectorEnergy_mulVec_eq,strong_power_symmetric,← pow_add]
  congr 3
  omega

lemma plus_one_energy : vectorEnergy (strongMatrix *ᵥ qplus) ≤ 69/100 := by
  have h := alpha_two_bound.le
  rw [← strong_power_energy_eq 1] at h
  simpa only [pow_one,abs_of_nonneg (vectorEnergy_nonneg _)] using h
lemma minus_one_energy : vectorEnergy (strongMatrix *ᵥ qminus) ≤ 11/100 := by
  have h := nu_two_bound.le
  rw [← strong_power_energy_eq 1] at h
  simpa only [pow_one,abs_of_nonneg (vectorEnergy_nonneg _)] using h
lemma minus_two_energy : vectorEnergy ((strongMatrix^2) *ᵥ qminus) ≤ 2/100 := by
  have h := nu_four_bound.le
  rw [← strong_power_energy_eq 2] at h
  simpa only [abs_of_nonneg (vectorEnergy_nonneg _)] using h

/-- Shift a finite left and right moment into the endpoints before applying
operator contraction. This is the submitted Cauchy--Schwarz extension. -/
lemma shifted_moment_sq_le (a n b : ℕ) (x y : State → ℝ) (X Y : ℝ)
    (hX : vectorEnergy ((strongMatrix^a) *ᵥ x) ≤ X)
    (hY : vectorEnergy ((strongMatrix^b) *ᵥ y) ≤ Y) :
    (x ⬝ᵥ ((strongMatrix^(a+n+b)) *ᵥ y))^2 ≤ strongBound^(2*n)*X*Y := by
  rw [strong_bilinear_shift]
  have h := power_bilinear_sq_le strongMatrix strongBound strong_energy_le n
    ((strongMatrix^a) *ᵥ x) ((strongMatrix^b) *ᵥ y)
  have hXY := mul_le_mul hX hY (vectorEnergy_nonneg _)
    ((vectorEnergy_nonneg _).trans hX)
  have hh := mul_le_mul_of_nonneg_left hXY (pow_nonneg strongBound_pos.le (2*n))
  exact h.trans (by simpa only [mul_assoc] using hh)

lemma shifted_moment_abs_le (a n b : ℕ) (x y : State → ℝ) (X Y c : ℝ)
    (hc : 0 ≤ c)
    (hX : vectorEnergy ((strongMatrix^a) *ᵥ x) ≤ X)
    (hY : vectorEnergy ((strongMatrix^b) *ᵥ y) ≤ Y)
    (hnum : X*Y ≤ (strongBound^(a+b)*c)^2) :
    |x ⬝ᵥ ((strongMatrix^(a+n+b)) *ᵥ y)| ≤ strongBound^(a+n+b)*c := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (pow_nonneg strongBound_pos.le _) hc)).mp
  rw [sq_abs]
  have h := shifted_moment_sq_le a n b x y X Y hX hY
  have hn := mul_le_mul_of_nonneg_left hnum (pow_nonneg strongBound_pos.le (2*n))
  have he : strongBound^(2*n)*(strongBound^(a+b)*c)^2 =
      (strongBound^(a+n+b)*c)^2 := by
    rw [mul_pow,mul_pow,← pow_mul,← pow_mul]
    rw [← mul_assoc,← pow_add]
    congr 1
    congr 1
    omega
  rw [he] at hn
  exact h.trans (by simpa only [mul_assoc] using hn)

/-- Uniform alpha bound for every nonempty strong run. -/
theorem alpha_all (k : ℕ) (hk : 1 ≤ k) :
    |qplus ⬝ᵥ ((strongMatrix^k) *ᵥ qplus)| ≤ strongBound^k*(47/50) := by
  by_cases h1 : k=1
  · subst k
    exact alpha_one_bound.le.trans (by norm_num [strongBound])
  · obtain ⟨n,rfl⟩ : ∃ n, k=1+n+1 := ⟨k-2,by omega⟩
    apply shifted_moment_abs_le 1 n 1 qplus qplus (69/100) (69/100) (47/50)
      (by norm_num) (by simpa using plus_one_energy) (by simpa using plus_one_energy)
    norm_num [strongBound]

/-- Uniform off-diagonal bound tight enough for both uv entries. -/
theorem omega_all (k : ℕ) (hk : 1 ≤ k) :
    |qplus ⬝ᵥ ((strongMatrix^k) *ᵥ qminus)| ≤ strongBound^k*(7/25)*(47/50) := by
  by_cases h1 : k=1
  · subst k
    exact omega_one_bound.le.trans (by norm_num [strongBound])
  by_cases h2 : k=2
  · subst k
    exact omega_two_bound.le.trans (by norm_num [strongBound])
  obtain ⟨n,rfl⟩ : ∃ n, k=1+n+2 := ⟨k-3,by omega⟩
  have h := shifted_moment_abs_le 1 n 2 qplus qminus (69/100) (2/100)
    ((7/25)*(47/50)) (by norm_num) (by simpa using plus_one_energy) minus_two_energy
    (by norm_num [strongBound])
  simpa only [mul_assoc] using h

/-- Negative diagonal gains the essential positive carry-run ratio. -/
theorem nu_all_scaled (k : ℕ) (hk : 1 ≤ k) :
    |qminus ⬝ᵥ ((strongMatrix^k) *ᵥ qminus)| * (39/100) ≤
      strongBound^k*(7/25)*(9/50) := by
  by_cases h1 : k=1
  · subst k
    exact (mul_le_mul_of_nonneg_right nu_one_bound.le (by norm_num)).trans
      (by norm_num [strongBound])
  by_cases h2 : k=2
  · subst k
    exact (mul_le_mul_of_nonneg_right nu_two_bound.le (by norm_num)).trans
      (by norm_num [strongBound])
  by_cases h3 : k=3
  · subst k
    have h := shifted_moment_abs_le 1 0 2 qminus qminus (11/100) (2/100)
      ((7/25)*(9/50)/(39/100)) (by norm_num)
      (by simpa using minus_one_energy) minus_two_energy (by norm_num [strongBound])
    have hh := mul_le_mul_of_nonneg_right h (by norm_num : (0:ℝ)≤39/100)
    norm_num at hh ⊢
    nlinarith
  obtain ⟨n,rfl⟩ : ∃ n, k=2+n+2 := ⟨k-4,by omega⟩
  have h := shifted_moment_abs_le 2 n 2 qminus qminus (2/100) (2/100)
    ((7/25)*(9/50)/(39/100)) (by norm_num) minus_two_energy minus_two_energy
    (by norm_num [strongBound])
  have hh := mul_le_mul_of_nonneg_right h (by norm_num : (0:ℝ)≤39/100)
  norm_num at hh ⊢
  nlinarith

end SubmittedGenus.CapFourMass
