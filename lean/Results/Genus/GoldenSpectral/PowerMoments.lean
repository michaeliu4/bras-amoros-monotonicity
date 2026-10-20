import Results.Genus.GoldenSpectral.Moments

/-! All-power golden-q moment bounds from the seven submitted certificates. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.GoldenSpectral
open CapFiveMass.MatrixBounds CapFourMass

lemma strongBound_pos : 0<strongBound := by norm_num [strongBound]
lemma strongBound_lt_one : strongBound<1 := by norm_num [strongBound]
lemma strong_symmetric : strongMatrix.transpose=strongMatrix := transfer_symmetric 4 4
lemma strong_power_symmetric (n : ℕ) : (strongMatrix^n).transpose=strongMatrix^n := by
  rw [Matrix.transpose_pow,strong_symmetric]
lemma strong_bilinear_shift (a n b : ℕ) (x y : State→ℝ) :
    x ⬝ᵥ ((strongMatrix^(a+n+b))*ᵥ y)=
      ((strongMatrix^a)*ᵥ x) ⬝ᵥ ((strongMatrix^n)*ᵥ ((strongMatrix^b)*ᵥ y)) := by
  rw [pow_add,pow_add,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  have h:=Matrix.dotProduct_transpose_mulVec (strongMatrix^a) x
    ((strongMatrix^n)*ᵥ ((strongMatrix^b)*ᵥ y))
  rw [strong_power_symmetric] at h
  exact h.trans (dotProduct_comm _ _)
lemma strong_power_energy_eq (n : ℕ) (x : State→ℝ) :
    vectorEnergy ((strongMatrix^n)*ᵥ x)=x ⬝ᵥ ((strongMatrix^(2*n))*ᵥ x) := by
  rw [vectorEnergy_mulVec_eq,strong_power_symmetric,← pow_add]
  congr 3
  omega

lemma plus_one_energy : vectorEnergy (strongMatrix*ᵥ qplus)≤823/1250 := by
  have h:=alpha_two_bound.le
  rw [← strong_power_energy_eq 1] at h
  simpa only [pow_one,abs_of_nonneg (vectorEnergy_nonneg _)] using h
lemma minus_one_energy : vectorEnergy (strongMatrix*ᵥ qminus)≤66/625 := by
  have h:=beta_two_bound.le
  rw [← strong_power_energy_eq 1] at h
  simpa only [pow_one,abs_of_nonneg (vectorEnergy_nonneg _)] using h
lemma minus_two_energy : vectorEnergy ((strongMatrix^2)*ᵥ qminus)≤17/1000 := by
  have h:=beta_four_bound.le
  rw [← strong_power_energy_eq 2] at h
  simpa only [abs_of_nonneg (vectorEnergy_nonneg _)] using h

lemma shifted_moment_abs_le (a n b : ℕ) (x y : State→ℝ) (X Y c : ℝ)
    (hc : 0≤c) (hX : vectorEnergy ((strongMatrix^a)*ᵥ x)≤X)
    (hY : vectorEnergy ((strongMatrix^b)*ᵥ y)≤Y) (hnum : X*Y≤c^2) :
    |x ⬝ᵥ ((strongMatrix^(a+n+b))*ᵥ y)|≤strongBound^n*c := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (pow_nonneg strongBound_pos.le _) hc)).mp
  rw [sq_abs,strong_bilinear_shift]
  have h:=power_bilinear_sq_le strongMatrix strongBound strong_energy_le n
    ((strongMatrix^a)*ᵥ x) ((strongMatrix^b)*ᵥ y)
  have hxy:=(mul_le_mul hX hY (vectorEnergy_nonneg _) ((vectorEnergy_nonneg _).trans hX)).trans hnum
  have hh:=mul_le_mul_of_nonneg_left hxy (pow_nonneg strongBound_pos.le (2*n))
  have he : strongBound^(2*n)*c^2=(strongBound^n*c)^2 := by rw [mul_pow,← pow_mul]; congr 2; omega
  exact h.trans (by simpa only [mul_assoc,he] using hh)

/-- Uniform alpha entry with the original three-edge discount. -/
lemma alpha_all (k : ℕ) (hk : 1≤k) :
    |qplus ⬝ᵥ ((strongMatrix^k)*ᵥ qplus)|≤strongBound^(k-3)*(823/1250) := by
  by_cases h1 : k=1
  · subst k; simpa using alpha_one_bound.le
  by_cases h2 : k=2
  · subst k; simpa using alpha_two_bound.le
  have hge : 3≤k := by omega
  have h:=shifted_moment_abs_le 1 (k-2) 1 qplus qplus (823/1250) (823/1250) (823/1250)
    (by norm_num) (by simpa using plus_one_energy) (by simpa using plus_one_energy) (by norm_num)
  rw [show 1+(k-2)+1=k by omega] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one strongBound_pos.le strongBound_lt_one.le (by omega : k-3≤k-2)) (by norm_num))

lemma omega_all (k : ℕ) (hk : 1≤k) :
    |qplus ⬝ᵥ ((strongMatrix^k)*ᵥ qminus)|≤strongBound^(k-3)*((13/50)*(823/1250)) := by
  by_cases h1 : k=1
  · subst k; exact omega_one_bound.le.trans (by norm_num)
  by_cases h2 : k=2
  · subst k; exact omega_two_bound.le.trans (by norm_num)
  have hge : 3≤k := by omega
  have h:=shifted_moment_abs_le 1 (k-3) 2 qplus qminus (823/1250) (17/1000) ((13/50)*(823/1250))
    (by norm_num) (by simpa using plus_one_energy) minus_two_energy (by norm_num)
  simpa only [show 1+(k-3)+2=k by omega] using h

lemma beta_all (k : ℕ) (hk : 1≤k) :
    |qminus ⬝ᵥ ((strongMatrix^k)*ᵥ qminus)|≤strongBound^(k-3)*(66/625) := by
  by_cases h1 : k=1
  · subst k; exact beta_one_bound.le.trans (by norm_num)
  by_cases h2 : k=2
  · subst k; simpa using beta_two_bound.le
  by_cases h3 : k=3
  · subst k
    simpa using shifted_moment_abs_le 1 0 2 qminus qminus (66/625) (17/1000) (66/625)
      (by norm_num) (by simpa using minus_one_energy) minus_two_energy (by norm_num)
  have hge : 4≤k := by omega
  have h:=shifted_moment_abs_le 2 (k-4) 2 qminus qminus (17/1000) (17/1000) (17/1000)
    (by norm_num) minus_two_energy minus_two_energy (by norm_num)
  rw [show 2+(k-4)+2=k by omega] at h
  apply h.trans
  rw [show k-3=(k-4)+1 by omega,pow_succ]
  have hn : (17/1000:ℝ)≤strongBound*(66/625) := by norm_num [strongBound]
  exact (mul_le_mul_of_nonneg_left hn (pow_nonneg strongBound_pos.le _)).trans_eq (by ring)

end SubmittedGenus.GoldenSpectral
