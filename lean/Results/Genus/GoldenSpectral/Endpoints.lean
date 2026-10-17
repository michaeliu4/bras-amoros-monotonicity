import Results.Genus.GoldenSpectral.Blocks

/-! Exact golden-q carry powers, orthogonal endpoint contraction, and physical
alphabet/loop norms used by the original raw graph-value estimate. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.GoldenSpectral
open CapFiveMass.MatrixBounds

lemma dot_add_right (v x y : State→ℝ) :
    v ⬝ᵥ (fun i => x i+y i)=v ⬝ᵥ x+v ⬝ᵥ y := by
  simp only [dotProduct,mul_add,Finset.sum_add_distrib]
lemma dot_scale_right (c : ℝ) (v w : State→ℝ) :
    v ⬝ᵥ (fun i => c*w i)=c*(v ⬝ᵥ w) := by
  simp only [dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
lemma dot_scale_left (c : ℝ) (v w : State→ℝ) :
    (fun i => c*v i) ⬝ᵥ w=c*(v ⬝ᵥ w) := by
  simp only [dotProduct,Finset.mul_sum,mul_assoc]
lemma qminus_qplus : qminus ⬝ᵥ qplus=0 := by rw [dotProduct_comm,qplus_qminus]
lemma matrix_mulVec_add (A : Matrix State State ℝ) (x y : State→ℝ) :
    A*ᵥ (fun i => x i+y i)=fun i => (A*ᵥ x) i+(A*ᵥ y) i := by
  funext i
  simp only [Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib]
lemma matrix_mulVec_scale (A : Matrix State State ℝ) (c : ℝ) (v : State→ℝ) :
    A*ᵥ (fun i => c*v i)=fun i => c*(A*ᵥ v) i := by
  funext i
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma carry_modes (x : State→ℝ) :
    carryMatrix*ᵥ x=fun i => (qplus ⬝ᵥ x)*qplus i+mu*(qminus ⬝ᵥ x)*qminus i := by
  funext i
  simp only [Matrix.mulVec,dotProduct]
  simp_rw [carry_matrix_modes]
  simp only [add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

lemma carry_power_modes (n : ℕ) (x : State→ℝ) :
    (carryMatrix^(n+1))*ᵥ x=fun i =>
      (qplus ⬝ᵥ x)*qplus i+mu^(n+1)*(qminus ⬝ᵥ x)*qminus i := by
  induction n with
  | zero => simpa only [Nat.zero_add,pow_one] using carry_modes x
  | succ n ih =>
    rw [pow_succ',← Matrix.mulVec_mulVec,ih,matrix_mulVec_add,
      matrix_mulVec_scale,matrix_mulVec_scale,qplus_eigen,qminus_eigen]
    funext i
    simp only [pow_succ]
    ring

lemma carry_power_matrix (n : ℕ) (hn : 1 ≤ n) :
    carryMatrix^n=modeMatrix*Matrix.diagonal (fun j => modeRoot j^n)*modeMatrix.transpose := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [carry_power_modes]
  simp only [← Matrix.mulVec_mulVec]
  ext i
  simp only [Matrix.mulVec_diagonal,modeMatrix,Matrix.transpose_apply,
    Matrix.mulVec,dotProduct,Fin.sum_univ_two,modeVector,modeRoot,
    Matrix.cons_val_zero,Matrix.cons_val_one,one_pow]
  norm_num [Matrix.diagonal,modeRoot]
  ring

lemma projection_residual_energy (x : State→ℝ) (a b : ℝ) :
    vectorEnergy (fun i => x i-a*qplus i-b*qminus i)=
      vectorEnergy x+a^2+b^2-2*a*(qplus ⬝ᵥ x)-2*b*(qminus ⬝ᵥ x) := by
  have he : vectorEnergy (fun i => x i-a*qplus i-b*qminus i)=
      vectorEnergy x+a^2*vectorEnergy qplus+b^2*vectorEnergy qminus-
      2*a*(qplus ⬝ᵥ x)-2*b*(qminus ⬝ᵥ x)+2*a*b*(qplus ⬝ᵥ qminus) := by
    simp only [vectorEnergy,dotProduct,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [qplus_energy,qminus_energy,qplus_qminus,mul_one,mul_zero,add_zero] using he

lemma two_mode_bessel (x : State→ℝ) :
    (qplus ⬝ᵥ x)^2+(qminus ⬝ᵥ x)^2 ≤ vectorEnergy x := by
  have h:=vectorEnergy_nonneg (fun i => x i-(qplus ⬝ᵥ x)*qplus i-(qminus ⬝ᵥ x)*qminus i)
  rw [projection_residual_energy] at h
  nlinarith

def modeBoundary (x : State→ℝ) : Mode→ℝ := fun j => |modeVector j ⬝ᵥ x|
lemma modeBoundary_energy (x : State→ℝ) : vectorEnergy (modeBoundary x) ≤ vectorEnergy x := by
  simpa [vectorEnergy,modeBoundary,modeVector,Fin.sum_univ_succ,sq_abs] using two_mode_bessel x
lemma modeRoot_power_abs_le (n : ℕ) (j : Mode) : |modeRoot j^n| ≤ 1 := by
  fin_cases j
  · simp [modeRoot]
  · simpa [modeRoot,abs_pow] using pow_le_one₀ (abs_nonneg mu)
      (mu_abs_lt.le.trans (by norm_num : (191/500:ℝ) ≤ 1))

def carryBoundary (n : ℕ) (x : State→ℝ) : Mode→ℝ := fun j => |modeRoot j^n*(modeVector j ⬝ᵥ x)|
lemma carryBoundary_energy (n : ℕ) (x : State→ℝ) : vectorEnergy (carryBoundary n x) ≤ vectorEnergy x := by
  apply le_trans _ (modeBoundary_energy x)
  apply Finset.sum_le_sum
  intro j _
  have h:=mul_le_mul_of_nonneg_right (modeRoot_power_abs_le n j) (abs_nonneg (modeVector j ⬝ᵥ x))
  simp only [one_mul] at h
  simpa only [carryBoundary,modeBoundary,abs_mul] using
    pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _)) h 2

def alphabetMass : ℝ := ∑ i : State,radius^(i.val+1)
def loopMass : ℝ := radius^2+radius^3+radius^4
lemma alphabetMass_eq : alphabetMass=1+radius^2 := by
  norm_num [alphabetMass,Fin.sum_univ_succ]
  nlinarith [radius_pow_two,radius_pow_three,radius_pow_four]
lemma alphabetMass_gt_one : 1<alphabetMass := by rw [alphabetMass_eq]; nlinarith [sq_pos_of_pos radius_pos]
lemma loopMass_lt_one : loopMass<1 := by
  unfold loopMass
  rw [radius_pow_two,radius_pow_three,radius_pow_four]
  linarith [radius_lower]

def endpoint (cap : ℕ) (loop : Bool) : State→ℝ := fun i =>
  if i.val+1 ≤ cap ∧ (loop=true → 2 ≤ i.val+1) then halfWeight i else 0
lemma endpoint_energy_free (cap : ℕ) (loop : Bool) : vectorEnergy (endpoint cap loop) ≤ alphabetMass := by
  apply Finset.sum_le_sum
  intro i _
  unfold endpoint
  split_ifs
  · exact (halfWeight_sq i).le
  · simp only [zero_pow (by decide : 2≠0)]
    exact pow_nonneg radius_pos.le _
lemma endpoint_energy_loop (cap : ℕ) : vectorEnergy (endpoint cap true) ≤ loopMass := by
  have h : vectorEnergy (endpoint cap true) ≤ ∑ i : State,if 2 ≤ i.val+1 then radius^(i.val+1) else 0 := by
    apply Finset.sum_le_sum
    intro i _
    unfold endpoint
    split_ifs with hgate hhigh
    · exact (halfWeight_sq i).le
    · simp at hgate
      omega
    · simpa using pow_nonneg radius_pos.le (i.val+1)
    · simp
  have hs : (∑ i : State,if 2 ≤ i.val+1 then radius^(i.val+1) else 0)=loopMass := by
    norm_num [Fin.sum_univ_succ,loopMass]
    ring
  exact h.trans_eq hs

end SubmittedGenus.GoldenSpectral
