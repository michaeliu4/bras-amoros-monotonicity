import Results.Genus.GoldenSpectral.Matrices

/-! The two actual golden-q carry modes, orthonormality and exact eigenvalues.
Their common positive normalization is q(1+q²), so these are the manuscript's
vectors without changing either signed mode. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.GoldenSpectral
open CapFiveMass.MatrixBounds

def mu : ℝ := -radius^2
def modeNorm : ℝ := radius+radius^3
def plusVector : State→ℝ := ![radius,1,1,0]
def minusVector : State→ℝ := ![1,-radius,-radius,0]
def plusRaw : State→ℝ := halfScale plusVector
def minusRaw : State→ℝ := halfScale minusVector
def qplus : State→ℝ := fun i => plusRaw i/Real.sqrt modeNorm
def qminus : State→ℝ := fun i => minusRaw i/Real.sqrt modeNorm

lemma modeNorm_pos : 0<modeNorm := add_pos radius_pos (pow_pos radius_pos 3)
lemma modeNorm_eq : modeNorm=radius*(1+radius^2) := by unfold modeNorm; ring

lemma halfScale_dot (v w : State→ℝ) :
    halfScale v ⬝ᵥ halfScale w=∑ i,radius^(i.val+1)*v i*w i := by
  unfold dotProduct halfScale
  apply Finset.sum_congr rfl
  intro i _
  calc
    halfWeight i*v i*(halfWeight i*w i)=(halfWeight i)^2*v i*w i := by ring
    _ = _ := by rw [halfWeight_sq]

lemma vectorEnergy_eq_dot (v : State→ℝ) : vectorEnergy v=v ⬝ᵥ v := by
  simp [vectorEnergy,dotProduct,pow_two]

lemma plusRaw_energy : vectorEnergy plusRaw=modeNorm := by
  rw [vectorEnergy_eq_dot,plusRaw,halfScale_dot]
  norm_num [plusVector,Fin.sum_univ_succ,modeNorm]
  nlinarith [radius_pow_two,radius_pow_three]
lemma minusRaw_energy : vectorEnergy minusRaw=modeNorm := by
  rw [vectorEnergy_eq_dot,minusRaw,halfScale_dot]
  norm_num [minusVector,Fin.sum_univ_succ,modeNorm]
  nlinarith [radius_pow_two,radius_pow_three,radius_pow_four,radius_pow_five]
lemma plusRaw_minusRaw : plusRaw ⬝ᵥ minusRaw=0 := by
  rw [plusRaw,minusRaw,halfScale_dot]
  norm_num [plusVector,minusVector,Fin.sum_univ_succ]
  nlinarith [radius_pow_two,radius_pow_three,radius_pow_four]

lemma qplus_energy : vectorEnergy qplus=1 := by
  simp only [qplus,vectorEnergy,div_pow,← Finset.sum_div]
  change vectorEnergy plusRaw/(Real.sqrt modeNorm)^2=1
  rw [Real.sq_sqrt modeNorm_pos.le,plusRaw_energy]
  exact div_self (ne_of_gt modeNorm_pos)
lemma qminus_energy : vectorEnergy qminus=1 := by
  simp only [qminus,vectorEnergy,div_pow,← Finset.sum_div]
  change vectorEnergy minusRaw/(Real.sqrt modeNorm)^2=1
  rw [Real.sq_sqrt modeNorm_pos.le,minusRaw_energy]
  exact div_self (ne_of_gt modeNorm_pos)
lemma qplus_qminus : qplus ⬝ᵥ qminus=0 := by
  simp only [qplus,qminus,dotProduct,div_mul_div_comm,← Finset.sum_div]
  change (plusRaw ⬝ᵥ minusRaw)/_=0
  rw [plusRaw_minusRaw,zero_div]
lemma qplus_self : qplus ⬝ᵥ qplus=1 := by rw [← vectorEnergy_eq_dot,qplus_energy]
lemma qminus_self : qminus ⬝ᵥ qminus=1 := by rw [← vectorEnergy_eq_dot,qminus_energy]

lemma plusVector_eigen : rationalTransfer 3 3 *ᵥ plusVector=plusVector := by
  funext i
  fin_cases i <;> norm_num [rationalTransfer,gate,Matrix.mulVec,dotProduct,plusVector,Fin.sum_univ_succ] <;>
    nlinarith [radius_pow_two,radius_pow_three]
lemma minusVector_eigen : rationalTransfer 3 3 *ᵥ minusVector=fun i => mu*minusVector i := by
  funext i
  fin_cases i <;> norm_num [rationalTransfer,gate,Matrix.mulVec,dotProduct,minusVector,mu,Fin.sum_univ_succ] <;>
    nlinarith [radius_pow_two,radius_pow_three,radius_pow_four]

lemma halfScale_scale (c : ℝ) (v : State→ℝ) :
    halfScale (fun i => c*v i)=fun i => c*halfScale v i := by
  funext i
  simp only [halfScale]
  ring
lemma matrix_mulVec_div (A : Matrix State State ℝ) (v : State→ℝ) (c : ℝ) :
    A *ᵥ (fun i => v i/c)=fun i => (A *ᵥ v) i/c := by
  funext i
  simp only [Matrix.mulVec,dotProduct,mul_div_assoc,Finset.sum_div]
lemma qplus_eigen : carryMatrix *ᵥ qplus=qplus := by
  unfold qplus
  rw [matrix_mulVec_div,plusRaw,carryMatrix,transfer_halfScale,plusVector_eigen]
lemma qminus_eigen : carryMatrix *ᵥ qminus=fun i => mu*qminus i := by
  unfold qminus
  rw [matrix_mulVec_div,minusRaw,carryMatrix,transfer_halfScale,minusVector_eigen,halfScale_scale]
  funext i
  ring

lemma mu_abs : |mu|=radius^2 := by unfold mu; rw [abs_neg,abs_of_nonneg (sq_nonneg _)]
lemma mu_abs_lt : |mu|<191/500 := by rw [mu_abs,radius_pow_two]; linarith [radius_lower]

lemma raw_mode_entry (i j : State) :
    plusVector i*plusVector j+mu*minusVector i*minusVector j=
      if gate 3 3 i j then modeNorm else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [plusVector,minusVector,mu,modeNorm,gate] <;>
    nlinarith [radius_pow_two,radius_pow_three,radius_pow_four]

lemma carry_matrix_modes (i j : State) :
    carryMatrix i j=qplus i*qplus j+mu*qminus i*qminus j := by
  have hp : qplus i*qplus j=plusRaw i*plusRaw j/modeNorm := by
    rw [qplus,qplus,div_mul_div_comm,← pow_two,Real.sq_sqrt modeNorm_pos.le]
  have hm : qminus i*qminus j=minusRaw i*minusRaw j/modeNorm := by
    rw [qminus,qminus,div_mul_div_comm,← pow_two,Real.sq_sqrt modeNorm_pos.le]
  have he:=congrArg (fun x : ℝ => halfWeight i*halfWeight j*x) (raw_mode_entry i j)
  rw [hp,show mu*qminus i*qminus j=mu*(qminus i*qminus j) by ring,hm]
  unfold plusRaw minusRaw halfScale at *
  unfold carryMatrix transfer
  split_ifs at * <;> field_simp [ne_of_gt modeNorm_pos] <;> nlinarith [he]

end SubmittedGenus.GoldenSpectral
