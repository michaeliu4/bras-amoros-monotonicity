import Results.Genus.CapFourMass.TwoModeBasis
import Results.Genus.GoldenSpectral.Endpoints

/-! The exact ordered-basis quantifier in the golden-q uniform block lemma.
All unit vectors in the respective nonzero eigenspaces are covered. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.GoldenSpectral
open CapFiveMass.MatrixBounds

lemma normalized_carry_eigenvector (j : Mode) (x : State→ℝ)
    (hx : vectorEnergy x=1)
    (he : carryMatrix*ᵥ x=fun i => modeRoot j*x i) :
    ∃ s : ℝ,|s|=1 ∧ x=fun i => s*modeVector j i := by
  have hm : mu<0 := by unfold mu; exact neg_neg_of_pos (sq_pos_of_pos radius_pos)
  fin_cases j
  · apply TwoModeBasis.unit_eigenvector_multiple carryMatrix qplus qminus x 1 mu
      one_ne_zero (by linarith) qplus_energy qminus_energy qplus_qminus hx _ he
    intro v
    simpa only [one_mul] using carry_modes v
  · apply TwoModeBasis.unit_eigenvector_multiple carryMatrix qminus qplus x mu 1
      (ne_of_lt hm) (by linarith) qminus_energy qplus_energy qminus_qplus hx _ he
    intro v
    rw [carry_modes]
    funext i
    ring

lemma ordered_coupled_abs_eq (Q : Matrix State Mode ℝ)
    (hunit : ∀ j,vectorEnergy (fun i => Q i j)=1)
    (heigen : ∀ j,carryMatrix*ᵥ (fun i => Q i j)=fun i => modeRoot j*Q i j)
    (A : Matrix State State ℝ) (n : ℕ) (i j : Mode) :
    |(Q.transpose*A*Q*Matrix.diagonal (fun j => modeRoot j^n)) i j|=
      |coupledBlock A n i j| := by
  obtain ⟨s,hs,hsi⟩:=normalized_carry_eigenvector i _ (hunit i) (heigen i)
  obtain ⟨t,ht,htj⟩:=normalized_carry_eigenvector j _ (hunit j) (heigen j)
  rw [Matrix.mul_diagonal,coupledBlock_entry,Matrix.mul_assoc]
  exact TwoModeBasis.coupled_entry_abs_invariant A (modeVector i) (modeVector j)
    (fun k => Q k i) (fun k => Q k j) s t (modeRoot j^n) hs ht hsi htj

/-- Original raw:block for every ordered orthonormal basis of the nonzero
carry eigenspaces, including every sign choice. -/
theorem actual_strong_block_ordered (Q : Matrix State Mode ℝ)
    (hunit : ∀ j,vectorEnergy (fun i => Q i j)=1)
    (heigen : ∀ j,carryMatrix*ᵥ (fun i => Q i j)=fun i => modeRoot j*Q i j)
    (k n : ℕ) (hk : 1≤k) (hn : 1≤n) (i j : Mode) :
    |(Q.transpose*(strongMatrix^k)*Q*Matrix.diagonal (fun j => modeRoot j^n)) i j|≤
      strongBound^(k-3)*modeU i*modeV j := by
  rw [ordered_coupled_abs_eq Q hunit heigen]
  exact actual_strong_block k n hk hn i j

lemma ordered_basis_four (Q : Matrix State Mode ℝ)
    (hunit : ∀ j,vectorEnergy (fun i => Q i j)=1)
    (heigen : ∀ j,carryMatrix*ᵥ (fun i => Q i j)=fun i => modeRoot j*Q i j)
    (j : Mode) : Q 3 j=0 := by
  obtain ⟨s,_,hs⟩:=normalized_carry_eigenvector j _ (hunit j) (heigen j)
  simpa only [modeVector_last,mul_zero] using congrFun hs 3

lemma ordered_projected_restricted_eq (Q : Matrix State Mode ℝ)
    (hunit : ∀ j,vectorEnergy (fun i => Q i j)=1)
    (heigen : ∀ j,carryMatrix*ᵥ (fun i => Q i j)=fun i => modeRoot j*Q i j) :
    Q.transpose*restrictedMatrix*Q=Q.transpose*strongMatrix*Q := by
  ext i j
  rw [Matrix.mul_assoc,Matrix.mul_assoc]
  change (fun k => Q k i) ⬝ᵥ (restrictedMatrix*ᵥ fun k => Q k j)=
    (fun k => Q k i) ⬝ᵥ (strongMatrix*ᵥ fun k => Q k j)
  have hi:=ordered_basis_four Q hunit heigen i
  have hj:=ordered_basis_four Q hunit heigen j
  norm_num [restrictedMatrix,strongMatrix,transfer,gate,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,Fin.succ,hi,hj]
  have hi' : Q (⟨3,by decide⟩ : Fin 4) i=0 := hi
  have hj' : Q (⟨3,by decide⟩ : Fin 4) j=0 := hj
  simp only [hi',hj',mul_zero,zero_mul,add_zero]

/-- Matrix-form orthonormality supplies the unit-column hypotheses. -/
lemma ordered_columns_unit (Q : Matrix State Mode ℝ) (hQ : Q.transpose*Q=1) (j : Mode) :
    vectorEnergy (fun i => Q i j)=1 := by
  have hh:=congrFun (congrFun hQ j) j
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,
    vectorEnergy,pow_two] using hh

/-- Literal orthonormal-matrix form of the original ordered-basis quantifier. -/
theorem actual_strong_block_orthonormal (Q : Matrix State Mode ℝ)
    (hQ : Q.transpose*Q=1)
    (heigen : ∀ j,carryMatrix*ᵥ (fun i => Q i j)=fun i => modeRoot j*Q i j)
    (k n : ℕ) (hk : 1≤k) (hn : 1≤n) (i j : Mode) :
    |(Q.transpose*(strongMatrix^k)*Q*Matrix.diagonal (fun j => modeRoot j^n)) i j|≤
      strongBound^(k-3)*modeU i*modeV j :=
  actual_strong_block_ordered Q (ordered_columns_unit Q hQ) heigen k n hk hn i j

lemma projected_restricted_eq_orthonormal (Q : Matrix State Mode ℝ)
    (hQ : Q.transpose*Q=1)
    (heigen : ∀ j,carryMatrix*ᵥ (fun i => Q i j)=fun i => modeRoot j*Q i j) :
    Q.transpose*restrictedMatrix*Q=Q.transpose*strongMatrix*Q :=
  ordered_projected_restricted_eq Q (ordered_columns_unit Q hQ) heigen

end SubmittedGenus.GoldenSpectral
