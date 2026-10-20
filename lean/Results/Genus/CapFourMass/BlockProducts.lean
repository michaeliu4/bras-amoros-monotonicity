import Results.Genus.CapFourMass.SpectralBlocks

/-! Absolute source-block products, including dimension-free cycle traces. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

lemma modeU_nonneg (i : Mode) : 0 ≤ modeU i := by fin_cases i <;> norm_num [modeU]
lemma modeV_nonneg (i : Mode) : 0 ≤ modeV i := by fin_cases i <;> norm_num [modeV]

def absoluteMatrix (A : Matrix Mode Mode ℝ) : Matrix Mode Mode ℝ := fun i j => |A i j|

/-- A rank-one entry majorant with its actual nonnegative source matrix. -/
structure DominatedBlock where
  matrix : Matrix Mode Mode ℝ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  matrix_nonneg : ∀ i j, 0 ≤ matrix i j
  entry_le : ∀ i j, matrix i j ≤ bound*modeU i*modeV j

/-- Absolute projected source block, never instantiated with a zero carry run. -/
def strongBlock (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) : DominatedBlock where
  matrix := absoluteMatrix (coupledBlock (strongMatrix^k) n)
  bound := strongBound^k*lam^n
  bound_nonneg := mul_nonneg (pow_nonneg strongBound_pos.le _) (pow_nonneg lam_pos.le _)
  matrix_nonneg := fun _ _ => abs_nonneg _
  entry_le := actual_strong_block k n hk hn

def restrictedBlock (n : ℕ) (hn : 1 ≤ n) : DominatedBlock where
  matrix := absoluteMatrix (coupledBlock restrictedMatrix n)
  bound := restrictedBound*lam^n
  bound_nonneg := mul_nonneg (by norm_num [restrictedBound]) (pow_nonneg lam_pos.le _)
  matrix_nonneg := fun _ _ => abs_nonneg _
  entry_le := actual_restricted_block n hn

lemma dominated_mul_entry (A B : DominatedBlock) (i j : Mode) :
    (A.matrix*B.matrix) i j ≤ (A.bound*B.bound)*modeU i*modeV j := by
  calc
    (A.matrix*B.matrix) i j ≤
        ∑ k, (A.bound*modeU i*modeV k)*(B.bound*modeU k*modeV j) := by
      rw [Matrix.mul_apply]
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul (A.entry_le i k) (B.entry_le k j) (B.matrix_nonneg k j)
        (mul_nonneg (mul_nonneg A.bound_nonneg (modeU_nonneg i)) (modeV_nonneg k))
    _ = ((A.bound*B.bound)*modeU i*modeV j)*(modeV ⬝ᵥ modeU) := by
      simp only [dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (A.bound*B.bound)*modeU i*modeV j := by
      apply mul_le_of_le_one_right
      · exact mul_nonneg (mul_nonneg (mul_nonneg A.bound_nonneg B.bound_nonneg)
          (modeU_nonneg i)) (modeV_nonneg j)
      · exact mode_overlap_lt_one.le

def DominatedBlock.mul (A B : DominatedBlock) : DominatedBlock where
  matrix := A.matrix*B.matrix
  bound := A.bound*B.bound
  bound_nonneg := mul_nonneg A.bound_nonneg B.bound_nonneg
  matrix_nonneg := by
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (A.matrix_nonneg i k) (B.matrix_nonneg k j)
  entry_le := dominated_mul_entry A B

/-- Nonempty products preserve the same rank-one majorant; every internal
mode junction contributes vᵀu<1 and hence introduces no extra factor. -/
def blockProduct (A : DominatedBlock) : List DominatedBlock → DominatedBlock
  | [] => A
  | B::l => blockProduct (A.mul B) l

lemma blockProduct_matrix (A : DominatedBlock) (l : List DominatedBlock) :
    (blockProduct A l).matrix = A.matrix*(l.map DominatedBlock.matrix).prod := by
  induction l generalizing A with
  | nil => simp [blockProduct]
  | cons B l ih =>
    simp only [blockProduct,ih,List.map_cons,List.prod_cons,DominatedBlock.mul]
    exact Matrix.mul_assoc _ _ _
lemma blockProduct_bound (A : DominatedBlock) (l : List DominatedBlock) :
    (blockProduct A l).bound = A.bound*(l.map DominatedBlock.bound).prod := by
  induction l generalizing A with
  | nil => simp [blockProduct]
  | cons B l ih =>
    simp only [blockProduct,ih,List.map_cons,List.prod_cons,DominatedBlock.mul]
    ring

lemma dominated_energy_le (A : DominatedBlock) : energy A.matrix ≤ A.bound^2 := by
  calc
    energy A.matrix ≤ ∑ i, ∑ j, (A.bound*modeU i*modeV j)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (A.matrix_nonneg i j) (A.entry_le i j) 2
    _ = A.bound^2*(vectorEnergy modeU*vectorEnergy modeV) := by
      simp only [vectorEnergy,mul_pow,← Finset.mul_sum,← Finset.sum_mul]
      ring
    _ ≤ A.bound^2 := mul_le_of_le_one_right (sq_nonneg _) mode_norm_product_lt_one.le

lemma energy_controls_vector (A : Matrix Mode Mode ℝ) (v : Mode → ℝ) :
    vectorEnergy (A *ᵥ v) ≤ energy A*vectorEnergy v := by
  calc
    vectorEnergy (A *ᵥ v) ≤ ∑ i, vectorEnergy (A i)*vectorEnergy v :=
      Finset.sum_le_sum fun i _ => dot_sq_le (A i) v
    _ = _ := by rw [← Finset.sum_mul]; rfl

lemma dominated_vector_energy (A : DominatedBlock) (v : Mode → ℝ) :
    vectorEnergy (A.matrix *ᵥ v) ≤ A.bound^2*vectorEnergy v :=
  (energy_controls_vector A.matrix v).trans (mul_le_mul_of_nonneg_right
    (dominated_energy_le A) (vectorEnergy_nonneg v))

lemma dominated_path_le (A : DominatedBlock) (x y : Mode → ℝ) :
    x ⬝ᵥ (A.matrix *ᵥ y) ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*A.bound := by
  apply le_of_sq_le_sq _ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)) A.bound_nonneg)
  have h := (dot_sq_le x (A.matrix *ᵥ y)).trans
    (mul_le_mul_of_nonneg_left (dominated_vector_energy A y) (vectorEnergy_nonneg x))
  simpa only [mul_pow,Real.sq_sqrt (vectorEnergy_nonneg x),
    Real.sq_sqrt (vectorEnergy_nonneg y),mul_assoc,mul_left_comm,mul_comm] using h

lemma dominated_trace_le (A : DominatedBlock) : A.matrix.trace ≤ A.bound := by
  calc
    A.matrix.trace ≤ ∑ i, A.bound*modeU i*modeV i :=
      Finset.sum_le_sum fun i _ => A.entry_le i i
    _ = A.bound*(modeV ⬝ᵥ modeU) := by
      simp only [dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ A.bound := mul_le_of_le_one_right A.bound_nonneg mode_overlap_lt_one.le

/-- Every nonempty cyclic spectral block product has the dimension-free
bound stated in the submitted paper, including a single strong/carry block. -/
theorem spectral_cycle_le (A : DominatedBlock) (l : List DominatedBlock) :
    (A.matrix*(l.map DominatedBlock.matrix).prod).trace ≤
      A.bound*(l.map DominatedBlock.bound).prod := by
  rw [← blockProduct_matrix,← blockProduct_bound]
  exact dominated_trace_le _

theorem spectral_path_le (A : DominatedBlock) (l : List DominatedBlock) (x y : Mode → ℝ) :
    x ⬝ᵥ ((A.matrix*(l.map DominatedBlock.matrix).prod) *ᵥ y) ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
        (A.bound*(l.map DominatedBlock.bound).prod) := by
  rw [← blockProduct_matrix,← blockProduct_bound]
  exact dominated_path_le _ _ _

end SubmittedGenus.CapFourMass
