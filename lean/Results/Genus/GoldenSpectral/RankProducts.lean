import Results.Genus.GoldenSpectral.Blocks

/-! Golden-q paid block products retain one exact overlap per strong run.
Cycles have no dimension factor; every path has only the submitted k0 inflation. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.GoldenSpectral
open CapFiveMass.MatrixBounds

def overlap : ℝ := 10918/15625
def pathInflation : ℝ := 10003/10000
def gapDecay : ℝ := 47597/50000
def tiltBound : ℝ := 95761/100000
def normalizedV (i : Mode) : ℝ := modeV i/overlap

lemma overlap_pos : 0<overlap := by norm_num [overlap]
lemma pathInflation_pos : 0<pathInflation := by norm_num [pathInflation]
lemma modeU_nonneg (i : Mode) : 0≤modeU i := by fin_cases i <;> norm_num [modeU]
lemma normalizedV_nonneg (i : Mode) : 0≤normalizedV i := by fin_cases i <;> norm_num [normalizedV,modeV,overlap]
lemma normalized_overlap_eq_one : normalizedV ⬝ᵥ modeU=1 := by
  norm_num [normalizedV,modeV,modeU,overlap,dotProduct,Fin.sum_univ_succ]
lemma normalized_norm_product_lt :
    vectorEnergy modeU*vectorEnergy normalizedV<pathInflation^2 := by
  norm_num [vectorEnergy,normalizedV,modeV,modeU,overlap,pathInflation,Fin.sum_univ_succ]

lemma paid_decay_comparisons : overlap/strongBound^3<gapDecay^2 ∧ gapDecay^2<1 ∧
    (19/25:ℝ)<strongBound^3 ∧ gapDecay<tiltBound ∧ strongBound<tiltBound^2 := by
  norm_num [overlap,strongBound,gapDecay,tiltBound]

def absoluteMatrix (A : Matrix Mode Mode ℝ) : Matrix Mode Mode ℝ := fun i j => |A i j|

/-- A rank-one entry majorant with its actual nonnegative source matrix. -/
structure DominatedBlock where
  matrix : Matrix Mode Mode ℝ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  matrix_nonneg : ∀ i j, 0 ≤ matrix i j
  entry_le : ∀ i j, matrix i j ≤ bound*modeU i*normalizedV j

/-- Absolute projected source block, never instantiated with a zero carry run. -/
def strongBlock (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) : DominatedBlock where
  matrix := absoluteMatrix (coupledBlock (strongMatrix^k) n)
  bound := strongBound^(k-3)*overlap
  bound_nonneg := mul_nonneg (pow_nonneg strongBound_pos.le _) overlap_pos.le
  matrix_nonneg := fun _ _ => abs_nonneg _
  entry_le := by
    intro i j
    have hh:=actual_strong_block k n hk hn i j
    exact hh.trans_eq (by unfold normalizedV; field_simp [ne_of_gt overlap_pos] <;> ring)

def restrictedBlock (n : ℕ) (hn : 1 ≤ n) : DominatedBlock where
  matrix := absoluteMatrix (coupledBlock restrictedMatrix n)
  bound := overlap
  bound_nonneg := overlap_pos.le
  matrix_nonneg := fun _ _ => abs_nonneg _
  entry_le := by
    intro i j
    have hh:=actual_strong_block 1 n (by norm_num) hn i j
    simp only [pow_one,show 1-3=0 by omega,pow_zero,one_mul] at hh
    unfold coupledBlock at hh ⊢
    rw [projected_restricted_eq]
    exact hh.trans_eq (by unfold normalizedV; field_simp [ne_of_gt overlap_pos] <;> ring)

lemma dominated_mul_entry (A B : DominatedBlock) (i j : Mode) :
    (A.matrix*B.matrix) i j ≤ (A.bound*B.bound)*modeU i*normalizedV j := by
  calc
    (A.matrix*B.matrix) i j ≤
        ∑ k, (A.bound*modeU i*normalizedV k)*(B.bound*modeU k*normalizedV j) := by
      rw [Matrix.mul_apply]
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul (A.entry_le i k) (B.entry_le k j) (B.matrix_nonneg k j)
        (mul_nonneg (mul_nonneg A.bound_nonneg (modeU_nonneg i)) (normalizedV_nonneg k))
    _ = ((A.bound*B.bound)*modeU i*normalizedV j)*(normalizedV ⬝ᵥ modeU) := by
      simp only [dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (A.bound*B.bound)*modeU i*normalizedV j := by
      apply mul_le_of_le_one_right
      · exact mul_nonneg (mul_nonneg (mul_nonneg A.bound_nonneg B.bound_nonneg)
          (modeU_nonneg i)) (normalizedV_nonneg j)
      · exact normalized_overlap_eq_one.le

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

/-- Normalizing the right vector by ν makes the internal overlap exactly one;
the paid scalar bound retains one original ν factor for every block. -/
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

lemma dominated_energy_le (A : DominatedBlock) : energy A.matrix ≤ (pathInflation*A.bound)^2 := by
  calc
    energy A.matrix ≤ ∑ i, ∑ j, (A.bound*modeU i*normalizedV j)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (A.matrix_nonneg i j) (A.entry_le i j) 2
    _ = A.bound^2*(vectorEnergy modeU*vectorEnergy normalizedV) := by
      simp only [vectorEnergy,mul_pow,← Finset.mul_sum,← Finset.sum_mul]
      ring
    _ ≤ (pathInflation*A.bound)^2 := by
      have h:=mul_le_mul_of_nonneg_left normalized_norm_product_lt.le (sq_nonneg A.bound)
      simpa only [mul_pow,mul_comm] using h

lemma energy_controls_vector (A : Matrix Mode Mode ℝ) (v : Mode → ℝ) :
    vectorEnergy (A *ᵥ v) ≤ energy A*vectorEnergy v := by
  calc
    vectorEnergy (A *ᵥ v) ≤ ∑ i, vectorEnergy (A i)*vectorEnergy v :=
      Finset.sum_le_sum fun i _ => dot_sq_le (A i) v
    _ = _ := by rw [← Finset.sum_mul]; rfl

lemma dominated_vector_energy (A : DominatedBlock) (v : Mode → ℝ) :
    vectorEnergy (A.matrix *ᵥ v) ≤ (pathInflation*A.bound)^2*vectorEnergy v :=
  (energy_controls_vector A.matrix v).trans (mul_le_mul_of_nonneg_right
    (dominated_energy_le A) (vectorEnergy_nonneg v))

lemma dominated_path_le (A : DominatedBlock) (x y : Mode → ℝ) :
    x ⬝ᵥ (A.matrix *ᵥ y) ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*(pathInflation*A.bound) := by
  apply le_of_sq_le_sq _ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)) (mul_nonneg pathInflation_pos.le A.bound_nonneg))
  have h := (dot_sq_le x (A.matrix *ᵥ y)).trans
    (mul_le_mul_of_nonneg_left (dominated_vector_energy A y) (vectorEnergy_nonneg x))
  simpa only [mul_pow,Real.sq_sqrt (vectorEnergy_nonneg x),
    Real.sq_sqrt (vectorEnergy_nonneg y),mul_assoc,mul_left_comm,mul_comm] using h

lemma dominated_trace_le (A : DominatedBlock) : A.matrix.trace ≤ A.bound := by
  calc
    A.matrix.trace ≤ ∑ i, A.bound*modeU i*normalizedV i :=
      Finset.sum_le_sum fun i _ => A.entry_le i i
    _ = A.bound*(normalizedV ⬝ᵥ modeU) := by
      simp only [dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ A.bound := mul_le_of_le_one_right A.bound_nonneg normalized_overlap_eq_one.le

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
        (pathInflation*(A.bound*(l.map DominatedBlock.bound).prod)) := by
  rw [← blockProduct_matrix,← blockProduct_bound]
  exact dominated_path_le _ _ _

end SubmittedGenus.GoldenSpectral
