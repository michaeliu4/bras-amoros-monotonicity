import Results.Genus.CapFourMass.SchurBounds
import Mathlib.Data.Fin.VecNotation

/-! Exact submitted cap-four symmetric transfers and rational Schur certificates. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

abbrev State := Fin 4

def radius : ℝ := 1247/2000
def strongBound : ℝ := 23389/25000
def restrictedBound : ℝ := 72789/100000
def lambdaBound : ℝ := 101778011/100000000

def halfWeight (i : State) : ℝ := Real.sqrt (radius^(i.val+1))
def gate (threshold cap : ℕ) (i j : State) : Prop :=
  i.val+1 ≤ cap ∧ j.val+1 ≤ cap ∧ threshold ≤ (i.val+1)+(j.val+1)
instance (threshold cap : ℕ) (i j : State) : Decidable (gate threshold cap i j) := by
  unfold gate
  infer_instance

def transfer (threshold cap : ℕ) : Matrix State State ℝ :=
  fun i j => if gate threshold cap i j then halfWeight i*halfWeight j else 0

def strongMatrix : Matrix State State ℝ := transfer 4 4
def restrictedMatrix : Matrix State State ℝ := transfer 4 3
def carryMatrix : Matrix State State ℝ := transfer 3 3

def rationalTransfer (threshold cap : ℕ) : Matrix State State ℝ :=
  fun i j => if gate threshold cap i j then radius^(j.val+1) else 0

def halfScale (v : State → ℝ) : State → ℝ := fun i => halfWeight i*v i

lemma radius_pos : 0 < radius := by norm_num [radius]
lemma radius_lt_one : radius < 1 := by norm_num [radius]
lemma halfWeight_pos (i : State) : 0 < halfWeight i :=
  Real.sqrt_pos.mpr (pow_pos radius_pos _)
lemma halfWeight_sq (i : State) : (halfWeight i)^2 = radius^(i.val+1) :=
  Real.sq_sqrt (pow_nonneg radius_pos.le _)
lemma transfer_symmetric (t c : ℕ) : (transfer t c).transpose = transfer t c := by
  ext i j
  simp [transfer, Matrix.transpose_apply, gate, and_comm, and_left_comm, Nat.add_comm, mul_comm]
lemma transfer_nonneg (t c : ℕ) (i j : State) : 0 ≤ transfer t c i j := by
  unfold transfer
  split_ifs
  · exact mul_nonneg (halfWeight_pos i).le (halfWeight_pos j).le
  · rfl

/-- The actual half-weight transfer is diagonally conjugate to the rational
arriving-vertex transfer. No vertex weight is dropped in the conjugation. -/
lemma transfer_halfScale (t c : ℕ) (v : State → ℝ) :
    transfer t c *ᵥ halfScale v = halfScale (rationalTransfer t c *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, halfScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold transfer rationalTransfer
  split_ifs
  · calc
      halfWeight i*halfWeight j*(halfWeight j*v j) =
          halfWeight i*((halfWeight j)^2*v j) := by ring
      _ = _ := by rw [halfWeight_sq]
  · ring

/-- Original submitted positive strong test vector, in rational coordinates. -/
def strongTest : State → ℝ := ![1000000,1710962,2377416,2377416]
/-- Original restricted test, extended positively into its zero fourth row. -/
def restrictedTest : State → ℝ := ![1000000,2146345,3002947,1]

def strongInner : ℝ := strongBound-1/100000
def restrictedInner : ℝ := restrictedBound-1/100000

lemma strongTest_pos (i : State) : 0 < strongTest i := by fin_cases i <;> norm_num [strongTest]
lemma restrictedTest_pos (i : State) : 0 < restrictedTest i := by
  fin_cases i <;> norm_num [restrictedTest]

lemma strong_rational_row (i : State) :
    (rationalTransfer 4 4 *ᵥ strongTest) i ≤ strongInner*strongTest i := by
  fin_cases i <;> norm_num [rationalTransfer, gate, strongTest, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, radius, strongInner, strongBound]

lemma restricted_rational_row (i : State) :
    (rationalTransfer 4 3 *ᵥ restrictedTest) i ≤ restrictedInner*restrictedTest i := by
  fin_cases i <;> norm_num [rationalTransfer, gate, restrictedTest, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, radius, restrictedInner, restrictedBound]

lemma transfer_test_row (t c : ℕ) (v : State → ℝ) (R : ℝ)
    (hrow : ∀ i, (rationalTransfer t c *ᵥ v) i ≤ R*v i) (i : State) :
    (transfer t c *ᵥ halfScale v) i ≤ R*halfScale v i := by
  rw [transfer_halfScale]
  dsimp only [halfScale]
  have h := mul_le_mul_of_nonneg_left (hrow i) (halfWeight_pos i).le
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- A strict-margin bound for the genuine strong matrix, proved from the
paper's integer vector rather than an assumed norm or spectral oracle. -/
theorem strong_energy_inner (v : State → ℝ) :
    vectorEnergy (strongMatrix *ᵥ v) ≤ strongInner^2*vectorEnergy v := by
  exact positive_test_energy_le (transfer 4 4) (halfScale strongTest) strongInner
    (transfer_symmetric 4 4) (transfer_nonneg 4 4)
    (fun i => mul_pos (halfWeight_pos i) (strongTest_pos i))
    (by norm_num [strongInner, strongBound])
    (transfer_test_row 4 4 strongTest strongInner strong_rational_row) v

theorem restricted_energy_inner (v : State → ℝ) :
    vectorEnergy (restrictedMatrix *ᵥ v) ≤ restrictedInner^2*vectorEnergy v := by
  exact positive_test_energy_le (transfer 4 3) (halfScale restrictedTest) restrictedInner
    (transfer_symmetric 4 3) (transfer_nonneg 4 3)
    (fun i => mul_pos (halfWeight_pos i) (restrictedTest_pos i))
    (by norm_num [restrictedInner, restrictedBound])
    (transfer_test_row 4 3 restrictedTest restrictedInner restricted_rational_row) v

theorem strong_energy_le (v : State → ℝ) :
    vectorEnergy (strongMatrix *ᵥ v) ≤ strongBound^2*vectorEnergy v :=
  (strong_energy_inner v).trans (mul_le_mul_of_nonneg_right
    (by norm_num [strongInner, strongBound]) (vectorEnergy_nonneg v))

theorem restricted_energy_le (v : State → ℝ) :
    vectorEnergy (restrictedMatrix *ᵥ v) ≤ restrictedBound^2*vectorEnergy v :=
  (restricted_energy_inner v).trans (mul_le_mul_of_nonneg_right
    (by norm_num [restrictedInner, restrictedBound]) (vectorEnergy_nonneg v))

theorem strong_power_energy_le (n : ℕ) (v : State → ℝ) :
    vectorEnergy ((strongMatrix^n) *ᵥ v) ≤ strongBound^(2*n)*vectorEnergy v :=
  power_energy_le strongMatrix strongBound strong_energy_le n v

theorem strong_energy_lt {v : State → ℝ} (hv : 0 < vectorEnergy v) :
    vectorEnergy (strongMatrix *ᵥ v) < strongBound^2*vectorEnergy v :=
  (strong_energy_inner v).trans_lt (mul_lt_mul_of_pos_right
    (by norm_num [strongInner, strongBound]) hv)

theorem restricted_energy_lt {v : State → ℝ} (hv : 0 < vectorEnergy v) :
    vectorEnergy (restrictedMatrix *ᵥ v) < restrictedBound^2*vectorEnergy v :=
  (restricted_energy_inner v).trans_lt (mul_lt_mul_of_pos_right
    (by norm_num [restrictedInner, restrictedBound]) hv)

end SubmittedGenus.CapFourMass
