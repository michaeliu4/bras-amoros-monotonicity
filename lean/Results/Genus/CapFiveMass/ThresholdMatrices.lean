import Results.Genus.CapFiveMass.MatrixBounds

/-!
# The actual cap-five strong and carry transfer matrices

Both matrices use the common five-state alphabet. Carry rows/columns at state5
are zero, so the four-state carry matrix is embedded exactly rather than
being replaced by a five-state relaxation of the carry alphabet.
-/

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass

abbrev State := Fin 5

def vertexHalf (z : ℝ) (i : State) : ℝ := Real.sqrt (z ^ (i.val + 1))

def eligible (t : ℕ) (i j : State) : Prop :=
  i.val + 1 ≤ t ∧ j.val + 1 ≤ t ∧ t ≤ (i.val + 1) + (j.val + 1)

instance (t : ℕ) (i j : State) : Decidable (eligible t i j) := by
  unfold eligible
  infer_instance

def thresholdMatrix (t : ℕ) (z : ℝ) : Matrix State State ℝ :=
  fun i j => if eligible t i j then vertexHalf z i * vertexHalf z j else 0

lemma threshold_symmetric (t : ℕ) (z : ℝ) :
    (thresholdMatrix t z).transpose = thresholdMatrix t z := by
  ext i j
  simp [Matrix.transpose_apply, thresholdMatrix, eligible, Nat.add_comm,
    and_comm, and_left_comm, mul_comm]

lemma threshold_nonneg (t : ℕ) (z : ℝ) (i j : State) : 0 ≤ thresholdMatrix t z i j := by
  unfold thresholdMatrix
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · rfl

lemma vertexHalf_sq {z : ℝ} (hz : 0 ≤ z) (i : State) : vertexHalf z i ^ 2 = z ^ (i.val + 1) :=
  Real.sq_sqrt (pow_nonneg hz _)

lemma four_entry_product {z : ℝ} (hz : 0 ≤ z) (t : ℕ) (i j k l : State) :
    thresholdMatrix t z i j * (thresholdMatrix t z j k *
      (thresholdMatrix t z k l * thresholdMatrix t z l i)) =
    if eligible t i j ∧ eligible t j k ∧ eligible t k l ∧ eligible t l i
    then z ^ ((i.val + 1) + (j.val + 1) + (k.val + 1) + (l.val + 1)) else 0 := by
  by_cases hij : eligible t i j <;> by_cases hjk : eligible t j k <;>
    by_cases hkl : eligible t k l <;> by_cases hli : eligible t l i <;>
    simp only [thresholdMatrix, hij, hjk, hkl, hli, and_self, and_true, and_false,
      false_and, true_and, ↓reduceIte, mul_zero, zero_mul]
  calc
    vertexHalf z i * vertexHalf z j * (vertexHalf z j * vertexHalf z k *
        (vertexHalf z k * vertexHalf z l * (vertexHalf z l * vertexHalf z i))) =
      vertexHalf z i ^ 2 * vertexHalf z j ^ 2 * vertexHalf z k ^ 2 * vertexHalf z l ^ 2 := by ring
    _ = _ := by simp only [vertexHalf_sq hz, pow_add]

def ambientFourthTrace (t : ℕ) (z : ℝ) : ℝ :=
  ∑ i : State, ∑ j : State, ∑ k : State, ∑ l : State,
    if eligible t i j ∧ eligible t j k ∧ eligible t k l ∧ eligible t l i
    then z ^ ((i.val + 1) + (j.val + 1) + (k.val + 1) + (l.val + 1)) else 0

lemma threshold_trace_fourth {z : ℝ} (hz : 0 ≤ z) (t : ℕ) :
    ((thresholdMatrix t z) ^ 4).trace = ambientFourthTrace t z := by
  have he (M : Matrix State State ℝ) : M ^ 4 = M * (M * (M * M)) := by noncomm_ring
  rw [he]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
  simp_rw [four_entry_product hz]
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma ambient_trace_five (z : ℝ) : ambientFourthTrace 5 z = fourthTrace 5 z := by
  norm_num [ambientFourthTrace, fourthTrace, eligible, Fin.sum_univ_succ]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma ambient_trace_four (z : ℝ) : ambientFourthTrace 4 z = fourthTrace 4 z := by
  norm_num [ambientFourthTrace, fourthTrace, eligible, Fin.sum_univ_succ]

/-- The submitted strong matrix at the submitted rational radius. -/
def strongTransfer : MatrixBounds.Controlled (ι := State) where
  matrix := thresholdMatrix 5 radius
  bound := strongBound
  bound_nonneg := norm_bound_order.1.le
  symmetric := threshold_symmetric 5 radius
  trace_le := by
    rw [threshold_trace_fourth radius_bounds.1.le, ambient_trace_five]
    exact fourthTrace_five_lt.le

/-- The submitted carry matrix, with its fifth row/column exactly zero. -/
def carryTransfer : MatrixBounds.Controlled (ι := State) where
  matrix := thresholdMatrix 4 radius
  bound := carryBound
  bound_nonneg := (norm_bound_order.1.trans norm_bound_order.2.1).le
  symmetric := threshold_symmetric 4 radius
  trace_le := by
    rw [threshold_trace_fourth radius_bounds.1.le, ambient_trace_four]
    exact fourthTrace_four_lt.le

inductive EndpointKind
  | free | strongLoop | carryLoop
  deriving DecidableEq, Fintype

def endpointVector (kind : EndpointKind) (z : ℝ) (i : State) : ℝ :=
  match kind with
  | .free => vertexHalf z i
  | .strongLoop => if 3 ≤ i.val + 1 then vertexHalf z i else 0
  | .carryLoop => if 2 ≤ i.val + 1 ∧ i.val + 1 ≤ 4 then vertexHalf z i else 0

def endpointBound : EndpointKind → ℝ
  | .free => alphabetMass 5 radius
  | .strongLoop => strongBound
  | .carryLoop => carryBound

lemma endpoint_energy (kind : EndpointKind) {z : ℝ} (hz : 0 ≤ z) :
    MatrixBounds.vectorEnergy (endpointVector kind z) =
      match kind with
      | .free => alphabetMass 5 z
      | .strongLoop => strongEndpoint z
      | .carryLoop => carryEndpoint z := by
  cases kind
  · simp only [MatrixBounds.vectorEnergy, endpointVector, vertexHalf_sq hz, alphabetMass]
  · norm_num [MatrixBounds.vectorEnergy, endpointVector, Fin.sum_univ_succ,
      vertexHalf_sq hz, strongEndpoint]
    ring
  · norm_num [MatrixBounds.vectorEnergy, endpointVector, Fin.sum_univ_succ,
      vertexHalf_sq hz, carryEndpoint]
    ring

lemma endpoint_energy_le (kind : EndpointKind) :
    MatrixBounds.vectorEnergy (endpointVector kind radius) ≤ endpointBound kind := by
  rw [endpoint_energy kind radius_bounds.1.le]
  cases kind
  · rfl
  · exact strong_endpoint_le
  · exact carry_endpoint_le

lemma endpointBound_nonneg (kind : EndpointKind) : 0 ≤ endpointBound kind :=
  (MatrixBounds.vectorEnergy_nonneg _).trans (endpoint_energy_le kind)

/-- All three genuine endpoint kinds satisfy the paper's Cauchy--Schwarz
factor, including self-pair restrictions on isolated vertices. -/
lemma source_endpoint_path_bound (l : List (MatrixBounds.Controlled (ι := State)))
    (left right : EndpointKind) :
    endpointVector left radius ⬝ᵥ (MatrixBounds.chain l *ᵥ endpointVector right radius) ≤
      Real.sqrt (endpointBound left) * Real.sqrt (endpointBound right) * MatrixBounds.chainBound l := by
  exact (MatrixBounds.path_le l _ _).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (Real.sqrt_le_sqrt (endpoint_energy_le left))
      (Real.sqrt_le_sqrt (endpoint_energy_le right)) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)) (MatrixBounds.chainBound_nonneg l))

end SubmittedGenus.CapFiveMass
