import Results.Genus.CapFiveMass.Numerics
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Elementary finite-matrix fourth-trace contraction

Squared finite Cauchy--Schwarz proves the only Schatten inequalities needed
by the submitted cap-five argument. No spectral approximation is involved.
-/

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass
namespace MatrixBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The squared Euclidean norm. -/
def vectorEnergy (v : ι → ℝ) : ℝ := ∑ i, (v i) ^ 2
/-- The squared Hilbert--Schmidt norm. -/
def energy (A : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, (A i j) ^ 2

lemma vectorEnergy_nonneg (v : ι → ℝ) : 0 ≤ vectorEnergy v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma energy_nonneg (A : Matrix ι ι ℝ) : 0 ≤ energy A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma energy_transpose (A : Matrix ι ι ℝ) : energy A.transpose = energy A := by
  unfold energy
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

lemma energy_eq_trace (A : Matrix ι ι ℝ) : energy A = (A.transpose * A).trace := by
  unfold energy Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, ← sq]
  exact Finset.sum_comm

/-- Squared Cauchy--Schwarz for the actual finite matrix entries. -/
lemma trace_mul_sq_le (A B : Matrix ι ι ℝ) :
    (A * B).trace ^ 2 ≤ energy A * energy B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun x => A x.1 x.2) (fun x => B x.2 x.1)
  simp only [Fintype.sum_prod_type] at h
  rw [Finset.sum_comm (f := fun i j => B j i ^ 2)] at h
  simpa only [energy, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] using h

lemma energy_mul_eq_trace (A B : Matrix ι ι ℝ) :
    energy (A * B) = (A.transpose * A * (B * B.transpose)).trace := by
  rw [energy_eq_trace, Matrix.transpose_mul]
  calc
    (B.transpose * A.transpose * (A * B)).trace =
        (B.transpose * (A.transpose * A * B)).trace := by rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (A.transpose * A * B * B.transpose).trace := Matrix.trace_mul_comm _ _
    _ = _ := by rw [Matrix.mul_assoc]

/-- Hilbert--Schmidt of a pair is controlled by the fourth traces. -/
lemma energy_mul_sq_le (A B : Matrix ι ι ℝ) :
    energy (A * B) ^ 2 ≤ energy (A.transpose * A) * energy (B * B.transpose) := by
  rw [energy_mul_eq_trace]
  exact trace_mul_sq_le _ _

lemma symmetric_energy_sq (A : Matrix ι ι ℝ) (hA : A.transpose = A) :
    energy (A * A) = (A ^ 4).trace := by
  rw [energy_eq_trace, Matrix.transpose_mul, hA]
  congr 1
  noncomm_ring

/-- The two-factor fourth-norm inequality, with the norm bound represented
as its exact fourth-power trace comparison. -/
lemma pair_energy_le {A B : Matrix ι ι ℝ} {a b : ℝ}
    (hA : A.transpose = A) (hB : B.transpose = B)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hqa : (A ^ 4).trace ≤ a ^ 4) (hqb : (B ^ 4).trace ≤ b ^ 4) :
    energy (A * B) ≤ (a * b) ^ 2 := by
  have h := energy_mul_sq_le A B
  rw [hA, hB, symmetric_energy_sq A hA, symmetric_energy_sq B hB] at h
  have hna : 0 ≤ (A ^ 4).trace := by rw [← symmetric_energy_sq A hA]; exact energy_nonneg _
  have hnb : 0 ≤ (B ^ 4).trace := by rw [← symmetric_energy_sq B hB]; exact energy_nonneg _
  have hprod := mul_le_mul hqa hqb hnb (pow_nonneg ha 4)
  have he := energy_nonneg (A * B)
  have hab : 0 ≤ (a * b) ^ 2 := sq_nonneg _
  have hpow : a ^ 4 * b ^ 4 = ((a * b) ^ 2) ^ 2 := by ring
  rw [hpow] at hprod
  nlinarith

/-- Squared vector Cauchy--Schwarz. -/
lemma dot_sq_le (x y : ι → ℝ) :
    (x ⬝ᵥ y) ^ 2 ≤ vectorEnergy x * vectorEnergy y :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y

lemma vectorEnergy_mulVec_eq (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    vectorEnergy (A *ᵥ x) = x ⬝ᵥ ((A.transpose * A) *ᵥ x) := by
  have he (v : ι → ℝ) : vectorEnergy v = v ⬝ᵥ v := by simp [vectorEnergy, dotProduct, pow_two]
  rw [he]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]

lemma quadratic_sq_le (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    (x ⬝ᵥ (A *ᵥ x)) ^ 2 ≤ energy A * (vectorEnergy x) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun ij => A ij.1 ij.2) (fun ij => x ij.1 * x ij.2)
  simp only [Fintype.sum_prod_type] at h
  have hs : (∑ i, ∑ j, (x i * x j) ^ 2) = vectorEnergy x ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, vectorEnergy]
    ring
  rw [hs] at h
  have he : x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, A i j * (x i * x j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact h

/-- An exact fourth-trace bound also controls the Euclidean operator norm. -/
lemma vectorEnergy_mulVec_le {A : Matrix ι ι ℝ} {a : ℝ}
    (hA : A.transpose = A) (ha : 0 ≤ a) (hqa : (A ^ 4).trace ≤ a ^ 4)
    (x : ι → ℝ) : vectorEnergy (A *ᵥ x) ≤ a ^ 2 * vectorEnergy x := by
  have h := quadratic_sq_le (A.transpose * A) x
  rw [← vectorEnergy_mulVec_eq, hA, symmetric_energy_sq A hA] at h
  have hm := mul_le_mul_of_nonneg_right hqa (sq_nonneg (vectorEnergy x))
  have hp : a ^ 4 * vectorEnergy x ^ 2 = (a ^ 2 * vectorEnergy x) ^ 2 := by ring
  rw [hp] at hm
  have hv := vectorEnergy_nonneg (A *ᵥ x)
  have hw : 0 ≤ a ^ 2 * vectorEnergy x := mul_nonneg (sq_nonneg a) (vectorEnergy_nonneg x)
  nlinarith

/-- A real symmetric transfer and its proved fourth-trace bound. -/
structure Controlled where
  matrix : Matrix ι ι ℝ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  symmetric : matrix.transpose = matrix
  trace_le : (matrix ^ 4).trace ≤ bound ^ 4

def chain (l : List (Controlled (ι := ι))) : Matrix ι ι ℝ := (l.map Controlled.matrix).prod
def chainBound (l : List (Controlled (ι := ι))) : ℝ := (l.map Controlled.bound).prod

@[simp] lemma chain_nil : chain ([] : List (Controlled (ι := ι))) = 1 := rfl
@[simp] lemma chain_cons (A : Controlled (ι := ι)) (l) :
    chain (A :: l) = A.matrix * chain l := rfl
@[simp] lemma chainBound_nil : chainBound ([] : List (Controlled (ι := ι))) = 1 := rfl
@[simp] lemma chainBound_cons (A : Controlled (ι := ι)) (l) :
    chainBound (A :: l) = A.bound * chainBound l := rfl

lemma chainBound_nonneg (l : List (Controlled (ι := ι))) : 0 ≤ chainBound l := by
  induction l with
  | nil => simp
  | cons A l ih => exact mul_nonneg A.bound_nonneg ih

lemma energy_mul_right_le (M : Matrix ι ι ℝ) (A : Controlled (ι := ι)) :
    energy (M * A.matrix) ≤ A.bound ^ 2 * energy M := by
  have he (i) : (M * A.matrix) i = A.matrix *ᵥ M i := by
    rw [Matrix.mul_apply_eq_vecMul, ← Matrix.mulVec_transpose, A.symmetric]
  change (∑ i, vectorEnergy ((M * A.matrix) i)) ≤ _
  simp_rw [he]
  calc
    (∑ i, vectorEnergy (A.matrix *ᵥ M i)) ≤ ∑ i, A.bound ^ 2 * vectorEnergy (M i) :=
      Finset.sum_le_sum fun i _ => vectorEnergy_mulVec_le A.symmetric A.bound_nonneg A.trace_le (M i)
    _ = A.bound ^ 2 * energy M := by rw [← Finset.mul_sum]; rfl

lemma energy_mul_chain_le (M : Matrix ι ι ℝ) (l : List (Controlled (ι := ι))) :
    energy (M * chain l) ≤ chainBound l ^ 2 * energy M := by
  induction l generalizing M with
  | nil => simp
  | cons A l ih =>
    rw [chain_cons, ← Matrix.mul_assoc]
    calc
      energy (M * A.matrix * chain l) ≤ chainBound l ^ 2 * energy (M * A.matrix) := ih _
      _ ≤ chainBound l ^ 2 * (A.bound ^ 2 * energy M) :=
        mul_le_mul_of_nonneg_left (energy_mul_right_le M A) (sq_nonneg _)
      _ = chainBound (A :: l) ^ 2 * energy M := by rw [chainBound_cons]; ring

lemma vectorEnergy_chain_le (l : List (Controlled (ι := ι))) (x : ι → ℝ) :
    vectorEnergy (chain l *ᵥ x) ≤ chainBound l ^ 2 * vectorEnergy x := by
  induction l with
  | nil => simp
  | cons A l ih =>
    rw [chain_cons, ← Matrix.mulVec_mulVec]
    calc
      vectorEnergy (A.matrix *ᵥ (chain l *ᵥ x)) ≤ A.bound ^ 2 * vectorEnergy (chain l *ᵥ x) :=
        vectorEnergy_mulVec_le A.symmetric A.bound_nonneg A.trace_le _
      _ ≤ A.bound ^ 2 * (chainBound l ^ 2 * vectorEnergy x) :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = chainBound (A :: l) ^ 2 * vectorEnergy x := by rw [chainBound_cons]; ring

/-- Path bound, also valid for the empty edge list (one physical vertex). -/
lemma path_le (l : List (Controlled (ι := ι))) (x y : ι → ℝ) :
    x ⬝ᵥ (chain l *ᵥ y) ≤ Real.sqrt (vectorEnergy x) *
      Real.sqrt (vectorEnergy y) * chainBound l := by
  apply le_of_sq_le_sq _ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (chainBound_nonneg l))
  have h := (dot_sq_le x (chain l *ᵥ y)).trans
    (mul_le_mul_of_nonneg_left (vectorEnergy_chain_le l y) (vectorEnergy_nonneg x))
  simpa only [mul_pow, Real.sq_sqrt (vectorEnergy_nonneg x),
    Real.sq_sqrt (vectorEnergy_nonneg y), mul_assoc, mul_left_comm, mul_comm] using h

lemma pair_chain_energy_le (A B : Controlled (ι := ι)) (l : List (Controlled (ι := ι))) :
    energy (A.matrix * B.matrix * chain l) ≤ (A.bound * B.bound * chainBound l) ^ 2 := by
  calc
    energy (A.matrix * B.matrix * chain l) ≤ chainBound l ^ 2 * energy (A.matrix * B.matrix) :=
      energy_mul_chain_le _ _
    _ ≤ chainBound l ^ 2 * (A.bound * B.bound) ^ 2 := mul_le_mul_of_nonneg_left
      (pair_energy_le A.symmetric B.symmetric A.bound_nonneg B.bound_nonneg A.trace_le B.trace_le)
      (sq_nonneg _)
    _ = _ := by ring

/-- A cycle of at least four edges has no dimension factor. The first four
factors supply two Hilbert--Schmidt pairs; all later factors contract in
Euclidean operator norm. This proves the submitted Schatten step directly. -/
lemma cycle_four_plus_le (A B C D : Controlled (ι := ι))
    (l : List (Controlled (ι := ι))) :
    (A.matrix * B.matrix * C.matrix * D.matrix * chain l).trace ≤
      A.bound * B.bound * C.bound * D.bound * chainBound l := by
  have ht := trace_mul_sq_le (A.matrix * B.matrix) (C.matrix * D.matrix * chain l)
  have ha := pair_energy_le A.symmetric B.symmetric A.bound_nonneg B.bound_nonneg A.trace_le B.trace_le
  have hb := pair_chain_energy_le C D l
  have hh := mul_le_mul ha hb (energy_nonneg _) (sq_nonneg _)
  have he : (A.bound * B.bound) ^ 2 * (C.bound * D.bound * chainBound l) ^ 2 =
      (A.bound * B.bound * C.bound * D.bound * chainBound l) ^ 2 := by ring
  rw [he] at hh
  apply le_of_sq_le_sq _ (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    A.bound_nonneg B.bound_nonneg) C.bound_nonneg) D.bound_nonneg) (chainBound_nonneg l))
  simpa only [Matrix.mul_assoc] using ht.trans hh

lemma cycle_le (l : List (Controlled (ι := ι))) (hl : 4 ≤ l.length) :
    (chain l).trace ≤ chainBound l := by
  rcases l with _ | ⟨A, l⟩ <;> simp only [List.length_nil, List.length_cons] at hl
  · omega
  rcases l with _ | ⟨B, l⟩ <;> simp only [List.length_nil, List.length_cons] at hl
  · omega
  rcases l with _ | ⟨C, l⟩ <;> simp only [List.length_nil, List.length_cons] at hl
  · omega
  rcases l with _ | ⟨D, l⟩ <;> simp only [List.length_nil, List.length_cons] at hl
  · omega
  simpa only [chain_cons, chainBound_cons, Matrix.mul_assoc, mul_assoc] using cycle_four_plus_le A B C D l

end MatrixBounds
end SubmittedGenus.CapFiveMass
