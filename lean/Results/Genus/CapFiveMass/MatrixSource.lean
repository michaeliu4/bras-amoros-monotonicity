import Results.Genus.CapFiveMass.ThresholdMatrices
import Results.Genus.RawGraph.Transfer

/-!
# Exact path matrix evaluation with one weight per source coordinate

Splitting a vertex weight between its two incidences is justified by an
identity of complete finite source sums. In particular an isolated vertex
receives two half factors and exactly one full vertex weight.
-/

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass
namespace MatrixSource

open RawGraph.Transfer
variable {A : Type*} [Fintype A] [DecidableEq A]

def matrixRun : ℕ → (ℕ → Matrix A A ℝ) → Matrix A A ℝ
  | 0, _ => 1
  | n + 1, E => E 0 * matrixRun n (shift E)

def splitMatrix (w : ℕ → A → ℝ) (edge : ℕ → A → A → ℝ) (n : ℕ) : Matrix A A ℝ :=
  fun i j => w n i * edge n i j * w (n + 1) j

lemma splitMatrix_shift (w : ℕ → A → ℝ) (edge : ℕ → A → A → ℝ) :
    shift (splitMatrix w edge) = splitMatrix (shift w) (shift edge) := rfl

/-- Exact weighted fixed-source normalization into symmetric half weights. -/
lemma run_split_exact (n : ℕ) (w : ℕ → A → ℝ) (edge : ℕ → A → A → ℝ) (first : A) :
    run n (fun k i => (w k i) ^ 2) edge (fun _ => 1) first =
      w 0 first * (matrixRun n (splitMatrix w edge) *ᵥ w n) first := by
  induction n generalizing w edge first with
  | zero => simp [run, matrixRun, pow_two]
  | succ n ih =>
    simp only [run, matrixRun, ← Matrix.mulVec_mulVec, splitMatrix_shift]
    have hw : shift (fun k i => (w k i) ^ 2) = (fun k i => (shift w k i) ^ 2) := rfl
    rw [hw]
    simp_rw [ih]
    simp only [Matrix.mulVec, dotProduct, splitMatrix, shift, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Complete finite path assignments equal their boundary-matrix expression. -/
lemma pathSource_split_exact (n : ℕ) (w : ℕ → A → ℝ) (edge : ℕ → A → A → ℝ) :
    pathSource n (fun k i => (w k i) ^ 2) edge =
      w 0 ⬝ᵥ (matrixRun n (splitMatrix w edge) *ᵥ w n) := by
  rw [← pathRun_eq_source]
  simp only [pathRun, run_split_exact, dotProduct]

/-- Endpoint test kept explicit for the eventual cycle-closing condition. -/
lemma run_split_finish_exact (n : ℕ) (w : ℕ → A → ℝ) (edge : ℕ → A → A → ℝ)
    (finish : A → ℝ) (first : A) :
    run n (fun k i => (w k i) ^ 2) edge finish first =
      w 0 first * (matrixRun n (splitMatrix w edge) *ᵥ (fun last => w n last * finish last)) first := by
  induction n generalizing w edge first with
  | zero => simp [run, matrixRun, pow_two, mul_assoc]
  | succ n ih =>
    simp only [run, matrixRun, ← Matrix.mulVec_mulVec, splitMatrix_shift]
    have hw : shift (fun k i => (w k i) ^ 2) = (fun k i => (shift w k i) ^ 2) := rfl
    rw [hw]
    simp_rw [ih]
    simp only [Matrix.mulVec, dotProduct, splitMatrix, shift, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def closeMatrix (n : ℕ) (w : ℕ → A → ℝ) (close : A → A → ℝ) : Matrix A A ℝ :=
  fun last first => w n last * close last first * w 0 first

/-- Exact cycle normalization. The closing state is the actual first state,
not a second independent endpoint. -/
lemma cycleSource_split_exact (n : ℕ) (w : ℕ → A → ℝ) (edge : ℕ → A → A → ℝ)
    (close : A → A → ℝ) :
    cycleSource n (fun k i => (w k i) ^ 2) edge close =
      (matrixRun n (splitMatrix w edge) * closeMatrix n w close).trace := by
  rw [← cycleRun_eq_source]
  simp only [cycleRun, run_split_finish_exact, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, closeMatrix]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def controls : ℕ → (ℕ → MatrixBounds.Controlled (ι := A)) → List (MatrixBounds.Controlled (ι := A))
  | 0, _ => []
  | n + 1, E => E 0 :: controls n (shift E)

lemma controls_length (n : ℕ) (E : ℕ → MatrixBounds.Controlled (ι := A)) :
    (controls n E).length = n := by
  induction n generalizing E with
  | zero => rfl
  | succ n ih => simp [controls, ih]

lemma matrixRun_controlled (n : ℕ) (E : ℕ → MatrixBounds.Controlled (ι := A)) :
    matrixRun n (fun k => (E k).matrix) = MatrixBounds.chain (controls n E) := by
  induction n generalizing E with
  | zero => rfl
  | succ n ih =>
    change (E 0).matrix * matrixRun n (fun k => (shift E k).matrix) =
      (E 0).matrix * MatrixBounds.chain (controls n (shift E))
    rw [ih]

lemma mul_nonneg (M N : Matrix A A ℝ) (hM : ∀ i j, 0 ≤ M i j) (hN : ∀ i j, 0 ≤ N i j) :
    ∀ i j, 0 ≤ (M * N) i j := by
  intro i j
  exact Finset.sum_nonneg fun k _ => _root_.mul_nonneg (hM i k) (hN k j)

lemma matrixRun_nonneg (n : ℕ) (E : ℕ → Matrix A A ℝ)
    (hE : ∀ k i j, 0 ≤ E k i j) : ∀ i j, 0 ≤ matrixRun n E i j := by
  induction n generalizing E with
  | zero => intro i j; simp only [matrixRun, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih => exact mul_nonneg _ _ (hE 0) (ih (shift E) (fun k => hE (k + 1)))

lemma matrixRun_mono (n : ℕ) (E F : ℕ → Matrix A A ℝ)
    (hE : ∀ k i j, 0 ≤ E k i j) (hle : ∀ k i j, E k i j ≤ F k i j) :
    ∀ i j, matrixRun n E i j ≤ matrixRun n F i j := by
  induction n generalizing E F with
  | zero => intro i j; rfl
  | succ n ih =>
    intro i j
    simp only [matrixRun, Matrix.mul_apply]
    exact Finset.sum_le_sum fun k _ => _root_.mul_le_mul (hle 0 i k)
      (ih (shift E) (shift F) (fun k => hE (k + 1)) (fun k => hle (k + 1)) k j)
      (matrixRun_nonneg n (shift E) (fun k => hE (k + 1)) k j)
      ((hE 0 i k).trans (hle 0 i k))

/-- Alphabet restrictions that decrease nonnegative half weights can be
removed before the matrix path estimate. -/
lemma boundary_matrix_mono (M N : Matrix A A ℝ) (x x' y y' : A → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hMN : ∀ i j, M i j ≤ N i j)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxx : ∀ i, x i ≤ x' i) (hyy : ∀ i, y i ≤ y' i) :
    x ⬝ᵥ (M *ᵥ y) ≤ x' ⬝ᵥ (N *ᵥ y') := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact _root_.mul_le_mul (hxx i)
    (_root_.mul_le_mul (hMN i j) (hyy j) (hy j) ((hM i j).trans (hMN i j)))
    (_root_.mul_nonneg (hM i j) (hy j)) ((hx i).trans (hxx i))

end MatrixSource
end SubmittedGenus.CapFiveMass
