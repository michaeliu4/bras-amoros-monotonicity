import Results.Genus.CapFourMass.EndpointBounds
import Results.Genus.CapFiveMass.MatrixSource

/-!
# Exact finite spectral-mode source sums

Absolute path/cycle matrix products are proved equal to sums of absolute
assignment weights. The mixed remainder contains every assignment other than
the all-positive one, including the all-negative assignment.
-/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open RawGraph.Transfer CapFiveMass.MatrixSource

/-- Complete signed mode assignment for an open path. -/
def modePathWeight (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ)
    (ω : Fin (n+1) → Mode) : ℝ :=
  x (ω 0)*sourceTerm n (fun _ _ => 1) A y ω

def modePathMass (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ) : ℝ :=
  ∑ ω : Fin (n+1) → Mode, modePathWeight n A x y ω

def modePathAbsolute (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ) : ℝ :=
  ∑ ω : Fin (n+1) → Mode, |modePathWeight n A x y ω|

def modePathPure (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ) : ℝ :=
  modePathWeight n A x y (fun _ => 0)

def modePathMixed (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ) : ℝ :=
  modePathAbsolute n A x y-modePathPure n A x y

lemma unit_run_eq_matrix (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (y : Mode → ℝ) (first : Mode) :
    run n (fun _ _ => 1) A y first = (matrixRun n A *ᵥ y) first := by
  induction n generalizing A first with
  | zero => simp [run,matrixRun]
  | succ n ih =>
    simp only [run,one_mul,matrixRun,← Matrix.mulVec_mulVec]
    change (∑ next, A 0 first next*run n (fun _ _ => 1) (shift A) y next) = _
    simp_rw [ih]
    rfl

/-- Actual signed finite mode assignments equal their matrix product. -/
theorem modePathMass_eq_matrix (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ) :
    modePathMass n A x y = x ⬝ᵥ (matrixRun n A *ᵥ y) := by
  unfold modePathMass
  rw [sum_cons]
  simp only [modePathWeight,Fin.cons_zero,← Finset.mul_sum]
  change (∑ first, x first*fixedSource n (fun _ _ => 1) A y first) = _
  simp_rw [← run_eq_fixedSource,unit_run_eq_matrix]
  rfl

lemma abs_modePathWeight (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ)
    (ω : Fin (n+1) → Mode) :
    |modePathWeight n A x y ω| =
      modePathWeight n (fun k => absoluteMatrix (A k)) (fun i => |x i|) (fun i => |y i|) ω := by
  simp [modePathWeight,sourceTerm,absoluteMatrix,abs_mul,Finset.abs_prod]

/-- Taking entrywise absolutes before multiplying is exactly the absolute
mode sum, and is not the absolute value of the signed matrix product. -/
theorem modePathAbsolute_eq_matrix (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ) :
    modePathAbsolute n A x y =
      (fun i => |x i|) ⬝ᵥ (matrixRun n (fun k => absoluteMatrix (A k)) *ᵥ (fun i => |y i|)) := by
  unfold modePathAbsolute
  simp_rw [abs_modePathWeight]
  exact modePathMass_eq_matrix n _ _ _

lemma modePathPure_nonneg (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ)
    (hx : 0 ≤ x 0) (hy : 0 ≤ y 0) (hA : ∀ k, 0 ≤ A k 0 0) : 0 ≤ modePathPure n A x y := by
  unfold modePathPure modePathWeight sourceTerm
  simp only [Finset.prod_const_one,one_mul]
  exact mul_nonneg hx (mul_nonneg (Finset.prod_nonneg fun k _ => hA k.val) hy)

lemma modePathPure_le_absolute (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ) :
    modePathPure n A x y ≤ modePathAbsolute n A x y := by
  exact (le_abs_self _).trans (Finset.single_le_sum (fun ω _ => abs_nonneg (modePathWeight n A x y ω))
    (Finset.mem_univ (fun _ : Fin (n+1) => (0 : Mode))))

lemma modePathMixed_nonneg (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ) :
    0 ≤ modePathMixed n A x y := sub_nonneg.mpr (modePathPure_le_absolute n A x y)

/-- Nonnegative spectral majorization uses P+M=Aabs; it never asserts P≤Z. -/
theorem modePath_spectral_majorization (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ) :
    modePathMass n A x y ≤ modePathPure n A x y+modePathMixed n A x y := by
  have h : modePathMass n A x y ≤ modePathAbsolute n A x y :=
    Finset.sum_le_sum fun ω _ => le_abs_self _
  unfold modePathMixed
  linarith

/-- The mixed remainder is literally the sum of all assignments except the
all-positive assignment when that assignment has nonnegative weight. -/
theorem modePathMixed_eq_others (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (x y : Mode → ℝ)
    (hp : 0 ≤ modePathPure n A x y) :
    modePathMixed n A x y =
      ∑ ω ∈ (Finset.univ.erase (fun _ : Fin (n+1) => (0 : Mode))), |modePathWeight n A x y ω| := by
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin (n+1) → Mode)))
    (f := fun ω => |modePathWeight n A x y ω|)
    (Finset.mem_univ (fun _ : Fin (n+1) => (0 : Mode)))
  change _+|modePathPure n A x y|=modePathAbsolute n A x y at h
  rw [abs_of_nonneg hp] at h
  unfold modePathMixed
  linarith

lemma cycle_modes_eq_trace (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (close : Matrix Mode Mode ℝ) :
    cycleSource n (fun _ _ => 1) A close = (matrixRun n A*close).trace := by
  rw [← cycleRun_eq_source]
  unfold cycleRun
  simp_rw [unit_run_eq_matrix]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct]

/-- Every cycle assignment uses the actual closing state; taking absolutes
termwise gives the trace of the entrywise-absolute mode product. -/
theorem cycle_absolute_eq_trace (n : ℕ) (A : ℕ → Matrix Mode Mode ℝ) (close : Matrix Mode Mode ℝ) :
    (∑ ω : Fin (n+1) → Mode,
      |sourceTerm n (fun _ _ => 1) A (fun last => close last (ω 0)) ω|) =
      (matrixRun n (fun k => absoluteMatrix (A k))*absoluteMatrix close).trace := by
  have he (ω : Fin (n+1) → Mode) :
      |sourceTerm n (fun _ _ => 1) A (fun last => close last (ω 0)) ω| =
      sourceTerm n (fun _ _ => 1) (fun k => absoluteMatrix (A k))
        (fun last => absoluteMatrix close last (ω 0)) ω := by
    simp [sourceTerm,absoluteMatrix,abs_mul,Finset.abs_prod]
  simp_rw [he]
  exact cycle_modes_eq_trace n _ _

end SubmittedGenus.CapFourMass
