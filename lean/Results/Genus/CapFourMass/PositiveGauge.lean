import Results.Genus.CapFourMass.ModePartitions

/-! Positive diagonal changes of mode coordinates preserve complete scalar
contractions, including the entrywise-absolute path/cycle evaluators. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.PositiveGauge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrix (s : ι→ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => s i*A i j/s j

lemma one (s : ι→ℝ) (hs : ∀i,s i≠0) : matrix s 1=1 := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [matrix,hs]
  · simp [matrix,Matrix.one_apply,h]

lemma mul (s : ι→ℝ) (hs : ∀i,s i≠0) (A B : Matrix ι ι ℝ) :
    matrix s A*matrix s B=matrix s (A*B) := by
  ext i j
  simp only [matrix,Matrix.mul_apply,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  field_simp [hs k,hs j]
  <;> ring

lemma prod (s : ι→ℝ) (hs : ∀i,s i≠0) (l : List (Matrix ι ι ℝ)) :
    (l.map (matrix s)).prod=matrix s l.prod := by
  induction l with
  | nil => simpa using (one s hs).symm
  | cons A l ih => simp only [List.map_cons,List.prod_cons,ih,mul s hs]

lemma trace (s : ι→ℝ) (hs : ∀i,s i≠0) (A : Matrix ι ι ℝ) :
    (matrix s A).trace=A.trace := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  simp [matrix,hs]

lemma path (s : ι→ℝ) (hs : ∀i,s i≠0)
    (A : Matrix ι ι ℝ) (x y : ι→ℝ) :
    (fun i => x i/s i) ⬝ᵥ ((matrix s A)*ᵥ (fun i => s i*y i))=
      x ⬝ᵥ (A*ᵥ y) := by
  simp only [Matrix.mulVec,dotProduct,matrix,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hs i,hs j]
  <;> ring

lemma absolute (s : Mode→ℝ) (hs : ∀i,0<s i) (A : Matrix Mode Mode ℝ) :
    absoluteMatrix (matrix s A)=matrix s (absoluteMatrix A) := by
  ext i j
  simp only [absoluteMatrix,matrix,abs_div,abs_mul,abs_of_pos (hs i),abs_of_pos (hs j)]

/-- All internal scale factors cancel before a path is evaluated. -/
lemma path_prod (s : ι→ℝ) (hs : ∀i,s i≠0)
    (l : List (Matrix ι ι ℝ)) (x y : ι→ℝ) :
    (fun i => x i/s i) ⬝ᵥ ((l.map (matrix s)).prod*ᵥ (fun i => s i*y i))=
      x ⬝ᵥ (l.prod*ᵥ y) := by
  rw [prod s hs,path s hs]

/-- The same cancellation holds after entrywise absolute values. Positivity
of the gauge is explicit; no signed cancellation is used. -/
lemma path_absolute (s : Mode→ℝ) (hs : ∀i,0<s i)
    (l : List (Matrix Mode Mode ℝ)) (x y : Mode→ℝ) :
    (fun i => |x i/s i|) ⬝ᵥ
      ((l.map (fun A => absoluteMatrix (matrix s A))).prod*ᵥ (fun i => |s i*y i|))=
      (fun i => |x i|) ⬝ᵥ ((l.map absoluteMatrix).prod*ᵥ (fun i => |y i|)) := by
  have hsabs : ∀i,|s i|=s i := fun i => abs_of_pos (hs i)
  simp only [abs_div,abs_mul,hsabs,absolute s hs]
  rw [show l.map (fun A => matrix s (absoluteMatrix A))=
      (l.map absoluteMatrix).map (matrix s) by simp only [List.map_map,Function.comp_def]]
  exact path_prod s (fun i => ne_of_gt (hs i)) _ _ _

lemma cycle_prod (s : ι→ℝ) (hs : ∀i,s i≠0) (l : List (Matrix ι ι ℝ)) :
    ((l.map (matrix s)).prod).trace=l.prod.trace := by
  rw [prod s hs,trace s hs]

lemma cycle_absolute (s : Mode→ℝ) (hs : ∀i,0<s i) (l : List (Matrix Mode Mode ℝ)) :
    ((l.map (fun A => absoluteMatrix (matrix s A))).prod).trace=
      ((l.map absoluteMatrix).prod).trace := by
  simp only [absolute s hs]
  rw [show l.map (fun A => matrix s (absoluteMatrix A))=
      (l.map absoluteMatrix).map (matrix s) by simp only [List.map_map,Function.comp_def]]
  exact cycle_prod s (fun i => ne_of_gt (hs i)) _

end SubmittedGenus.CapFourMass.PositiveGauge
