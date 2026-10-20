import Results.Genus.CapFourMass.PositiveGauge
import Results.Genus.CapFourMass.RationalModeAdapter
import Results.Genus.CapFourMass.TaggedModeWeights

/-! The literal rational right/left convention of certify_perron_box.cpp.
All exposed evaluator data use rational operations in radius, lambda and mu;
the square-root gauge occurs only in the proof of equality. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.RationalRuns
open CapFiveMass.MatrixBounds ActualComponent

/-- Signed right vectors used by the submitted rational interval producer. -/
def rightVector (j : Mode) : State→ℝ :=
  if j=0 then ![carryB/lam,1,1,0] else ![lam/radius,-1,-1,0]

def norm (j : Mode) : ℝ := ∑i : State,radius^(i.val+1)*(rightVector j i)^2

def weightedDot (x y : State→ℝ) : ℝ := ∑i,radius^(i.val+1)*x i*y i

def strong : StrongRun→Matrix State State ℝ
  | .full n _ => (rationalTransfer 4 4)^n
  | .restricted => rationalTransfer 4 3

def frame : Option StrongRun→Matrix State State ℝ
  | none => 1
  | some s => strong s

/-- Left-normalized projected strong block followed by its exact carry power. -/
def block (b : CoupledRun) : Matrix Mode Mode ℝ := fun i j =>
  weightedDot (rightVector i) (strong b.strong*ᵥ rightVector j)/norm i * modeRoot j^b.carryLength

/-- The arriving carry mode has no denominator at the initial endpoint. -/
def start (pre : Option StrongRun) (n : ℕ) (x : State→ℝ) (j : Mode) : ℝ :=
  weightedDot x (frame pre*ᵥ rightVector j)*modeRoot j^n

/-- Its weighted norm denominator appears at the outgoing endpoint. -/
def finish (post : Option StrongRun) (y : State→ℝ) (j : Mode) : ℝ :=
  weightedDot (rightVector j) (frame post*ᵥ y)/norm j

def pathAbsolute (pre post : Option StrongRun) (n : ℕ) (l : List CoupledRun)
    (x y : State→ℝ) : ℝ :=
  (fun j => |start pre n x j|) ⬝ᵥ
    ((l.map (fun b => absoluteMatrix (block b))).prod*ᵥ (fun j => |finish post y j|))

def cycleAbsolute (l : List CoupledRun) : ℝ :=
  ((l.map (fun b => absoluteMatrix (block b))).prod).trace

/-- This positive scale is absent from the executable expressions. -/
def scale (j : Mode) : ℝ :=
  if j=0 then Real.sqrt plusNorm/lam else Real.sqrt minusNorm/radius

lemma scale_pos (j : Mode) : 0<scale j := by
  fin_cases j
  · simpa [scale] using div_pos (Real.sqrt_pos.mpr plusNorm_pos) lam_pos
  · simpa [scale] using div_pos (Real.sqrt_pos.mpr minusNorm_pos) radius_pos

lemma right_zero : rightVector 0=fun i => plusVector i/lam := by
  ext i
  fin_cases i <;> simp [rightVector,plusVector,ne_of_gt lam_pos]

lemma right_one : rightVector 1=fun i => minusVector i/radius := by
  ext i
  fin_cases i <;> simp [rightVector,minusVector,carryA,ne_of_gt radius_pos]

/-- The exact denominator written as kv in the original producer. -/
lemma norm_plus_formula : norm 0=radius*(carryB/lam)^2+carryB := by
  norm_num [norm,rightVector,Fin.sum_univ_succ,carryB]

/-- The exact denominator written as kq in the original producer. -/
lemma norm_minus_formula : norm 1=radius*(lam/radius)^2+carryB := by
  norm_num [norm,rightVector,Fin.sum_univ_succ,carryB]

lemma norm_zero : norm 0=plusNorm/lam^2 := by
  rw [norm,right_zero,plusNorm_eq]
  norm_num [plusVector,Fin.sum_univ_succ,carryA,carryB]
  field_simp [ne_of_gt lam_pos]
  <;> ring

lemma norm_one : norm 1=minusNorm/radius^2 := by
  rw [norm,right_one,minusNorm_eq]
  norm_num [minusVector,Fin.sum_univ_succ,carryA,carryB]
  field_simp [ne_of_gt radius_pos]
  <;> ring

lemma scale_sq (j : Mode) : scale j^2=norm j := by
  fin_cases j
  · change scale 0^2=norm 0
    rw [norm_zero]
    simp only [scale,ite_true,div_pow,Real.sq_sqrt plusNorm_pos.le]
  · change scale 1^2=norm 1
    rw [norm_one]
    norm_num only [scale,one_ne_zero,ite_false,div_pow,Real.sq_sqrt minusNorm_pos.le]

lemma norm_pos (j : Mode) : 0<norm j := by rw [←scale_sq]; exact sq_pos_of_pos (scale_pos j)

lemma modeVector_eq (j : Mode) : modeVector j=fun i => halfScale (rightVector j) i/scale j := by
  have hl:=ne_of_gt lam_pos
  have hz:=ne_of_gt radius_pos
  have hp:=ne_of_gt (Real.sqrt_pos.mpr plusNorm_pos)
  have hm:=ne_of_gt (Real.sqrt_pos.mpr minusNorm_pos)
  fin_cases j
  · change modeVector 0=fun i => halfScale (rightVector 0) i/scale 0
    rw [right_zero]
    ext i
    simp only [modeVector,Matrix.cons_val_zero,qplus,plusRaw,halfScale,scale,ite_true]
    field_simp [hl,hp]
    <;> ring
  · change modeVector 1=fun i => halfScale (rightVector 1) i/scale 1
    rw [right_one]
    ext i
    norm_num only [modeVector,Matrix.cons_val_one,Matrix.cons_val_zero,qminus,minusRaw,halfScale,scale,one_ne_zero,ite_false]
    field_simp [hz,hm]
    <;> ring

lemma halfScale_power (n : ℕ) (x : State→ℝ) :
    strongMatrix^n*ᵥ halfScale x=halfScale ((rationalTransfer 4 4)^n*ᵥ x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ',←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,ih]
    exact transfer_halfScale 4 4 _

lemma strong_halfScale (s : StrongRun) (x : State→ℝ) :
    s.matrix*ᵥ halfScale x=halfScale (strong s*ᵥ x) := by
  cases s with
  | full n hn => exact halfScale_power n x
  | restricted => exact transfer_halfScale 4 3 x

lemma frame_halfScale (s : Option StrongRun) (x : State→ℝ) :
    frameMatrix s*ᵥ halfScale x=halfScale (frame s*ᵥ x) := by
  cases s with
  | none => simp [frameMatrix,frame]
  | some s => exact strong_halfScale s x

lemma weightedDot_eq (x y : State→ℝ) : halfScale x ⬝ᵥ halfScale y=weightedDot x y :=
  halfScale_dot x y

lemma block_gauge (b : CoupledRun) :
    b.spectral=PositiveGauge.matrix scale (block b) := by
  ext i j
  rw [CoupledRun.spectral,coupledBlock_entry,modeVector_eq i,modeVector_eq j,
    mulVec_div,dot_div_div,strong_halfScale,weightedDot_eq]
  unfold PositiveGauge.matrix block
  rw [←scale_sq i]
  field_simp [ne_of_gt (scale_pos i),ne_of_gt (scale_pos j)]
  <;> ring

lemma start_gauge (pre : Option StrongRun) (n : ℕ) (x : State→ℝ) (j : Mode) :
    ((frameMatrix pre*ᵥ halfScale x) ⬝ᵥ modeVector j)*modeRoot j^n=start pre n x j/scale j := by
  rw [←frame_left_dot,modeVector_eq,mulVec_div,dot_div_right,frame_halfScale,weightedDot_eq]
  unfold start
  ring

lemma finish_gauge (post : Option StrongRun) (y : State→ℝ) (j : Mode) :
    modeVector j ⬝ᵥ (frameMatrix post*ᵥ halfScale y)=scale j*finish post y j := by
  rw [modeVector_eq,dot_div_left,frame_halfScale,weightedDot_eq]
  unfold finish
  rw [←scale_sq j]
  field_simp [ne_of_gt (scale_pos j)]
  <;> ring

/-- Exact rational two-state path evaluator, including a zero-length leading
carry when its independent source justification allows that corner. -/
theorem framed_absolute_eq (pre post : Option StrongRun) (n : ℕ) (l : List CoupledRun)
    (x y : State→ℝ) :
    framedPathAbsolute pre post n l (halfScale x) (halfScale y)=pathAbsolute pre post n l x y := by
  unfold framedPathAbsolute coupledPathAbsolute pathAbsolute
  have hs : carryBoundary n (frameMatrix pre*ᵥ halfScale x)=fun j => |start pre n x j/scale j| := by
    ext j
    unfold carryBoundary
    rw [dotProduct_comm,mul_comm,start_gauge]
  have hf : modeBoundary (frameMatrix post*ᵥ halfScale y)=fun j => |scale j*finish post y j| := by
    ext j
    unfold modeBoundary
    rw [finish_gauge]
  rw [hs,hf]
  simp_rw [CoupledRun.dominated_matrix,block_gauge]
  have hm : l.map (fun b => absoluteMatrix (PositiveGauge.matrix scale (block b)))=
      (l.map block).map (fun A => absoluteMatrix (PositiveGauge.matrix scale A)) := by
    simp only [List.map_map,Function.comp_def]
  rw [hm]
  simpa only [List.map_map,Function.comp_def] using
    PositiveGauge.path_absolute scale scale_pos (l.map block) (start pre n x) (finish post y)

/-- Exact rational cycle trace with entrywise absolute projected blocks. -/
theorem cycle_absolute_eq (l : List CoupledRun) : coupledCycleAbsolute l=cycleAbsolute l := by
  unfold coupledCycleAbsolute cycleAbsolute
  simp_rw [CoupledRun.dominated_matrix,block_gauge]
  have hm : l.map (fun b => absoluteMatrix (PositiveGauge.matrix scale (block b)))=
      (l.map block).map (fun A => absoluteMatrix (PositiveGauge.matrix scale A)) := by
    simp only [List.map_map,Function.comp_def]
  rw [hm]
  simpa only [List.map_map,Function.comp_def] using
    PositiveGauge.cycle_absolute scale scale_pos (l.map block)

end SubmittedGenus.CapFourMass.RationalRuns
