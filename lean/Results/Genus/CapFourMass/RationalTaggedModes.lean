import Results.Genus.CapFourMass.RationalRunGauge

/-! Rational expressions for the exact all-plus term and the independent
absolute complete-mode evaluator of each supplied tagged path/cycle program. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.RationalRuns
open ActualComponent

variable {B : Type*}

def pathPure (q : TaggedPathCode B) (x y : State→ℝ) : ℝ :=
  match q with
  | .pure s => weightedDot x (frame s*ᵥ y)
  | .carried pre _ n _ bs post =>
      start pre n x 0*(bs.map (fun b => block b.run 0 0)).prod*finish post y 0

def pathAbs (q : TaggedPathCode B) (x y : State→ℝ) : ℝ :=
  match q with
  | .pure s => |weightedDot x (frame s*ᵥ y)|
  | .carried pre _ n _ bs post => pathAbsolute pre post n (bs.map TaggedBlock.run) x y

def cyclePure (bs : List (TaggedBlock B)) : ℝ :=
  (bs.map (fun b => block b.run 0 0)).prod

lemma block_zero (b : CoupledRun) : b.spectral 0 0=block b 0 0 := by
  rw [block_gauge]
  simp [PositiveGauge.matrix,ne_of_gt (scale_pos 0)]

lemma allPlus_chain (bs : List (TaggedBlock B)) (finish : Mode→ℝ) :
    taggedModeChain (fun _ : B => 0) bs 0 finish=
      (bs.map (fun b => block b.run 0 0)).prod*finish 0 := by
  induction bs with
  | nil => simp [taggedModeChain]
  | cons b bs ih =>
    simp only [taggedModeChain,block_zero,ih,List.map_cons,List.prod_cons]
    ring

/-- Exact all-positive source program, with no square-root inputs. -/
theorem path_pure_eq (q : TaggedPathCode B) (x y : State→ℝ) :
    halfScale x ⬝ᵥ ((q.matrixWith (labelledModeMatrix (fun _ : B => 0)))*ᵥ halfScale y)=
      pathPure q x y := by
  rw [tagged_path_evaluation]
  cases q with
  | pure s =>
    simp only [TaggedPathCode.modeTerm,pathPure,frame_halfScale,weightedDot_eq]
  | carried pre tag n hn bs post =>
    simp only [TaggedPathCode.modeTerm,pathPure,allPlus_chain,start_gauge,finish_gauge]
    field_simp [ne_of_gt (scale_pos 0)]
    <;> ring

/-- The same rational block convention computes the exact independent-slot
absolute evaluator, not merely the absolute value of a signed contraction. -/
theorem path_absolute_eq (q : TaggedPathCode B) (x y : State→ℝ) :
    q.erase.absolute (halfScale x) (halfScale y)=pathAbs q x y := by
  cases q with
  | pure s =>
    simp only [TaggedPathCode.erase,PathCode.absolute,pathAbs,optionalStrongMatrix_eq_frame,
      frame_halfScale,weightedDot_eq]
  | carried pre tag n hn bs post =>
    exact framed_absolute_eq pre post n (bs.map TaggedBlock.run) x y

/-- A cycle's distinguished contribution closes at the same positive mode. -/
theorem cycle_pure_eq (b : TaggedBlock B) (bs : List (TaggedBlock B)) :
    (((b::bs).map (TaggedBlock.matrixWith (labelledModeMatrix (fun _ : B => 0)))).prod).trace=
      cyclePure (b::bs) := by
  simp only [List.map_cons,List.prod_cons]
  rw [tagged_cycle_evaluation,allPlus_chain,block_zero]
  simp only [cyclePure,List.map_cons,List.prod_cons]
  ring

def isolatedPure : ℝ := start none 0 ![1,1,1,0] 0*finish none ![0,1,1,0] 0

def isolatedAbsolute : ℝ := pathAbsolute none none 0 [] ![1,1,1,0] ![0,1,1,0]

lemma isolated_pure_eq :
    (freeBoundary ⬝ᵥ modeVector 0)*(loopBoundary ⬝ᵥ modeVector 0)=isolatedPure := by
  have hs:=start_gauge none 0 ![1,1,1,0] 0
  have hf:=finish_gauge none ![0,1,1,0] 0
  simp only [frameMatrix,Matrix.one_mulVec,pow_zero,mul_one] at hs hf
  rw [freeBoundary,loopBoundary,dotProduct_comm (halfScale ![0,1,1,0]),hs,hf]
  unfold isolatedPure
  field_simp [ne_of_gt (scale_pos 0)]
  <;> ring

lemma isolated_absolute_eq : carryAbsolute 0 freeBoundary loopBoundary=isolatedAbsolute := by
  have hh:=framed_absolute_eq none none 0 [] ![1,1,1,0] ![0,1,1,0]
  simpa only [framedPathAbsolute,frameMatrix,Matrix.one_mulVec,coupledPathAbsolute_nil,
    freeBoundary,loopBoundary,isolatedAbsolute] using hh

end SubmittedGenus.CapFourMass.RationalRuns
