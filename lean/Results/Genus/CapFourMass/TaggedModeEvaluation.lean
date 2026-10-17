import Results.Genus.CapFourMass.TaggedMatrices
import Results.Genus.CapFourMass.RankOneModes
import Results.Genus.CapFourMass.ModeRunEnvelope

/-! Exact fixed-choice evaluation of tagged carry runs. Every occurrence of a
label uses the same mode choice; no independence of repeated labels is assumed. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open RawGraph.Transfer CapFiveMass.MatrixSource

lemma modeProjector_mulVec (j : Mode) (y : State→ℝ) :
    modeProjector j*ᵥ y=fun a => (modeVector j ⬝ᵥ y)*modeVector j a := by
  funext a
  simp only [modeProjector,Matrix.mulVec,dotProduct,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma mode_projector_trace (A : Matrix State State ℝ) (j : Mode) :
    (A*modeProjector j).trace=modeVector j ⬝ᵥ (A*ᵥ modeVector j) := by
  change (A*Matrix.vecMulVec (modeVector j) (modeVector j)).trace=_
  rw [Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm]

lemma scaled_mode_trace (A : Matrix State State ℝ) (a : ℝ) (j : Mode) :
    (A*(a • modeProjector j)).trace=a*(modeVector j ⬝ᵥ (A*ᵥ modeVector j)) := by
  rw [Matrix.mul_smul,Matrix.trace_smul,mode_projector_trace]
  rfl

lemma mode_power_path (j : Mode) (n : ℕ) (hn : 1≤n) (x y : State→ℝ) :
    x ⬝ᵥ (((modeRoot j • modeProjector j)^n)*ᵥ y)=
      (x ⬝ᵥ modeVector j)*modeRoot j^n*(modeVector j ⬝ᵥ y) := by
  rw [carry_mode_power j n hn,Matrix.smul_mulVec,modeProjector_mulVec]
  change x ⬝ᵥ (fun a => modeRoot j^n*((modeVector j ⬝ᵥ y)*modeVector j a))=_
  have he : (fun a => modeRoot j^n*((modeVector j ⬝ᵥ y)*modeVector j a))=
      fun a => (modeRoot j^n*(modeVector j ⬝ᵥ y))*modeVector j a := by funext a; ring
  rw [he,dot_scale_right]
  ring

namespace ActualComponent
variable {B : Type*}

def labelledModeMatrix (choice : B→Mode) (b : B) : Matrix State State ℝ :=
  modeRoot (choice b) • modeProjector (choice b)

lemma tagged_block_left (choice : B→Mode) (b : TaggedBlock B) (j : Mode) (y : State→ℝ) :
    modeVector j ⬝ᵥ ((b.matrixWith (labelledModeMatrix choice))*ᵥ y)=
      b.run.spectral j (choice b.label)*(modeVector (choice b.label) ⬝ᵥ y) := by
  unfold TaggedBlock.matrixWith labelledModeMatrix
  rw [carry_mode_power _ _ b.run.carryPositive,← Matrix.mulVec_mulVec,
    Matrix.smul_mulVec,modeProjector_mulVec]
  have he : (modeRoot (choice b.label)^b.run.carryLength •
      (fun a => (modeVector (choice b.label) ⬝ᵥ y)*modeVector (choice b.label) a))=
      fun a => (modeRoot (choice b.label)^b.run.carryLength*(modeVector (choice b.label) ⬝ᵥ y))*
        modeVector (choice b.label) a := by ext a; simp [mul_assoc]
  rw [he,matrix_mulVec_scale,dot_scale_right]
  rw [CoupledRun.spectral,coupledBlock_entry]
  ring

def taggedModeChain (choice : B→Mode) : List (TaggedBlock B)→Mode→(Mode→ℝ)→ℝ
  | [],j,finish => finish j
  | b::bs,j,finish => b.run.spectral j (choice b.label)*taggedModeChain choice bs (choice b.label) finish

lemma taggedModeChain_scale (choice : B→Mode) (bs : List (TaggedBlock B)) (j : Mode)
    (finish : Mode→ℝ) (a : ℝ) :
    taggedModeChain choice bs j (fun k => a*finish k)=a*taggedModeChain choice bs j finish := by
  induction bs generalizing j with
  | nil => rfl
  | cons b bs ih => simp only [taggedModeChain,ih]; ring

lemma tagged_tail_evaluation (choice : B→Mode) (bs : List (TaggedBlock B)) (j : Mode) (y : State→ℝ) :
    modeVector j ⬝ᵥ ((bs.map (TaggedBlock.matrixWith (labelledModeMatrix choice))).prod*ᵥ y)=
      taggedModeChain choice bs j (fun k => modeVector k ⬝ᵥ y) := by
  induction bs generalizing j with
  | nil => simp [taggedModeChain]
  | cons b bs ih =>
    simp only [List.map_cons,List.prod_cons,← Matrix.mulVec_mulVec,taggedModeChain]
    rw [tagged_block_left,ih]

lemma frame_left_dot (pre : Option StrongRun) (x y : State→ℝ) :
    x ⬝ᵥ (frameMatrix pre*ᵥ y)=(frameMatrix pre*ᵥ x) ⬝ᵥ y := by
  have h:=Matrix.dotProduct_transpose_mulVec (frameMatrix pre) x y
  rw [frameMatrix_symmetric] at h
  exact h.trans (dotProduct_comm _ _)

def TaggedPathCode.modeTerm (choice : B→Mode) : TaggedPathCode B→(State→ℝ)→(State→ℝ)→ℝ
  | .pure s,x,y => x ⬝ᵥ (frameMatrix s*ᵥ y)
  | .carried pre tag n _ bs post,x,y =>
      ((frameMatrix pre*ᵥ x) ⬝ᵥ modeVector (choice tag))*modeRoot (choice tag)^n*
        taggedModeChain choice bs (choice tag) (fun j => modeVector j ⬝ᵥ (frameMatrix post*ᵥ y))

/-- Exact optional-frame path scalar for a single complete shared-label choice. -/
theorem tagged_path_evaluation (choice : B→Mode) (q : TaggedPathCode B) (x y : State→ℝ) :
    x ⬝ᵥ ((q.matrixWith (labelledModeMatrix choice))*ᵥ y)=q.modeTerm choice x y := by
  cases q with
  | pure s => simp only [TaggedPathCode.matrixWith,TaggedPathCode.modeTerm,optionalStrongMatrix_eq_frame]
  | carried pre tag n hn bs post =>
    simp only [TaggedPathCode.matrixWith,TaggedPathCode.modeTerm,optionalStrongMatrix_eq_frame,
      ← Matrix.mulVec_mulVec]
    rw [frame_left_dot]
    change (frameMatrix pre*ᵥ x) ⬝ᵥ
      (((modeRoot (choice tag) • modeProjector (choice tag))^n)*ᵥ
        ((bs.map (TaggedBlock.matrixWith (labelledModeMatrix choice))).prod*ᵥ (frameMatrix post*ᵥ y)))=_
    rw [mode_power_path _ _ hn,tagged_tail_evaluation choice bs]

/-- Exact cycle scalar, closed against the same initial tagged mode. -/
theorem tagged_cycle_evaluation (choice : B→Mode) (b : TaggedBlock B) (bs : List (TaggedBlock B)) :
    ((b.matrixWith (labelledModeMatrix choice))*(bs.map (TaggedBlock.matrixWith (labelledModeMatrix choice))).prod).trace=
      taggedModeChain choice bs (choice b.label) (fun j => b.run.spectral j (choice b.label)) := by
  change (b.run.strong.matrix*(labelledModeMatrix choice b.label)^b.run.carryLength*
    (bs.map (TaggedBlock.matrixWith (labelledModeMatrix choice))).prod).trace=_
  rw [Matrix.trace_mul_cycle]
  change (((bs.map (TaggedBlock.matrixWith (labelledModeMatrix choice))).prod*b.run.strong.matrix)*
    (modeRoot (choice b.label) • modeProjector (choice b.label))^b.run.carryLength).trace=_
  rw [carry_mode_power _ _ b.run.carryPositive,scaled_mode_trace,← Matrix.mulVec_mulVec,
    tagged_tail_evaluation choice bs]
  have he : (fun j => b.run.spectral j (choice b.label))=
      fun j => modeRoot (choice b.label)^b.run.carryLength*
        (modeVector j ⬝ᵥ (b.run.strong.matrix*ᵥ modeVector (choice b.label))) := by
    funext j
    rw [CoupledRun.spectral,coupledBlock_entry]
    ring
  rw [he,taggedModeChain_scale]

end ActualComponent
end SubmittedGenus.CapFourMass
