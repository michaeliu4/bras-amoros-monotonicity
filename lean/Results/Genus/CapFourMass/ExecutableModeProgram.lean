import Results.Genus.CapFourMass.ExecutableModeLayoutCheck
import Results.Genus.CapFourMass.ExecutableModeLayoutTags
import Results.Genus.CapFourMass.ExecutableRunCheck
import Results.Genus.CapFourMass.ModeRunEnvelope
import Results.Genus.CapFourMass.TaggedModeEvaluation

/-! Finite source programs supplied to the original interval evaluator. The
program retains canonical carry labels until the sound shared-slot injection;
only its independent absolute majorant erases those labels. -/
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.SourceModel FixedPivot ActualComponent

inductive ModeProgram (B : Type*)
  | path (code : TaggedPathCode B)
  | cycle (rotation : ℕ) (first : TaggedBlock B) (rest : List (TaggedBlock B))
  | isolated

section Check
variable {r N d : ℕ} (hd : 0<d) (hN : d<N)
variable (L : FreeLayout (r+N) r (r+d)) (c : Fin L.count)

/-- Each branch checks all additional facts needed by signed evaluation.
A zero-edge high vertex is the separate two-mode loop, never a pure path. -/
def ModeProgram.check : ModeProgram (Option (CarryRepresentative N d hN))→Bool
  | .path code => decide (L.cycle c=false ∧ (L.edges c≠0 ∨ physical (L.vertex c 0)≤r)) &&
      pathCodeCheck (L.pathTags hd hN c) code
  | .cycle rotation first rest => decide (L.cycle c=true) &&
      cycleCodeCheck (L.cycleTags hd hN c) rotation (first::rest)
  | .isolated => decide (L.cycle c=false ∧ L.edges c=0 ∧ r<physical (L.vertex c 0))

@[simp] lemma ModeProgram.check_path (code : TaggedPathCode (Option (CarryRepresentative N d hN))) :
    (ModeProgram.path code).check hd hN L c=true ↔
      L.cycle c=false ∧ (L.edges c≠0 ∨ physical (L.vertex c 0)≤r) ∧
      pathCodeCheck (L.pathTags hd hN c) code=true := by
  simp only [ModeProgram.check,Bool.and_eq_true,decide_eq_true_eq,and_assoc]

@[simp] lemma ModeProgram.check_cycle (rotation : ℕ)
    (first : TaggedBlock (Option (CarryRepresentative N d hN))) (rest : List (TaggedBlock (Option (CarryRepresentative N d hN)))) :
    (ModeProgram.cycle rotation first rest).check hd hN L c=true ↔
      L.cycle c=true ∧ cycleCodeCheck (L.cycleTags hd hN c) rotation (first::rest)=true := by
  simp only [ModeProgram.check,Bool.and_eq_true,decide_eq_true_eq]

@[simp] lemma ModeProgram.check_isolated :
    (ModeProgram.isolated (B:=Option (CarryRepresentative N d hN))).check hd hN L c=true ↔
      L.cycle c=false ∧ L.edges c=0 ∧ r<physical (L.vertex c 0) := by
  simp only [ModeProgram.check,decide_eq_true_eq]

end Check

noncomputable section
open scoped Matrix BigOperators

/-- Actual physical endpoint mask. This is represented by a finite mask in the
interval syntax, with the unchanged source radius and half weights. -/
def FreeLayout.half {m r p : ℕ} (L : FreeLayout m r p) (c : Fin L.count)
    (i : Fin (L.edges c+1)) (v : State) : ℝ :=
  if Domain r p 4 (L.vertex c i) (v.val+1) then halfWeight v else 0

def ModeProgram.pureValue {B : Type*} (x y : State→ℝ) : ModeProgram B→ℝ
  | .path code => x ⬝ᵥ (code.matrixWith (labelledModeMatrix (fun _ : B => 0))*ᵥ y)
  | .cycle _ first rest =>
      (((first::rest).map (TaggedBlock.matrixWith (labelledModeMatrix (fun _ : B => 0)))).prod).trace
  | .isolated => (freeBoundary ⬝ᵥ modeVector 0)*(loopBoundary ⬝ᵥ modeVector 0)

def ModeProgram.absoluteValue {B : Type*} (x y : State→ℝ) : ModeProgram B→ℝ
  | .path code => code.erase.absolute x y
  | .cycle _ first rest => coupledCycleAbsolute ((first::rest).map TaggedBlock.run)
  | .isolated => carryAbsolute 0 freeBoundary loopBoundary

/-- Executable finite indices and program data determine the two scalar
expressions to be enclosed; no choice-based component ordering is evaluated. -/
def programPure {r N d : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
    (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN))) : ℝ :=
  radius^8*∏c, (program c).pureValue (L.half c 0) (L.half c (Fin.last _))

def programAbsolute {r N d : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
    (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN))) : ℝ :=
  radius^8*∏c, (program c).absoluteValue (L.half c 0) (L.half c (Fin.last _))

def programMixed {r N d : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
    (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN))) : ℝ :=
  programAbsolute L program-programPure L program

end
end SubmittedGenus.CapFourMass.ExecutableModes
