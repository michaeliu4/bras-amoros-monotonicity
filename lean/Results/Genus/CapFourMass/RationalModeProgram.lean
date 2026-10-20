import Results.Genus.CapFourMass.RationalTaggedModes
import Results.Genus.CapFourMass.ExecutableModeProgram

/-! Exact rational input syntax for every supplied executable mode program.
The definitions are finite matrix arithmetic in radius and the two roots;
normalization square roots are eliminated by the proved positive gauge. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.SourceModel ActualComponent FixedPivot

/-- Purely finite endpoint indicator; no half weights enter the expression. -/
def FreeLayout.mask {m r p : ℕ} (L : FreeLayout m r p) (c : Fin L.count)
    (i : Fin (L.edges c+1)) (v : State) : ℝ :=
  if Domain r p 4 (L.vertex c i) (v.val+1) then 1 else 0

lemma FreeLayout.half_eq_mask {m r p : ℕ} (L : FreeLayout m r p) (c : Fin L.count)
    (i : Fin (L.edges c+1)) : L.half c i=halfScale (L.mask c i) := by
  ext v
  by_cases h : Domain r p 4 (L.vertex c i) (v.val+1)
  · simp [FreeLayout.half,FreeLayout.mask,halfScale,h]
  · simp [FreeLayout.half,FreeLayout.mask,halfScale,h]

def ModeProgram.rationalPure {B : Type*} (x y : State→ℝ) : ModeProgram B→ℝ
  | .path q => RationalRuns.pathPure q x y
  | .cycle _ b bs => RationalRuns.cyclePure (b::bs)
  | .isolated => RationalRuns.isolatedPure

def ModeProgram.rationalAbsolute {B : Type*} (x y : State→ℝ) : ModeProgram B→ℝ
  | .path q => RationalRuns.pathAbs q x y
  | .cycle _ b bs => RationalRuns.cycleAbsolute ((b::bs).map TaggedBlock.run)
  | .isolated => RationalRuns.isolatedAbsolute

lemma ModeProgram.pure_eq_rational {B : Type*} (q : ModeProgram B) (x y : State→ℝ) :
    q.pureValue (halfScale x) (halfScale y)=q.rationalPure x y := by
  cases q with
  | path q => exact RationalRuns.path_pure_eq q x y
  | cycle rotation b bs => exact RationalRuns.cycle_pure_eq b bs
  | isolated => exact RationalRuns.isolated_pure_eq

lemma ModeProgram.absolute_eq_rational {B : Type*} (q : ModeProgram B) (x y : State→ℝ) :
    q.absoluteValue (halfScale x) (halfScale y)=q.rationalAbsolute x y := by
  cases q with
  | path q => exact RationalRuns.path_absolute_eq q x y
  | cycle rotation b bs => exact RationalRuns.cycle_absolute_eq _
  | isolated => exact RationalRuns.isolated_absolute_eq

def rationalProgramPure {r N d : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
    (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN))) : ℝ :=
  radius^8*∏c,(program c).rationalPure (L.mask c 0) (L.mask c (Fin.last _))

def rationalProgramAbsolute {r N d : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
    (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN))) : ℝ :=
  radius^8*∏c,(program c).rationalAbsolute (L.mask c 0) (L.mask c (Fin.last _))

def rationalProgramMixed {r N d : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
    (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN))) : ℝ :=
  rationalProgramAbsolute L program-rationalProgramPure L program

lemma programPure_eq_rational {r N d : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
    (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN))) :
    programPure L program=rationalProgramPure L program := by
  unfold programPure rationalProgramPure
  congr 1
  apply Finset.prod_congr rfl
  intro c _
  rw [FreeLayout.half_eq_mask,FreeLayout.half_eq_mask,ModeProgram.pure_eq_rational]

lemma programAbsolute_eq_rational {r N d : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
    (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN))) :
    programAbsolute L program=rationalProgramAbsolute L program := by
  unfold programAbsolute rationalProgramAbsolute
  congr 1
  apply Finset.prod_congr rfl
  intro c _
  rw [FreeLayout.half_eq_mask,FreeLayout.half_eq_mask,ModeProgram.absolute_eq_rational]

lemma programMixed_eq_rational {r N d : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
    (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN))) :
    programMixed L program=rationalProgramMixed L program := by
  rw [programMixed,rationalProgramMixed,programAbsolute_eq_rational,programPure_eq_rational]

end SubmittedGenus.CapFourMass.ExecutableModes
