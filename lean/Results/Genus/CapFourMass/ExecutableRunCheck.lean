import Results.Genus.CapFourMass.TaggedMatrices

/-! Executable checking of supplied labelled run programs. Neither the typed
normal form nor the agreement of repeated carry labels is assumed from an
external producer. -/
namespace SubmittedGenus.CapFourMass.ExecutableModes
open ActualComponent

deriving instance DecidableEq for StrongRun
deriving instance DecidableEq for CoupledRun
deriving instance DecidableEq for TaggedEdge
deriving instance DecidableEq for TaggedAtom
deriving instance DecidableEq for TaggedBlock
deriving instance DecidableEq for TaggedPathCode

instance {B : Type*} [DecidableEq B] (a b : TaggedEdge B) : Decidable (TaggedCompatible a b) := by
  unfold TaggedCompatible CompatibleKinds
  infer_instance

/-- Supplied path program validation, including the complete shared label word. -/
def pathCodeCheck {B : Type*} [DecidableEq B] [Inhabited B]
    (word : List (TaggedEdge B)) (code : TaggedPathCode B) : Bool :=
  decide (word.IsChain TaggedCompatible ∧ taggedAtoms word=code.atoms)

@[simp] theorem pathCodeCheck_eq_true {B : Type*} [DecidableEq B] [Inhabited B]
    (word : List (TaggedEdge B)) (code : TaggedPathCode B) :
    pathCodeCheck word code=true ↔ word.IsChain TaggedCompatible ∧ taggedAtoms word=code.atoms := by
  simp [pathCodeCheck]

/-- Cyclic programs may rotate the literal source word. Rotation preserves
trace, and the checked nonempty block list preserves the closing carry slot. -/
def cycleCodeCheck {B : Type*} [DecidableEq B] [Inhabited B]
    (word : List (TaggedEdge B)) (rotation : ℕ) (blocks : List (TaggedBlock B)) : Bool :=
  decide (blocks≠[] ∧ (word.rotate rotation).IsChain TaggedCompatible ∧
    taggedAtoms (word.rotate rotation)=blocks.flatMap taggedPair)

@[simp] theorem cycleCodeCheck_eq_true {B : Type*} [DecidableEq B] [Inhabited B]
    (word : List (TaggedEdge B)) (rotation : ℕ) (blocks : List (TaggedBlock B)) :
    cycleCodeCheck word rotation blocks=true ↔ blocks≠[] ∧
      (word.rotate rotation).IsChain TaggedCompatible ∧
      taggedAtoms (word.rotate rotation)=blocks.flatMap taggedPair := by
  simp [cycleCodeCheck]

section Soundness
open scoped Matrix
variable {B : Type*} [DecidableEq B] [Inhabited B]
variable (C : B→Matrix State State ℝ)

/-- The complete signed matrix equality follows from finite acceptance. -/
theorem pathCodeCheck_sound (word : List (TaggedEdge B)) (code : TaggedPathCode B)
    (h : pathCodeCheck word code=true) :
    (word.map (TaggedEdge.matrixWith C)).prod=code.matrixWith C := by
  obtain ⟨hchain,he⟩:= (pathCodeCheck_eq_true word code).mp h
  rw [←taggedAtoms_matrix C word hchain,he,TaggedPathCode.atoms_matrixWith]

/-- The signed cyclic matrix equality before the final trace rotation. -/
theorem cycleCodeCheck_sound_rotated (word : List (TaggedEdge B)) (rotation : ℕ)
    (blocks : List (TaggedBlock B)) (h : cycleCodeCheck word rotation blocks=true) :
    ((word.rotate rotation).map (TaggedEdge.matrixWith C)).prod=
      (blocks.map (TaggedBlock.matrixWith C)).prod := by
  obtain ⟨_,hchain,he⟩:= (cycleCodeCheck_eq_true word rotation blocks).mp h
  rw [←taggedAtoms_matrix C (word.rotate rotation) hchain,he,taggedPairs_matrix]

end Soundness
end SubmittedGenus.CapFourMass.ExecutableModes
