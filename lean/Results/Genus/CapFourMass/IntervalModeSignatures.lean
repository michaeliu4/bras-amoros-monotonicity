import Results.Genus.CapFourMass.IntervalProgramTableSeries

/-! Label erasure is used solely for reusable numeric component signatures.
The physical source program is still validated with its canonical shared
labels before the original mixed-source majorization theorem is invoked. -/
namespace SubmittedGenus.CapFourMass.Interval.ModeSignatures
open ActualComponent ExecutableModes RationalTables

deriving instance DecidableEq for ModeProgram

def eraseBlock {B : Type*} (b : TaggedBlock B) : TaggedBlock Unit := ⟨b.run,()⟩

def erasePath {B : Type*} : TaggedPathCode B→TaggedPathCode Unit
  | .pure s=>.pure s
  | .carried pre _ n hn bs post=>.carried pre () n hn (bs.map eraseBlock) post

def eraseProgram {B : Type*} : ModeProgram B→ModeProgram Unit
  | .path q=>.path (erasePath q)
  | .cycle _ b bs=>.cycle 0 (eraseBlock b) (bs.map eraseBlock)
  | .isolated=>.isolated

theorem erasePath_pure {B : Type*} (q : TaggedPathCode B) (x y : State→ℝ) :
    RationalRuns.pathPure (erasePath q) x y=RationalRuns.pathPure q x y := by
  cases q <;> simp [erasePath,RationalRuns.pathPure,List.map_map,Function.comp_def,eraseBlock]

theorem erasePath_absolute {B : Type*} (q : TaggedPathCode B) (x y : State→ℝ) :
    RationalRuns.pathAbs (erasePath q) x y=RationalRuns.pathAbs q x y := by
  cases q <;> simp [erasePath,RationalRuns.pathAbs,List.map_map,Function.comp_def,eraseBlock]

theorem eraseProgram_pure {B : Type*} (q : ModeProgram B) (x y : State→ℝ) :
    (eraseProgram q).rationalPure x y=q.rationalPure x y := by
  cases q with
  | path q=>exact erasePath_pure q x y
  | cycle k b bs=>simp [eraseProgram,ModeProgram.rationalPure,RationalRuns.cyclePure,
      List.map_map,Function.comp_def,eraseBlock]
  | isolated=>rfl

theorem eraseProgram_absolute {B : Type*} (q : ModeProgram B) (x y : State→ℝ) :
    (eraseProgram q).rationalAbsolute x y=q.rationalAbsolute x y := by
  cases q with
  | path q=>exact erasePath_absolute q x y
  | cycle k b bs=>simp [eraseProgram,ModeProgram.rationalAbsolute,List.map_map,Function.comp_def,eraseBlock]
  | isolated=>rfl

abbrev Mask := Fin 4→Bool

def maskValues (m : Mask) : State→ℝ := fun i=>if m i then 1 else 0

def maskBoxes (m : Mask) : Vector 4 := fun i=>if m i then point 1 else point 0

theorem maskBoxes_contains (m : Mask) : VContains (maskBoxes m) (maskValues m) := by
  intro i
  unfold maskBoxes maskValues
  split_ifs
  · simpa using point_contains 1
  · simpa using point_contains 0

structure Signature where
  program : ModeProgram Unit
  leftMask : Mask
  rightMask : Mask
  deriving DecidableEq

noncomputable def Signature.pureValue (s : Signature) : ℝ :=
  s.program.rationalPure (maskValues s.leftMask) (maskValues s.rightMask)
noncomputable def Signature.absoluteValue (s : Signature) : ℝ :=
  s.program.rationalAbsolute (maskValues s.leftMask) (maskValues s.rightMask)

def maskData {m r p : ℕ} (L : FreeLayout m r p) (c : Fin L.count)
    (i : Fin (L.edges c+1)) : Mask :=
  fun v=>decide (RawGraph.SourceModel.Domain r p 4 (L.vertex c i) (v.val+1))

theorem maskData_values {m r p : ℕ} (L : FreeLayout m r p) (c : Fin L.count)
    (i : Fin (L.edges c+1)) : maskValues (maskData L c i)=L.mask c i := by
  ext v
  simp [maskValues,maskData,FreeLayout.mask]

def physicalSignature {m r p : ℕ} {B : Type*} (L : FreeLayout m r p)
    (program : Fin L.count→ModeProgram B) (c : Fin L.count) : Signature :=
  ⟨eraseProgram (program c),maskData L c 0,maskData L c (Fin.last _)⟩

theorem physicalSignature_pure {m r p : ℕ} {B : Type*} (L : FreeLayout m r p)
    (program : Fin L.count→ModeProgram B) (c : Fin L.count) :
    (physicalSignature L program c).pureValue=
      (program c).rationalPure (L.mask c 0) (L.mask c (Fin.last _)) := by
  unfold physicalSignature Signature.pureValue
  rw [eraseProgram_pure,maskData_values,maskData_values]

theorem physicalSignature_absolute {m r p : ℕ} {B : Type*} (L : FreeLayout m r p)
    (program : Fin L.count→ModeProgram B) (c : Fin L.count) :
    (physicalSignature L program c).absoluteValue=
      (program c).rationalAbsolute (L.mask c 0) (L.mask c (Fin.last _)) := by
  unfold physicalSignature Signature.absoluteValue
  rw [eraseProgram_absolute,maskData_values,maskData_values]

structure Entry where
  signature : Signature
  pureBox : Box
  absoluteBox : Box
  pure_contains : Contains pureBox signature.pureValue
  absolute_contains : Contains absoluteBox signature.absoluteValue

def certify (C : CachedContext) (s : Signature) (pureBox absoluteBox : Box)
    (hp : C.pure s.program (maskBoxes s.leftMask) (maskBoxes s.rightMask)=pureBox)
    (ha : C.absolute s.program (maskBoxes s.leftMask) (maskBoxes s.rightMask)=absoluteBox) : Entry where
  signature:=s
  pureBox:=pureBox
  absoluteBox:=absoluteBox
  pure_contains:=by
    rw [←hp]
    exact C.pure_contains s.program (maskBoxes_contains _) (maskBoxes_contains _)
  absolute_contains:=by
    rw [←ha]
    exact C.absolute_contains s.program (maskBoxes_contains _) (maskBoxes_contains _)

end SubmittedGenus.CapFourMass.Interval.ModeSignatures
