import Results.Genus.CapFourMass.TaggedModeEvaluation

/-! Tagged fixed-choice scalars are literally the complete finite mode weights
used by ModePartitions, even when several runs share one canonical label. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph.Transfer
variable {B : Type*}

def taggedModeMatrices (bs : List (TaggedBlock B)) (n : ℕ) : Matrix Mode Mode ℝ :=
  (bs.map (fun b => b.run.spectral)).getD n 0

def taggedModeStates (choice : B→Mode) : (bs : List (TaggedBlock B))→Mode→(Fin (bs.length+1)→Mode)
  | [],j => fun _ => j
  | b::bs,j => Fin.cons j (taggedModeStates choice bs (choice b.label))

def taggedModeLabels : (bs : List (TaggedBlock B))→B→(Fin (bs.length+1)→B)
  | [],tag => fun _ => tag
  | b::bs,tag => Fin.cons tag (taggedModeLabels bs b.label)

lemma taggedModeStates_zero (choice : B→Mode) (bs : List (TaggedBlock B)) (j : Mode) :
    taggedModeStates choice bs j 0=j := by cases bs <;> rfl
lemma taggedModeMatrices_zero (b : TaggedBlock B) (bs : List (TaggedBlock B)) :
    taggedModeMatrices (b::bs) 0=b.run.spectral := rfl
lemma taggedModeMatrices_shift (b : TaggedBlock B) (bs : List (TaggedBlock B)) :
    shift (taggedModeMatrices (b::bs))=taggedModeMatrices bs := by funext n; rfl

lemma taggedModeStates_comp (choice : B→Mode) (bs : List (TaggedBlock B)) (tag : B) :
    taggedModeStates choice bs (choice tag)=choice ∘ taggedModeLabels bs tag := by
  induction bs generalizing tag with
  | nil => rfl
  | cons b bs ih =>
    rw [taggedModeStates,taggedModeLabels,ih]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Surjective occurrence of labels is enough for injection of complete choices;
repeated labels are allowed and are not replaced by independent choices. -/
lemma taggedModeStates_injective (bs : List (TaggedBlock B)) (tag : B)
    (hlabels : Function.Surjective (taggedModeLabels bs tag)) :
    Function.Injective (fun choice : B→Mode => taggedModeStates choice bs (choice tag)) := by
  intro f g h
  change taggedModeStates f bs (f tag)=taggedModeStates g bs (g tag) at h
  rw [taggedModeStates_comp,taggedModeStates_comp] at h
  funext b
  obtain ⟨i,rfl⟩:=hlabels b
  exact congrFun h i

lemma taggedModeChain_source (choice : B→Mode) (bs : List (TaggedBlock B))
    (j : Mode) (finish : Mode→ℝ) :
    taggedModeChain choice bs j finish=
      sourceTerm bs.length (fun _ _ => 1) (taggedModeMatrices bs) finish (taggedModeStates choice bs j) := by
  induction bs generalizing j with
  | nil => simp [taggedModeChain,sourceTerm,taggedModeStates]
  | cons b bs ih =>
    simp only [taggedModeChain,taggedModeStates,List.length_cons,sourceTerm_cons,
      one_mul,taggedModeStates_zero,taggedModeMatrices_zero,taggedModeMatrices_shift]
    change b.run.spectral j (choice b.label)*taggedModeChain choice bs (choice b.label) finish=
      b.run.spectral j (choice b.label)*sourceTerm bs.length (fun _ _ => 1)
        (taggedModeMatrices bs) finish (taggedModeStates choice bs (choice b.label))
    rw [ih]

/-- The fixed shared-label carried path is a single original modePathWeight. -/
theorem tagged_carried_path_weight (choice : B→Mode) (pre post : Option StrongRun)
    (tag : B) (n : ℕ) (hn : 1≤n) (bs : List (TaggedBlock B)) (x y : State→ℝ) :
    x ⬝ᵥ (((TaggedPathCode.carried pre tag n hn bs post).matrixWith (labelledModeMatrix choice))*ᵥ y)=
      modePathWeight bs.length (taggedModeMatrices bs)
        (fun j => ((frameMatrix pre*ᵥ x) ⬝ᵥ modeVector j)*modeRoot j^n)
        (fun j => modeVector j ⬝ᵥ (frameMatrix post*ᵥ y))
        (taggedModeStates choice bs (choice tag)) := by
  rw [tagged_path_evaluation]
  simp only [TaggedPathCode.modeTerm,modePathWeight,taggedModeStates_zero,taggedModeChain_source]

/-- A cycle closes against its actual first tagged mode, not a new free state. -/
theorem tagged_cycle_weight (choice : B→Mode) (b : TaggedBlock B) (bs : List (TaggedBlock B)) :
    ((b.matrixWith (labelledModeMatrix choice))*(bs.map (TaggedBlock.matrixWith (labelledModeMatrix choice))).prod).trace=
      sourceTerm bs.length (fun _ _ => 1) (taggedModeMatrices bs)
        (fun j => b.run.spectral j (choice b.label))
        (taggedModeStates choice bs (choice b.label)) := by
  rw [tagged_cycle_evaluation,taggedModeChain_source]

end SubmittedGenus.CapFourMass.ActualComponent
