import Results.Genus.CapFourMass.TaggedCompiler

/-! Exact matrix compilation with arbitrary signed matrices on labelled carry
edges. Absolute values have not yet been introduced. -/
noncomputable section
open scoped Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph

section Matrices
variable {B : Type*} (C : B→Matrix State State ℝ)

def TaggedEdge.matrixWith : TaggedEdge B→Matrix State State ℝ
  | .strong => strongMatrix
  | .restricted => restrictedMatrix
  | .carry b => C b

def TaggedAtom.matrixWith : TaggedAtom B→Matrix State State ℝ
  | .strong s => s.matrix
  | .carry b n _ => C b^n

def TaggedBlock.matrixWith (b : TaggedBlock B) : Matrix State State ℝ :=
  b.run.strong.matrix*C b.label^b.run.carryLength

def TaggedPathCode.matrixWith : TaggedPathCode B→Matrix State State ℝ
  | .pure s => optionalStrongMatrix s
  | .carried pre tag n _ bs post => optionalStrongMatrix pre*C tag^n*
      (bs.map (TaggedBlock.matrixWith C)).prod*optionalStrongMatrix post

lemma compileTaggedRun_matrix [Inhabited B] (l : List (TaggedEdge B))
    (hl : l.IsChain TaggedCompatible) {g : List (TaggedEdge B)}
    (hg : g∈RunSegmentation.runs TaggedEdge.kind l) :
    (compileTaggedRun g).matrixWith C=(g.map (TaggedEdge.matrixWith C)).prod := by
  have hn:=RunSegmentation.run_nonempty TaggedEdge.kind l hg
  rw [tagged_run_product l hl (TaggedEdge.matrixWith C) hg]
  unfold compileTaggedRun
  rw [dif_neg hn]
  split
  · simp_all [TaggedAtom.matrixWith,StrongRun.matrix,TaggedEdge.matrixWith]
  · have he : g=[.restricted] := tagged_restricted_singleton l hl hg (by assumption)
    subst g
    simp only [List.length_singleton,pow_one]
    rfl
  · simp_all [TaggedAtom.matrixWith,TaggedEdge.matrixWith]

/-- Exact arbitrary signed matrix word compilation into labelled source runs. -/
theorem taggedAtoms_matrix [Inhabited B] (l : List (TaggedEdge B))
    (hl : l.IsChain TaggedCompatible) :
    ((taggedAtoms l).map (TaggedAtom.matrixWith C)).prod=
      (l.map (TaggedEdge.matrixWith C)).prod := by
  rw [RunSegmentation.product_runs TaggedEdge.kind l]
  unfold taggedAtoms
  rw [List.map_map]
  congr 1
  exact List.map_congr_left (fun g hg => compileTaggedRun_matrix C l hl hg)

lemma taggedPairs_matrix (bs : List (TaggedBlock B)) :
    ((bs.flatMap taggedPair).map (TaggedAtom.matrixWith C)).prod=
      (bs.map (TaggedBlock.matrixWith C)).prod := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons,List.map_append,List.prod_append,taggedPair,List.map_cons,
      List.map_nil,List.prod_cons,List.prod_nil,mul_one,TaggedAtom.matrixWith,ih,TaggedBlock.matrixWith]

lemma taggedOptional_matrix (s : Option StrongRun) :
    ((s.toList.map TaggedAtom.strong).map (TaggedAtom.matrixWith C)).prod=optionalStrongMatrix s := by
  cases s <;> simp [optionalStrongMatrix,TaggedAtom.matrixWith]

/-- Typed optional frames preserve the complete signed matrix contraction. -/
theorem TaggedPathCode.atoms_matrixWith (q : TaggedPathCode B) :
    (q.atoms.map (TaggedAtom.matrixWith C)).prod=q.matrixWith C := by
  cases q with
  | pure s => exact taggedOptional_matrix C s
  | carried pre tag n hn bs post =>
    simp only [TaggedPathCode.atoms,List.map_append,List.prod_append,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one,taggedOptional_matrix,taggedPairs_matrix,
      TaggedAtom.matrixWith,TaggedPathCode.matrixWith]

end Matrices
end SubmittedGenus.CapFourMass.ActualComponent
