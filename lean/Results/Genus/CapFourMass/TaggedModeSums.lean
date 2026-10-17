import Results.Genus.CapFourMass.TaggedModeWeights

/-! Shared canonical labels inject into independent run slots.  The resulting
absolute sum comparison takes absolute values only after each complete physical
matrix contraction, and does not assume that distinct runs have distinct labels. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph.Transfer CapFiveMass.MatrixSource
variable {B I : Type*} [Fintype I]

lemma sum_injective_nonnegative {J : Type*} [Fintype J] (f : I→J)
    (hf : Function.Injective f) (w : J→ℝ) (hw : ∀ j,0 ≤ w j) :
    (∑ i,w (f i)) ≤ ∑ j,w j := by
  classical
  calc
    (∑ i,w (f i)) = ∑ j ∈ Finset.univ.image f,w j :=
      (Finset.sum_image (fun a _ b _ hab => hf hab)).symm
    _ ≤ ∑ j,w j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hw j)

lemma tagged_absolute_matrixRun (bs : List (TaggedBlock B)) :
    matrixRun bs.length (fun k => absoluteMatrix (taggedModeMatrices bs k))=
      (bs.map (fun b => b.run.dominated.matrix)).prod := by
  induction bs with
  | nil => simp [matrixRun]
  | cons b bs ih =>
    change absoluteMatrix b.run.spectral *
      matrixRun bs.length (fun k => absoluteMatrix (taggedModeMatrices bs k))=
      b.run.dominated.matrix*(bs.map (fun b => b.run.dominated.matrix)).prod
    rw [ih,CoupledRun.dominated_matrix]

lemma tagged_path_independent_absolute (pre post : Option StrongRun) (n : ℕ)
    (bs : List (TaggedBlock B)) (x y : State→ℝ) :
    modePathAbsolute bs.length (taggedModeMatrices bs)
      (fun j => ((frameMatrix pre*ᵥ x) ⬝ᵥ modeVector j)*modeRoot j^n)
      (fun j => modeVector j ⬝ᵥ (frameMatrix post*ᵥ y))=
      framedPathAbsolute pre post n (bs.map TaggedBlock.run) x y := by
  rw [modePathAbsolute_eq_matrix,tagged_absolute_matrixRun]
  simp only [framedPathAbsolute,coupledPathAbsolute,List.map_map,Function.comp_def]
  congr 1
  funext j
  simp only [carryBoundary,dotProduct_comm (frameMatrix pre*ᵥ x),mul_comm]

/-- Canonical choices may repeat labels across blocks.  Coverage supplies only
an injection into the finite independent slot assignments. -/
theorem tagged_path_absolute_sum_le (choices : I→B→Mode)
    (pre post : Option StrongRun) (tag : B) (n : ℕ) (hn : 1 ≤ n)
    (bs : List (TaggedBlock B)) (x y : State→ℝ)
    (hinj : Function.Injective (fun i => taggedModeStates (choices i) bs (choices i tag))) :
    (∑ i,|x ⬝ᵥ (((TaggedPathCode.carried pre tag n hn bs post).matrixWith
      (labelledModeMatrix (choices i)))*ᵥ y)|) ≤
      framedPathAbsolute pre post n (bs.map TaggedBlock.run) x y := by
  simp_rw [tagged_carried_path_weight]
  rw [← tagged_path_independent_absolute]
  exact sum_injective_nonnegative _ hinj _ (fun _ => abs_nonneg _)

lemma tagged_cycle_independent_absolute (b : TaggedBlock B) (bs : List (TaggedBlock B)) :
    (∑ ω : Fin (bs.length+1)→Mode,
      |sourceTerm bs.length (fun _ _ => 1) (taggedModeMatrices bs)
        (fun j => b.run.spectral j (ω 0)) ω|)=
      coupledCycleAbsolute ((b::bs).map TaggedBlock.run) := by
  rw [cycle_absolute_eq_trace,tagged_absolute_matrixRun,Matrix.trace_mul_comm]
  simp only [coupledCycleAbsolute,List.map_cons,List.prod_cons,List.map_map,
    Function.comp_def,CoupledRun.dominated_matrix]

/-- The first cycle slot is its actual closing mode. -/
theorem tagged_cycle_absolute_sum_le (choices : I→B→Mode)
    (b : TaggedBlock B) (bs : List (TaggedBlock B))
    (hinj : Function.Injective (fun i => taggedModeStates (choices i) bs (choices i b.label))) :
    (∑ i,|((b.matrixWith (labelledModeMatrix (choices i)))*
      (bs.map (TaggedBlock.matrixWith (labelledModeMatrix (choices i)))).prod).trace|) ≤
      coupledCycleAbsolute ((b::bs).map TaggedBlock.run) := by
  simp_rw [tagged_cycle_weight]
  rw [← tagged_cycle_independent_absolute]
  have h:=sum_injective_nonnegative
    (fun i => taggedModeStates (choices i) bs (choices i b.label)) hinj
    (fun ω => |sourceTerm bs.length (fun _ _ => 1) (taggedModeMatrices bs)
      (fun j => b.run.spectral j (ω 0)) ω|) (fun _ => abs_nonneg _)
  simpa only [taggedModeStates_zero] using h

end SubmittedGenus.CapFourMass.ActualComponent
