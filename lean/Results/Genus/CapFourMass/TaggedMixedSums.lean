import Results.Genus.CapFourMass.TaggedModeSums

/-! Pointed shared-label majorization for the original mixed evaluator. The
all-plus assignment is retained exactly and subtracted only after the complete
absolute partition. This does not provide an executable source layout. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph.Transfer CapFiveMass.MatrixSource
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I J B : Type*} [Fintype I] [Fintype J]

lemma absolute_sum_point_split (a : I→ℝ) (i0 : I) :
    (∑ i,|a i|)=|a i0|+(∑ i,if i=i0 then 0 else |a i|) := by
  classical
  calc
    _ = ∑ i,((if i=i0 then |a i| else 0)+(if i=i0 then 0 else |a i|)) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by rw [Finset.sum_add_distrib]; simp

lemma mixed_le_sub_of_total_le (a : I→ℝ) (i0 : I) (A : ℝ)
    (hA : (∑ i,|a i|)≤A) :
    (∑ i,if i=i0 then 0 else |a i|)≤A-|a i0| := by
  classical
  rw [absolute_sum_point_split a i0] at hA
  linarith

/-- An explicit pointed injection retains the exact all-plus image. Signed
weights are first completed, and only then are their absolute values summed. -/
theorem pointed_mixed_absolute_le (f : I→J) (hf : Function.Injective f)
    (i0 : I) (j0 : J) (hpoint : f i0=j0) (a : I→ℝ) (w : J→ℝ)
    (hsource : ∀ i,a i=w (f i)) :
    (∑ i,if i=i0 then 0 else |a i|)≤(∑ j,|w j|)-|w j0| := by
  classical
  have hA : (∑ i,|a i|)≤∑ j,|w j| := by
    simp_rw [hsource]
    exact sum_injective_nonnegative f hf _ (fun _ => abs_nonneg _)
  simpa only [hsource,hpoint] using mixed_le_sub_of_total_le a i0 _ hA

/-- For a nonnegative all-plus contribution the producer subtracts its signed
value, which is exactly its absolute value. -/
theorem pointed_mixed_le (f : I→J) (hf : Function.Injective f)
    (i0 : I) (j0 : J) (hpoint : f i0=j0) (a : I→ℝ) (w : J→ℝ)
    (hsource : ∀ i,a i=w (f i)) (hplus : 0≤w j0) :
    (∑ i,if i=i0 then 0 else |a i|)≤(∑ j,|w j|)-w j0 := by
  classical
  simpa only [abs_of_nonneg hplus] using
    pointed_mixed_absolute_le f hf i0 j0 hpoint a w hsource

lemma pointed_absolute_difference_nonneg (w : J→ℝ) (j0 : J) :
    0≤(∑ j,|w j|)-|w j0| := by
  exact sub_nonneg.mpr (Finset.single_le_sum (fun j _ => abs_nonneg (w j)) (Finset.mem_univ j0))

lemma pointed_difference_nonneg (w : J→ℝ) (j0 : J) :
    0≤(∑ j,|w j|)-w j0 := by
  have hh:=pointed_absolute_difference_nonneg w j0
  have hp:=le_abs_self (w j0)
  linarith

/-- Constant positive canonical choices map to the constant positive run-slot
assignment, including the initial/closing slot. -/
lemma tagged_allPlus_image (bs : List (TaggedBlock B)) (tag : B) :
    taggedModeStates (fun _ : B => (0 : Mode)) bs 0=(fun _ => 0) := by
  have hh:=taggedModeStates_comp (fun _ : B => (0 : Mode)) bs tag
  exact hh

/-- Exact all-plus term of a carried path. -/
lemma tagged_path_allPlus_weight (pre post : Option StrongRun) (tag : B)
    (n : ℕ) (hn : 1≤n) (bs : List (TaggedBlock B)) (x y : State→ℝ) :
    x ⬝ᵥ (((TaggedPathCode.carried pre tag n hn bs post).matrixWith
      (labelledModeMatrix (fun _ : B => 0)))*ᵥ y)=
      modePathPure bs.length (taggedModeMatrices bs)
        (fun j => ((frameMatrix pre*ᵥ x) ⬝ᵥ modeVector j)*modeRoot j^n)
        (fun j => modeVector j ⬝ᵥ (frameMatrix post*ᵥ y)) := by
  rw [tagged_carried_path_weight,tagged_allPlus_image bs tag]
  rfl

/-- The source shared-label mixed sum is bounded by the original independent
absolute path partition minus its exact all-plus scalar. -/
theorem tagged_path_mixed_sum_le (choices : I→B→Mode) (i0 : I)
    (hplus : choices i0=(fun _ => 0))
    (pre post : Option StrongRun) (tag : B) (n : ℕ) (hn : 1≤n)
    (bs : List (TaggedBlock B)) (x y : State→ℝ)
    (hinj : Function.Injective (fun i => taggedModeStates (choices i) bs (choices i tag)))
    (hpos : 0≤x ⬝ᵥ (((TaggedPathCode.carried pre tag n hn bs post).matrixWith
      (labelledModeMatrix (fun _ : B => 0)))*ᵥ y)) :
    (∑ i,if i=i0 then 0 else
      |x ⬝ᵥ (((TaggedPathCode.carried pre tag n hn bs post).matrixWith
        (labelledModeMatrix (choices i)))*ᵥ y)|) ≤
      framedPathAbsolute pre post n (bs.map TaggedBlock.run) x y-
        x ⬝ᵥ (((TaggedPathCode.carried pre tag n hn bs post).matrixWith
          (labelledModeMatrix (fun _ : B => 0)))*ᵥ y) := by
  classical
  have hh:=mixed_le_sub_of_total_le
    (fun i => x ⬝ᵥ (((TaggedPathCode.carried pre tag n hn bs post).matrixWith
      (labelledModeMatrix (choices i)))*ᵥ y)) i0 _
    (tagged_path_absolute_sum_le choices pre post tag n hn bs x y hinj)
  simpa only [hplus,abs_of_nonneg hpos] using hh

/-- Cyclic mixed evaluation retains the exact same all-plus closing mode. -/
theorem tagged_cycle_mixed_sum_le (choices : I→B→Mode) (i0 : I)
    (hplus : choices i0=(fun _ => 0)) (b : TaggedBlock B) (bs : List (TaggedBlock B))
    (hinj : Function.Injective (fun i => taggedModeStates (choices i) bs (choices i b.label)))
    (hpos : 0≤((b.matrixWith (labelledModeMatrix (fun _ : B => 0)))*
      (bs.map (TaggedBlock.matrixWith (labelledModeMatrix (fun _ : B => 0)))).prod).trace) :
    (∑ i,if i=i0 then 0 else
      |((b.matrixWith (labelledModeMatrix (choices i)))*
        (bs.map (TaggedBlock.matrixWith (labelledModeMatrix (choices i)))).prod).trace|) ≤
      coupledCycleAbsolute ((b::bs).map TaggedBlock.run)-
        ((b.matrixWith (labelledModeMatrix (fun _ : B => 0)))*
          (bs.map (TaggedBlock.matrixWith (labelledModeMatrix (fun _ : B => 0)))).prod).trace := by
  classical
  have hh:=mixed_le_sub_of_total_le
    (fun i => ((b.matrixWith (labelledModeMatrix (choices i)))*
      (bs.map (TaggedBlock.matrixWith (labelledModeMatrix (choices i)))).prod).trace) i0 _
    (tagged_cycle_absolute_sum_le choices b bs hinj)
  simpa only [hplus,abs_of_nonneg hpos] using hh

lemma tagged_path_difference_nonneg (pre post : Option StrongRun) (tag : B)
    (n : ℕ) (hn : 1≤n) (bs : List (TaggedBlock B)) (x y : State→ℝ) :
    0≤framedPathAbsolute pre post n (bs.map TaggedBlock.run) x y-
      x ⬝ᵥ (((TaggedPathCode.carried pre tag n hn bs post).matrixWith
        (labelledModeMatrix (fun _ : B => 0)))*ᵥ y) := by
  rw [tagged_path_allPlus_weight,←tagged_path_independent_absolute]
  exact modePathMixed_nonneg _ _ _ _

lemma tagged_cycle_allPlus_weight (b : TaggedBlock B) (bs : List (TaggedBlock B)) :
    ((b.matrixWith (labelledModeMatrix (fun _ : B => 0)))*
      (bs.map (TaggedBlock.matrixWith (labelledModeMatrix (fun _ : B => 0)))).prod).trace=
      sourceTerm bs.length (fun _ _ => 1) (taggedModeMatrices bs)
        (fun j => b.run.spectral j 0) (fun _ => 0) := by
  rw [tagged_cycle_weight,tagged_allPlus_image bs b.label]

lemma tagged_cycle_difference_nonneg (b : TaggedBlock B) (bs : List (TaggedBlock B)) :
    0≤coupledCycleAbsolute ((b::bs).map TaggedBlock.run)-
      ((b.matrixWith (labelledModeMatrix (fun _ : B => 0)))*
        (bs.map (TaggedBlock.matrixWith (labelledModeMatrix (fun _ : B => 0)))).prod).trace := by
  rw [tagged_cycle_allPlus_weight,←tagged_cycle_independent_absolute]
  exact pointed_difference_nonneg
    (fun ω : Fin (bs.length+1)→Mode => sourceTerm bs.length (fun _ _ => 1)
      (taggedModeMatrices bs) (fun j => b.run.spectral j (ω 0)) ω) (fun _ => 0)

end SubmittedGenus.CapFourMass.ActualComponent
