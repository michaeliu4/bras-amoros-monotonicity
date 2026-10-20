import Results.Genus.CapFourMass.SignedPhysicalSource
import Results.Genus.CapFourMass.TaggedMixedSums

/-! The genuine canonical all-positive assignment has a nonnegative complete
physical scalar and maps to the all-positive run slots. These discharge the
pointed mixed evaluator's distinguished-point premises for source components. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot CarryLocalization
attribute [local instance] Classical.propDecidable Classical.decEq

lemma tagged_allPlus_matrix_nonneg {B : Type*} (e : TaggedEdge B) (v w : State) :
    0≤e.matrixWith (labelledModeMatrix (fun _ : B => 0)) v w := by
  cases e with
  | strong => exact transfer_nonneg 4 4 v w
  | restricted => exact transfer_nonneg 4 3 v w
  | carry tag =>
    change 0≤lam*(qplus v*qplus w)
    exact mul_nonneg lam_pos.le (mul_nonneg (qplus_nonneg v) (qplus_nonneg w))

lemma physicalSignedMass_nonneg_of_kernel {m r p : ℕ}
    (K : Fin (m-1)→Fin (m-1)→State→State→ℝ)
    (hK : ∀ i j v w,0≤K i j v w) (c : Component m r p) :
    0≤physicalSignedMass K c := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact pow_nonneg radius_pos.le _
    · rfl
  · unfold signedKernelProduct
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _ => hK _ _ _ _)
    · split_ifs
      · exact hK _ _ _ _
      · norm_num

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)

lemma sourceSignedKernel_allPlus_nonneg (i j : Fin (r+N-1)) (v w : State) :
    0≤sourceSignedKernel hd hN (fun _ => 0) i j v w := by
  apply div_nonneg _ (mul_nonneg (halfWeight_pos v).le (halfWeight_pos w).le)
  unfold sourceSignedMatrix
  split_ifs with h
  · exact tagged_allPlus_matrix_nonneg _ v w
  · rfl

lemma physical_allPlus_nonneg (c : Component (r+N) r (r+d)) :
    0≤physicalSignedMass (sourceSignedKernel hd hN (fun _ => 0)) c :=
  physicalSignedMass_nonneg_of_kernel _ (sourceSignedKernel_allPlus_nonneg hd hN) c

lemma componentChoice_allPlus (c : Component (r+N) r (r+d)) :
    componentChoice hr hN hbig c (fun _ => false)=(fun _ => 0) := by
  funext a
  cases a with
  | none => rfl
  | some a =>
    simp only [componentChoice]
    split_ifs <;> rfl

lemma component_allPlus_nonneg (c : Component (r+N) r (r+d)) :
    0≤physicalSignedMass (sourceSignedKernel hd hN
      (componentChoice hr hN hbig c (fun _ => false))) c := by
  rw [componentChoice_allPlus]
  exact physical_allPlus_nonneg hd hN c

lemma component_allPlus_slot_image (c : Component (r+N) r (r+d))
    (bs : List (TaggedBlock (Option (CarryRepresentative N d hN))))
    (tag : Option (CarryRepresentative N d hN)) :
    taggedModeStates (componentChoice hr hN hbig c (fun _ => false)) bs
      (componentChoice hr hN hbig c (fun _ => false) tag)=(fun _ => 0) := by
  rw [componentChoice_allPlus]
  exact tagged_allPlus_image bs tag

end Source
end SubmittedGenus.CapFourMass.ActualComponent
