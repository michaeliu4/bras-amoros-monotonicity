import Results.Genus.CapFourMass.IsolatedModeSource
import Results.Genus.CapFourMass.TaggedMixedSums

/-! The exact distinguished positive source coefficient at the isolated
carry-loop corner. The canonical positive Bool is false, and the other mode
remains in the mixed remainder. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq

lemma isolated_allPlus_weight_nonneg :
    0≤(freeBoundary ⬝ᵥ modeVector 0)*(loopBoundary ⬝ᵥ modeVector 0) := by
  have hf (i : State) : 0≤freeBoundary i := by
    unfold freeBoundary halfScale
    apply mul_nonneg (halfWeight_pos i).le
    fin_cases i <;> norm_num
  have hl (i : State) : 0≤loopBoundary i := by
    unfold loopBoundary halfScale
    apply mul_nonneg (halfWeight_pos i).le
    fin_cases i <;> norm_num
  apply mul_nonneg
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hf i) (qplus_nonneg i))
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hl i) (qplus_nonneg i))

section Isolated
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (a : CarryRepresentative N d hN) (hz : freeCarrySize N d hN a=1)
include hz

/-- The actual empty core is summed once, before any absolute value. -/
theorem singleton_component_coefficient
    (b : ModeFiber hr hN hbig (owner hr hN hbig a)→Bool) :
    (∑ x : CoreAt hN (owner hr hN hbig a)→State,
      componentModeTerm hr hd hN hbig (owner hr hN hbig a) x b)=
      (freeBoundary ⬝ᵥ modeVector (choiceMode (b (singletonMode hr hN hbig a))))*
        (loopBoundary ⬝ᵥ modeVector (choiceMode (b (singletonMode hr hN hbig a)))) := by
  letI : IsEmpty (CoreAt hN (owner hr hN hbig a)):=singleton_core_empty hr hd hN hbig a hz
  simp_rw [singleton_component_term hr hd hN hbig a hz]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_eq_zero,pow_zero,one_nsmul]

/-- The original all-plus coefficient uses false, not true. -/
theorem singleton_component_allPlus :
    (∑ x : CoreAt hN (owner hr hN hbig a)→State,
      componentModeTerm hr hd hN hbig (owner hr hN hbig a) x (fun _ => false))=
      (freeBoundary ⬝ᵥ modeVector 0)*(loopBoundary ⬝ᵥ modeVector 0) := by
  simpa only [choiceMode,Bool.false_eq_true,if_false] using
    singleton_component_coefficient hr hd hN hbig a hz (fun _ => false)

lemma singleton_component_allPlus_nonneg :
    0≤(∑ x : CoreAt hN (owner hr hN hbig a)→State,
      componentModeTerm hr hd hN hbig (owner hr hN hbig a) x (fun _ => false)) := by
  rw [singleton_component_allPlus hr hd hN hbig a hz]
  exact isolated_allPlus_weight_nonneg

/-- The isolated producer's absolute-minus-pure expression is exactly the
complete canonical mixed source, including its negative mode. -/
theorem singleton_component_mixed :
    (∑ b : ModeFiber hr hN hbig (owner hr hN hbig a)→Bool,
      if b=(fun _ => false) then 0 else
        |∑ x : CoreAt hN (owner hr hN hbig a)→State,
          componentModeTerm hr hd hN hbig (owner hr hN hbig a) x b|)=
      carryAbsolute 0 freeBoundary loopBoundary-
        (freeBoundary ⬝ᵥ modeVector 0)*(loopBoundary ⬝ᵥ modeVector 0) := by
  have hh:=ActualComponent.absolute_sum_point_split
    (fun b : ModeFiber hr hN hbig (owner hr hN hbig a)→Bool =>
      ∑ x : CoreAt hN (owner hr hN hbig a)→State,
        componentModeTerm hr hd hN hbig (owner hr hN hbig a) x b) (fun _ => false)
  rw [singleton_component_absolute hr hd hN hbig a hz,
    singleton_component_allPlus hr hd hN hbig a hz,
    abs_of_nonneg isolated_allPlus_weight_nonneg] at hh
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  convert hh.symm using 2
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> rfl

end Isolated
end SubmittedGenus.CapFourMass.CarryLocalization
