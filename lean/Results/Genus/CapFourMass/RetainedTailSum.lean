import Results.Genus.CapFourMass.NormalizedModeTail

/-! The exact finite sum over canonical tail states. The port coordinates are
fixed, receive no tail weight, and enter through normalized signed mode edges. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.CarryLocalization
open FixedPivot
attribute [local instance] Classical.propDecidable Classical.decEq

lemma tail_left_inner (free : Prop) (j : Mode) (left : State) :
    tailLeftVector free j left ⬝ᵥ modeVector j=
      if free then freeBoundary ⬝ᵥ modeVector j else modeRoot j*modeVector j left/halfWeight left := by
  unfold tailLeftVector
  split_ifs
  · rfl
  · rw [dot_scale_left,modeVector_dot,if_pos rfl,mul_one]

lemma tail_right_inner (loop : Prop) (j : Mode) (right : State) :
    modeVector j ⬝ᵥ tailRightVector loop j right=
      if loop then loopBoundary ⬝ᵥ modeVector j else modeRoot j*modeVector j right/halfWeight right := by
  unfold tailRightVector
  split_ifs
  · exact dotProduct_comm _ _
  · rw [dot_scale_right,modeVector_dot,if_pos rfl,mul_one]

/-- A zero-tail-edge contraction is valid when a surviving port places at
least one boundary in this mode's image. The isolated free/loop corner is
intentionally excluded; its two-mode decomposition is supplied separately. -/
lemma normalizedTailSum_factor (n : ℕ) (free loop : Prop) (j : Mode) (left right : State)
    (hzero : n=0 → ¬(free ∧ loop)) :
    (∑ y : Fin (n+1)→State,normalizedTailTerm n free loop j left right y)=
      modeRoot j^n*
        (if free then freeBoundary ⬝ᵥ modeVector j else modeRoot j*modeVector j left/halfWeight left)*
        (if loop then loopBoundary ⬝ᵥ modeVector j else modeRoot j*modeVector j right/halfWeight right) := by
  rw [normalizedTailSum_matrix]
  cases n with
  | zero =>
    simp only [pow_zero,Matrix.one_mulVec,one_mul]
    by_cases hf : free
    · have hl : ¬loop := fun hl => hzero rfl ⟨hf,hl⟩
      simp only [tailLeftVector,tailRightVector,if_pos hf,if_neg hl]
      rw [dot_scale_right]
      ring
    · by_cases hl : loop
      · simp only [tailLeftVector,tailRightVector,if_neg hf,if_pos hl]
        rw [dot_scale_left,dotProduct_comm (modeVector j) loopBoundary]
      · simp only [tailLeftVector,tailRightVector,if_neg hf,if_neg hl]
        rw [dot_scale_left,dot_scale_right,modeVector_dot,if_pos rfl,mul_one]
  | succ n =>
    rw [mode_power_path j (n+1) (by omega),tail_left_inner,tail_right_inner]
    ring

section Retained
variable (N d : ℕ) (hN : d<N) (hbig : 2*d<N) (a : CarryRepresentative N d hN)

/-- A value-preserving index equivalence, using the proved positive tail size. -/
def retainedTailIndex : Fin (carryTailSize N d hN a-1+1)≃Fin (carryTailSize N d hN a) :=
  finCongr (by have:=carryTailSize_positive N d hN hbig a; omega)

@[simp] lemma retainedTailIndex_val (i : Fin (carryTailSize N d hN a-1+1)) :
    (retainedTailIndex N d hN hbig a i).val=i.val := rfl

/-- Exactly one full weight per tail vertex, cap 3 everywhere, the final loop
mask for fixed classes, and normalized edges to any surviving fixed core ports.
The index equivalence changes no natural-number position. -/
def retainedTailTerm (j : Mode) (left right : State)
    (y : Fin (carryTailSize N d hN a)→State) : ℝ :=
  normalizedTailTerm (carryTailSize N d hN a-1)
    (a.val.val+1=d) (a.val=portPartner N d hN a.val) j left right
    (y ∘ retainedTailIndex N d hN hbig a)

def retainedTailSum (j : Mode) (left right : State) : ℝ :=
  ∑ y : Fin (carryTailSize N d hN a)→State,retainedTailTerm N d hN hbig a j left right y

lemma retainedTailSum_reindex (j : Mode) (left right : State) :
    retainedTailSum N d hN hbig a j left right=
      ∑ y : Fin (carryTailSize N d hN a-1+1)→State,
        normalizedTailTerm (carryTailSize N d hN a-1)
          (a.val.val+1=d) (a.val=portPartner N d hN a.val) j left right y := by
  have he:=(Equiv.arrowCongr (retainedTailIndex N d hN hbig a) (Equiv.refl State)).sum_comp
    (retainedTailTerm N d hN hbig a j left right)
  unfold retainedTailSum
  rw [←he]
  apply Finset.sum_congr rfl
  intro y _
  unfold retainedTailTerm
  congr 1

include hbig in
lemma retained_tail_zero_has_port (hn : 1 ≤ freeCarrySize N d hN a-1) :
    carryTailSize N d hN a-1=0 → ¬(a.val.val+1=d ∧ a.val=portPartner N d hN a.val) := by
  intro ht ⟨hp,hf⟩
  have he:=freeCarry_edge_count N d hN hbig a
  rw [survivingPorts_fixed N d hN a hf,if_pos hp,ht] at he
  omega

/-- The complete finite physical tail sum is exactly its original canonical
signed mode factor. No absolute value has crossed this finite sum. -/
theorem retainedTailSum_eq_source (j : Mode) (left right : State)
    (hn : 1 ≤ freeCarrySize N d hN a-1) :
    retainedTailSum N d hN hbig a j left right=retainedSourceMode N d hN a j left right := by
  rw [retainedTailSum_reindex,normalizedTailSum_factor _ _ _ _ _ _
    (retained_tail_zero_has_port N d hN hbig a hn)]
  unfold retainedSourceMode initialPortMode terminalPortMode
  by_cases hf : a.val=portPartner N d hN a.val
  · simp only [if_pos hf,mul_one]
    ac_rfl
  · simp only [if_neg hf,mul_one]
    ac_rfl

end Retained
end SubmittedGenus.CapFourMass.CarryLocalization
