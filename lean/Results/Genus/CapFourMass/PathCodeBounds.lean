import Results.Genus.CapFourMass.CompilerCounts
import Results.Genus.CapFourMass.OptionalFrames

/-! Analytic bounds for the complete typed source-path compiler. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open CapFiveMass.MatrixBounds

/-- The original endpoint estimate also covers the empty edge word. -/
lemma identity_path_le (x y : State → ℝ) :
    x ⬝ᵥ y ≤ Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y) := by
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  simpa only [mul_pow,Real.sq_sqrt (vectorEnergy_nonneg x),
    Real.sq_sqrt (vectorEnergy_nonneg y)] using dot_sq_le x y

lemma optionalStrongMatrix_eq_frame (s : Option StrongRun) :
    optionalStrongMatrix s=frameMatrix s := by cases s <;> rfl
lemma optionalStrongCount_eq_frame (s : Option StrongRun) :
    optionalStrongCount s=frameStrongCount s := by cases s <;> rfl
lemma optionalRestrictedCount_eq_frame (s : Option StrongRun) :
    optionalRestrictedCount s=frameRestrictedCount s := by cases s <;> rfl

/-- Every compiled path satisfies the source exponent bound.  An absent carry
run is handled by the ordinary operator or identity bound, not by a positive-
length spectral-block assertion. -/
theorem PathCode.path_le (q : PathCode) (x y : State → ℝ) :
    x ⬝ᵥ (q.matrix *ᵥ y) ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
        (strongBound^q.strongCount*sigma^q.restrictedCount*lam^q.carryCount) := by
  cases q with
  | pure s =>
    cases s with
    | none => simpa [PathCode.matrix,optionalStrongMatrix,PathCode.strongCount,
        PathCode.restrictedCount,PathCode.carryCount,optionalStrongCount,optionalRestrictedCount]
        using identity_path_le x y
    | some s => simpa [PathCode.matrix,optionalStrongMatrix,PathCode.strongCount,
        PathCode.restrictedCount,PathCode.carryCount,optionalStrongCount,optionalRestrictedCount,
        StrongRun.bound_eq,mul_assoc] using s.path_le x y
  | carried pre n hn bs post =>
    have hh:=optional_frame_path_le pre post n hn bs x y
    rw [optional_frame_bounds_product] at hh
    simpa only [PathCode.matrix,optionalStrongMatrix_eq_frame,PathCode.strongCount,
      PathCode.restrictedCount,PathCode.carryCount,optionalStrongCount_eq_frame,
      optionalRestrictedCount_eq_frame,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

end SubmittedGenus.CapFourMass.ActualComponent
