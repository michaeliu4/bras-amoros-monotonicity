import Results.Genus.FiniteArithmetic.BoundedReflection
import Results.Genus.FiniteArithmetic.UnboundedTail

namespace SubmittedGenus.FiniteArithmetic

open PowerSeries
open Reflection

/-- For q=6,7,8, store the actual reflection blocks, with the pivot weight q. -/
abbrev FixedPivotSource (q : ℕ) := Graded.Shift q
  (Graded.Product (Reflection.Blocks (boundedSystem q q))
    (Reflection.Blocks (boundedSystem (q - 1) (q - 1))))

noncomputable def fixedPivotSeries (q : ℕ) : PowerSeries ℤ := Graded.series (FixedPivotSource q)

theorem fixedPivotSeries_identity (q : ℕ) :
    fixedPivotSeries q = (X : PowerSeries ℤ)^q *
      (capacityFactor q * capacityFactor (q - 1)) := by
  unfold fixedPivotSeries FixedPivotSource
  rw [Graded.shift_series, Graded.product_series]
  rfl

/-- Complete original M majorant source: three finite pivots plus every q≥9. -/
abbrev MSource := Graded.Sum (FixedPivotSource 6)
  (Graded.Sum (FixedPivotSource 7) (Graded.Sum (FixedPivotSource 8) OriginalTail.TailSource))

noncomputable def capacityM : PowerSeries ℤ := Graded.series MSource

@[simp] theorem capacityM_source_coeff (n : ℕ) :
    coeff n capacityM = (Fintype.card (MSource n) : ℤ) := by simp [capacityM]

/-- This is the original displayed M decomposition. The tail's cleared
rational identity is `OriginalTail.capacityMTail_source_identity`. -/
theorem capacityM_source_identity :
    capacityM = (X : PowerSeries ℤ)^6 * capacityFactor 6 * capacityFactor 5 +
      X^7 * capacityFactor 7 * capacityFactor 6 +
      X^8 * capacityFactor 8 * capacityFactor 7 + OriginalTail.capacityMTail := by
  unfold capacityM MSource
  rw [Graded.sum_series, Graded.sum_series, Graded.sum_series]
  change fixedPivotSeries 6 + (fixedPivotSeries 7 +
    (fixedPivotSeries 8 + OriginalTail.capacityMTail)) = _
  rw [fixedPivotSeries_identity, fixedPivotSeries_identity, fixedPivotSeries_identity]
  norm_num
  ring

#print axioms capacityM_source_coeff
#print axioms capacityM_source_identity

end SubmittedGenus.FiniteArithmetic
