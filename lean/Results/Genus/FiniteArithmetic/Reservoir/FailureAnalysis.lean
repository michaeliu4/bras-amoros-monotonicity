import Results.Genus.FiniteArithmetic.Reservoir.TransformAnalysis
import Results.Genus.FiniteArithmetic.Reservoir.FailureOperator
import Results.Genus.FiniteArithmetic.Reservoir.RadiusErrors

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries Analytic
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def failureValue (d : ℕ) : ℝ := (∑ i : Fin d,cValueAt^i.val)+cValueAt^d*failureBlockValue

theorem failureTail_evaluates (d : ℕ) : PositiveEval radius (failureTailSeries d) (failureValue d) := by
  rw [failureTailSeries_identity]
  exact (positiveEval_sum radius radius_nonneg Finset.univ (fun i : Fin d=>c^i.val)
    (fun i=>cValueAt^i.val) (fun i _=>c_evaluates.pow radius_nonneg i.val)).add radius_nonneg
      ((c_evaluates.pow radius_nonneg d).mul radius_nonneg failureBlock_evaluates)

def failureDomination : ℝ := 1/(cValueAt-1)+failureBlockValue

theorem failureDomination_nonneg : 0≤failureDomination := by
  norm_num [failureDomination,failureBlockValue,cValueAt,radius]

theorem failureValue_le (d : ℕ) : failureValue d≤failureDomination*cValueAt^d := by
  have hc : 0<cValueAt-1 := by norm_num [cValueAt,radius]
  have hg : (∑ i∈Finset.range d,cValueAt^i)*(cValueAt-1)=cValueAt^d-1 := by
    induction d with
    | zero => simp
    | succ d ih => rw [Finset.sum_range_succ,add_mul,ih,pow_succ]; ring
  have hsum : (∑ i:Fin d,cValueAt^i.val)≤cValueAt^d/(cValueAt-1) := by
    rw [Fin.sum_univ_eq_sum_range]
    apply (le_div_iff₀ hc).mpr
    linarith
  calc
    failureValue d ≤ cValueAt^d/(cValueAt-1)+cValueAt^d*failureBlockValue :=
      by unfold failureValue; exact add_le_add hsum (le_refl _)
    _ = failureDomination*cValueAt^d := by unfold failureDomination; ring

/-- Actual failed-mark convergence at 5/8 follows from the decorated physical
marked source. The proof uses positive domination, never a divergent
geometric expansion at c(5/8)>1. -/
theorem actualFailure_summable {C : Type} (F : OriginalReservoir.PrefixFamily C)
    (hmark : SummableAt radius (markedPrefixSeries F c)) :
    SummableAt radius (actualFailureSeries F) := by
  let K (n : ℕ) := ∑ p : OriginalReservoir.PrefixOccurrence F n,failureTailSeries p.distance
  let L (n : ℕ) := ∑ p : OriginalReservoir.PrefixOccurrence F n,c^p.distance
  have hK (n : ℕ) : PositiveEval radius (K n)
      (∑ p : OriginalReservoir.PrefixOccurrence F n,failureValue p.distance) :=
    positiveEval_sum radius radius_nonneg Finset.univ _ _ (fun p _=>failureTail_evaluates p.distance)
  have hL (n : ℕ) : PositiveEval radius (L n)
      (∑ p : OriginalReservoir.PrefixOccurrence F n,cValueAt^p.distance) :=
    positiveEval_sum radius radius_nonneg Finset.univ _ _ (fun p _=>c_evaluates.pow radius_nonneg p.distance)
  have hrow (n : ℕ) : massAt radius (K n)≤failureDomination*massAt radius (L n) := by
    rw [(hK n).value,(hL n).value,Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _=>failureValue_le p.distance)
  have ht := transform_summable_of_row_domination radius_nonneg failureDomination_nonneg
    (fun n=>(hK n).nonnegative) (fun n=>(hL n).nonnegative)
    (fun n=>(hK n).summable) hrow hmark
  rw [actualFailureSeries_transform]
  exact (mul_bound radius_nonneg (by simpa using xpow_bound radius 1)
    ⟨ht,le_refl (normAt radius (gradedTransform K))⟩).1

#print axioms actualFailure_summable
end
end SubmittedGenus.FiniteArithmetic.Reservoir
