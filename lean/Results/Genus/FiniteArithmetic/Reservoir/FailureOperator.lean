import Results.Genus.FiniteArithmetic.Reservoir.GradedTransform
import Results.Genus.Injection.ReservoirSources.MarkedFailures

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Physical marked-prefix series, with one formal t per unit of physical
distance. All outer sums are coefficientwise finite. -/
def markedPrefixSeries {C : Type} (F : OriginalReservoir.PrefixFamily C)
    (t : PowerSeries ℤ) : PowerSeries ℤ :=
  gradedTransform (fun n => ∑ p : OriginalReservoir.PrefixOccurrence F n, t^p.distance)

def actualFailureSeries {C : Type} (F : OriginalReservoir.PrefixFamily C) : PowerSeries ℤ :=
  Graded.series (OriginalReservoir.FailedMark F)

theorem actualFailureSeries_coeff {C : Type} (F : OriginalReservoir.PrefixFamily C) (g : ℕ) :
    coeff g (actualFailureSeries F) = (Fintype.card (OriginalReservoir.FailedMark F g) : ℤ) :=
  Graded.coeff_series _ _

theorem markedPrefixSeries_one {C : Type} (F : OriginalReservoir.PrefixFamily C) :
    markedPrefixSeries F 1 = Graded.series (OriginalReservoir.PrefixOccurrence F) := by
  simp only [markedPrefixSeries,one_pow]
  exact gradedTransform_one _

theorem actualFailureSeries_transform {C : Type} (F : OriginalReservoir.PrefixFamily C) :
    actualFailureSeries F = X*gradedTransform
      (fun n => ∑ p : OriginalReservoir.PrefixOccurrence F n, failureTailSeries p.distance) := by
  apply PowerSeries.ext
  intro g
  rw [actualFailureSeries_coeff,OriginalReservoir.failedMark_coeff_convolution]
  cases g with
  | zero => simp
  | succ g =>
    rw [show (X : PowerSeries ℤ) = X^1 by simp,coeff_X_pow_mul',if_pos (by omega)]
    rw [gradedTransform_coeff]
    simp only [Nat.succ_sub_one]
    apply Finset.sum_congr rfl
    intro n _
    rw [map_sum]

theorem failureTailSeries_clear (d : ℕ) :
    failureTailSeries d*(1-c) = 1-c^d+c^d*failureBlockSeries*(1-c) := by
  have hg : (∑ i ∈ Finset.range d, c^i)*(1-c)=1-c^d := by
    induction d with
    | zero => simp
    | succ d ih => rw [Finset.sum_range_succ,add_mul,ih,pow_succ]; ring
  rw [failureTailSeries_identity,Fin.sum_univ_eq_sum_range,add_mul,hg]

theorem failure_operator_identity {C : Type} (F : OriginalReservoir.PrefixFamily C) :
    (1-c)*actualFailureSeries F =
      X*(markedPrefixSeries F 1-markedPrefixSeries F c) +
        (1-c)*X*failureBlockSeries*markedPrefixSeries F c := by
  let K (n : ℕ) := ∑ p : OriginalReservoir.PrefixOccurrence F n, failureTailSeries p.distance
  let O (n : ℕ) := ∑ _p : OriginalReservoir.PrefixOccurrence F n, (1 : PowerSeries ℤ)
  let T (n : ℕ) := ∑ p : OriginalReservoir.PrefixOccurrence F n, c^p.distance
  have hn (n : ℕ) : K n*(1-c)=O n-T n+T n*failureBlockSeries*(1-c) := by
    dsimp [K,O,T]
    rw [Finset.sum_mul]
    simp_rw [failureTailSeries_clear]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.sum_mul]
  have ht : gradedTransform K*(1-c) = gradedTransform O-gradedTransform T+
      gradedTransform T*failureBlockSeries*(1-c) := by
    rw [←gradedTransform_mul]
    rw [gradedTransform_congr hn,gradedTransform_add,gradedTransform_sub,
      gradedTransform_mul,gradedTransform_mul]
  have ho : markedPrefixSeries F 1=gradedTransform O := by
    simp only [markedPrefixSeries,one_pow,O]
  rw [actualFailureSeries_transform,ho]
  change (1-c)*(X*gradedTransform K) =
    X*(gradedTransform O-gradedTransform T)+(1-c)*X*failureBlockSeries*gradedTransform T
  calc
    _ = X*(gradedTransform K*(1-c)) := by ring
    _ = _ := by rw [ht]; ring

#print axioms actualFailureSeries_transform
#print axioms failure_operator_identity
end
end SubmittedGenus.FiniteArithmetic.Reservoir
