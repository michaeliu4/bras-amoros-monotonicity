import Results.Genus.Injection.ReservoirSources.DecoratedOccurrences
import Results.Genus.FiniteArithmetic.Reservoir.CandidateSeries

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries OriginalReservoir
noncomputable section

def safeMarkedDen (t : PowerSeries ℤ) : PowerSeries ℤ := (1-v)*(1-v*t)*(1-v*t^2)
def safeMarkedNum (t : PowerSeries ℤ) : PowerSeries ℤ :=
  X^3*(1+u)*(1-v*t)*(1-v*t^2)+X^6*u*(1+u)*t*(1-v*t^2)+X^6*t*(1+s*t)*(1-v)
def earlyMarkedDen (t : PowerSeries ℤ) : PowerSeries ℤ :=
  (1-u)*(1-u^2)*(1-u*t)*(1-u^2*t)*(1-u^2*t^2)
def earlyMarkedNum (t : PowerSeries ℤ) : PowerSeries ℤ :=
  X^6*(1-u*t)*(1-u^2*t)*(1-u^2*t^2)+X^9*t*(1-u^2*t)*(1-u^2*t^2)+
  X^9*u*t^2*(1-u)*(1-u^2*t^2)+X^9*u*t^4*(1-u)*(1-u^2)
def awDen : PowerSeries ℤ := 1-2*X^3-X^4
def awNum : PowerSeries ℤ := 1+X^2

theorem safe_marked_rational (D : Decoration) :
    safeMarkedDen D.series*markedPrefixSeries safeFamily D.series=safeMarkedNum D.series := by
  rw [←safeMarkedSeries_eq_physical]
  exact safeMarkedSeries_identity D

theorem early_marked_rational (D : Decoration) :
    earlyMarkedDen D.series*markedPrefixSeries earlyFamily D.series=earlyMarkedNum D.series := by
  rw [←earlyMarkedSeries_eq_physical]
  exact earlyMarkedSeries_identity D

def failureDen (Q1 Qc : PowerSeries ℤ) : PowerSeries ℤ := (1-c)*Q1*Qc*awDen
def failureNum (P1 Q1 Pc Qc : PowerSeries ℤ) : PowerSeries ℤ :=
  X*(P1*Qc*awDen-Pc*Q1*awDen)+(1-c)*X*awNum*Pc*Q1

/-- Generic clearing of the actual failure-operator identity. Each marked
numerator/denominator identity is a semantic theorem, not certificate data. -/
theorem failure_rational {C : Type} (F : PrefixFamily C)
    {P1 Q1 Pc Qc : PowerSeries ℤ}
    (h1 : Q1*markedPrefixSeries F 1=P1) (hc : Qc*markedPrefixSeries F c=Pc) :
    failureDen Q1 Qc*actualFailureSeries F=failureNum P1 Q1 Pc Qc := by
  have ha : awDen*failureBlockSeries=awNum := failureBlockSeries_identity
  unfold failureDen failureNum
  calc
    _ = Q1*Qc*awDen*((1-c)*actualFailureSeries F) := by ring
    _ = X*((Q1*markedPrefixSeries F 1)*Qc*awDen-
      (Qc*markedPrefixSeries F c)*Q1*awDen)+
      (1-c)*X*(awDen*failureBlockSeries)*(Qc*markedPrefixSeries F c)*Q1 := by
      rw [failure_operator_identity]; ring
    _ = _ := by rw [h1,hc,ha]

def safeFailureDen : PowerSeries ℤ := failureDen (safeMarkedDen 1) (safeMarkedDen c)
def safeFailureNum : PowerSeries ℤ := failureNum (safeMarkedNum 1) (safeMarkedDen 1)
  (safeMarkedNum c) (safeMarkedDen c)
def earlyFailureDen : PowerSeries ℤ := failureDen (earlyMarkedDen 1) (earlyMarkedDen c)
def earlyFailureNum : PowerSeries ℤ := failureNum (earlyMarkedNum 1) (earlyMarkedDen 1)
  (earlyMarkedNum c) (earlyMarkedDen c)

theorem safe_failure_rational_identity :
    safeFailureDen*actualFailureSeries safeFamily=safeFailureNum := by
  apply failure_rational safeFamily
  · simpa only [unitDecoration_series] using safe_marked_rational unitDecoration
  · simpa only [binaryDecoration_series] using safe_marked_rational binaryDecoration

theorem early_failure_rational_identity :
    earlyFailureDen*actualFailureSeries earlyFamily=earlyFailureNum := by
  apply failure_rational earlyFamily
  · simpa only [unitDecoration_series] using early_marked_rational unitDecoration
  · simpa only [binaryDecoration_series] using early_marked_rational binaryDecoration

theorem safe_candidate_rational_identity :
    ((1-v)*(1-c))*safeCandidateSeries=X^4*(1+u) := by
  calc
    _ = (1-v)*((1-c)*safeCandidateSeries) := by ring
    _ = X*((1-v)*safeSeries) := by rw [safeCandidateSeries_identity]; ring
    _ = _ := by rw [safeSeries_identity]; ring

theorem early_candidate_rational_identity :
    ((1-u)*(1-u^2)*(1-c))*earlyCandidateSeries=X^7 := by
  calc
    _ = ((1-u)*(1-u^2))*((1-c)*earlyCandidateSeries) := by ring
    _ = X*(((1-u)*(1-u^2))*earlySeries) := by rw [earlyCandidateSeries_identity]; ring
    _ = _ := by rw [earlySeries_identity]; ring

#print axioms safe_failure_rational_identity
#print axioms early_failure_rational_identity
end
end SubmittedGenus.FiniteArithmetic.Reservoir
