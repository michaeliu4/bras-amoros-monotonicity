import Results.Genus.FiniteArithmetic.Reservoir.RationalIdentities
import Results.Genus.FiniteArithmetic.LookupSparse
namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries OriginalReservoir
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def tsNumerator : Sparse.Terms := [(4, 1), (6, 1), (7, 1)]
def tsDenominatorTail : Sparse.Terms := [(1, -1), (2, -1), (3, -1), (4, -1), (5, 1), (6, 3), (7, 3), (8, 1)]
def tsCancel : Sparse.Terms := [(0, 1)]
theorem ts_numerator_expansion : X^4*(1+u) = Sparse.series tsCancel*Sparse.series tsNumerator := by
  norm_num [Sparse.series, tsCancel, tsNumerator, safeFailureDen, earlyFailureDen, safeFailureNum, earlyFailureNum, failureDen, failureNum, safeMarkedDen, safeMarkedNum, earlyMarkedDen, earlyMarkedNum, awDen, awNum, u, s, c, v] <;> ring
 theorem ts_denominator_expansion : ((1-v)*(1-c)) = Sparse.series tsCancel*(1+Sparse.series tsDenominatorTail) := by
  norm_num [Sparse.series, tsCancel, tsDenominatorTail, safeFailureDen, earlyFailureDen, safeFailureNum, earlyFailureNum, failureDen, failureNum, safeMarkedDen, safeMarkedNum, earlyMarkedDen, earlyMarkedNum, awDen, awNum, u, s, c, v] <;> ring
 theorem ts_cancel_nonzero : Sparse.series tsCancel≠0 := by
  intro h
  have hh := congrArg constantCoeff h
  norm_num [Sparse.series,tsCancel] at hh
 theorem ts_denominator_positive : ∀ t∈tsDenominatorTail,0<t.1 := by decide
 theorem ts_sparse_identity : (1+Sparse.series tsDenominatorTail)*(safeCandidateSeries)=Sparse.series tsNumerator := by
  apply mul_left_cancel₀ ts_cancel_nonzero
  calc
    _ = ((1-v)*(1-c))*(safeCandidateSeries) := by rw [ts_denominator_expansion]; ring
    _ = X^4*(1+u) := safe_candidate_rational_identity
    _ = _ := ts_numerator_expansion
#print axioms ts_sparse_identity

def teNumerator : Sparse.Terms := [(7, 1)]
def teDenominatorTail : Sparse.Terms := [(1, -1), (2, -2), (4, 1), (6, 3), (7, 5), (9, -5), (10, -4), (11, -1)]
def teCancel : Sparse.Terms := [(0, 1)]
theorem te_numerator_expansion : X^7 = Sparse.series teCancel*Sparse.series teNumerator := by
  norm_num [Sparse.series, teCancel, teNumerator, safeFailureDen, earlyFailureDen, safeFailureNum, earlyFailureNum, failureDen, failureNum, safeMarkedDen, safeMarkedNum, earlyMarkedDen, earlyMarkedNum, awDen, awNum, u, s, c, v] <;> ring
 theorem te_denominator_expansion : ((1-u)*(1-u^2)*(1-c)) = Sparse.series teCancel*(1+Sparse.series teDenominatorTail) := by
  norm_num [Sparse.series, teCancel, teDenominatorTail, safeFailureDen, earlyFailureDen, safeFailureNum, earlyFailureNum, failureDen, failureNum, safeMarkedDen, safeMarkedNum, earlyMarkedDen, earlyMarkedNum, awDen, awNum, u, s, c, v] <;> ring
 theorem te_cancel_nonzero : Sparse.series teCancel≠0 := by
  intro h
  have hh := congrArg constantCoeff h
  norm_num [Sparse.series,teCancel] at hh
 theorem te_denominator_positive : ∀ t∈teDenominatorTail,0<t.1 := by decide
 theorem te_sparse_identity : (1+Sparse.series teDenominatorTail)*(earlyCandidateSeries)=Sparse.series teNumerator := by
  apply mul_left_cancel₀ te_cancel_nonzero
  calc
    _ = ((1-u)*(1-u^2)*(1-c))*(earlyCandidateSeries) := by rw [te_denominator_expansion]; ring
    _ = X^7 := early_candidate_rational_identity
    _ = _ := te_numerator_expansion
#print axioms te_sparse_identity

def usNumerator : Sparse.Terms := [(4, 1), (6, 2), (7, 1), (9, -3), (10, -11), (11, -20), (12, -30), (13, -33), (14, -21), (15, 13), (16, 78), (17, 163), (18, 238), (19, 264), (20, 212), (21, 73), (22, -139), (23, -384), (24, -594), (25, -695), (26, -652), (27, -495), (28, -300), (29, -140), (30, -47), (31, -10), (32, -1)]
def usDenominatorTail : Sparse.Terms := [(3, -4), (4, -6), (5, -8), (6, -5), (7, 8), (8, 33), (9, 69), (10, 100), (11, 95), (12, 12), (13, -175), (14, -449), (15, -723), (16, -830), (17, -558), (18, 242), (19, 1494), (20, 2782), (21, 3434), (22, 2861), (23, 978), (24, -1614), (25, -3892), (26, -4991), (27, -4691), (28, -3453), (29, -2017), (30, -925), (31, -323), (32, -81), (33, -13), (34, -1)]
def usCancel : Sparse.Terms := [(0, 1), (1, -1), (2, -1), (3, -2), (4, -2), (5, 2), (6, 7), (7, 9), (8, 5), (9, -2), (10, -10), (11, -14), (12, -11), (13, -5), (14, -1)]
theorem us_numerator_expansion : safeFailureNum = Sparse.series usCancel*Sparse.series usNumerator := by
  norm_num [Sparse.series, usCancel, usNumerator, safeFailureDen, earlyFailureDen, safeFailureNum, earlyFailureNum, failureDen, failureNum, safeMarkedDen, safeMarkedNum, earlyMarkedDen, earlyMarkedNum, awDen, awNum, u, s, c, v] <;> ring
 theorem us_denominator_expansion : safeFailureDen = Sparse.series usCancel*(1+Sparse.series usDenominatorTail) := by
  norm_num [Sparse.series, usCancel, usDenominatorTail, safeFailureDen, earlyFailureDen, safeFailureNum, earlyFailureNum, failureDen, failureNum, safeMarkedDen, safeMarkedNum, earlyMarkedDen, earlyMarkedNum, awDen, awNum, u, s, c, v] <;> ring
 theorem us_cancel_nonzero : Sparse.series usCancel≠0 := by
  intro h
  have hh := congrArg constantCoeff h
  norm_num [Sparse.series,usCancel] at hh
 theorem us_denominator_positive : ∀ t∈usDenominatorTail,0<t.1 := by decide
 theorem us_sparse_identity : (1+Sparse.series usDenominatorTail)*(actualFailureSeries safeFamily)=Sparse.series usNumerator := by
  apply mul_left_cancel₀ us_cancel_nonzero
  calc
    _ = safeFailureDen*(actualFailureSeries safeFamily) := by rw [us_denominator_expansion]; ring
    _ = safeFailureNum := safe_failure_rational_identity
    _ = _ := us_numerator_expansion
#print axioms us_sparse_identity

def ueNumerator : Sparse.Terms := [(7, 1), (9, 1), (11, -2), (12, -1), (13, -4), (14, -4), (15, -8), (16, -14), (17, -10), (18, -2), (19, 3), (20, 5), (21, 17), (22, 57), (23, 130), (24, 203), (25, 208), (26, 125), (27, 16), (28, -88), (29, -237), (30, -437), (31, -593), (32, -628), (33, -548), (34, -392), (35, -215), (36, -82), (37, -19), (38, -2)]
def ueDenominatorTail : Sparse.Terms := [(2, -1), (3, -4), (4, -5), (5, -3), (6, 4), (7, 15), (8, 29), (9, 38), (10, 34), (11, 5), (12, -63), (13, -166), (14, -275), (15, -331), (16, -238), (17, 87), (18, 630), (19, 1254), (20, 1715), (21, 1678), (22, 793), (23, -1094), (24, -3643), (25, -5858), (26, -6337), (27, -4003), (28, 1002), (29, 6913), (30, 10968), (31, 10907), (32, 6473), (33, -158), (34, -5630), (35, -7670), (36, -6458), (37, -3885), (38, -1713), (39, -545), (40, -119), (41, -16), (42, -1)]
def ueCancel : Sparse.Terms := [(0, 1), (1, -1), (2, -3), (4, 3), (5, 1), (6, 6), (7, 11), (8, -4), (9, -23), (10, -19), (11, -6), (12, 2), (13, 20), (14, 39), (15, 27), (16, -8), (17, -27), (18, -20), (19, -7), (20, -1)]
theorem ue_numerator_expansion : earlyFailureNum = Sparse.series ueCancel*Sparse.series ueNumerator := by
  norm_num [Sparse.series, ueCancel, ueNumerator, safeFailureDen, earlyFailureDen, safeFailureNum, earlyFailureNum, failureDen, failureNum, safeMarkedDen, safeMarkedNum, earlyMarkedDen, earlyMarkedNum, awDen, awNum, u, s, c, v] <;> ring
 theorem ue_denominator_expansion : earlyFailureDen = Sparse.series ueCancel*(1+Sparse.series ueDenominatorTail) := by
  norm_num [Sparse.series, ueCancel, ueDenominatorTail, safeFailureDen, earlyFailureDen, safeFailureNum, earlyFailureNum, failureDen, failureNum, safeMarkedDen, safeMarkedNum, earlyMarkedDen, earlyMarkedNum, awDen, awNum, u, s, c, v] <;> ring
 theorem ue_cancel_nonzero : Sparse.series ueCancel≠0 := by
  intro h
  have hh := congrArg constantCoeff h
  norm_num [Sparse.series,ueCancel] at hh
 theorem ue_denominator_positive : ∀ t∈ueDenominatorTail,0<t.1 := by decide
 theorem ue_sparse_identity : (1+Sparse.series ueDenominatorTail)*(actualFailureSeries earlyFamily)=Sparse.series ueNumerator := by
  apply mul_left_cancel₀ ue_cancel_nonzero
  calc
    _ = earlyFailureDen*(actualFailureSeries earlyFamily) := by rw [ue_denominator_expansion]; ring
    _ = earlyFailureNum := early_failure_rational_identity
    _ = _ := ue_numerator_expansion
#print axioms ue_sparse_identity
end SubmittedGenus.FiniteArithmetic.Reservoir
