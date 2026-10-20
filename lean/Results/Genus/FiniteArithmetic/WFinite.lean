import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk00
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk01
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk02
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk03
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk04
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk05
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk06
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk07
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk08
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk09
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk10
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk11
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk12
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk13
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk14
import Results.Genus.FiniteArithmetic.WLookupChunks.Chunk15

namespace SubmittedGenus.FiniteArithmetic
open PowerSeries WLookupCertificate

theorem wLookup500_valid : Sparse.LookupValidPrefix wNumeratorTerms wDenominatorTail wLookup500 500 := by
  intro n
  have hn := n.isLt
  by_cases h0 : n.val < 32
  · exact checkedRange_apply recurrence_00 (by omega) h0
  by_cases h1 : n.val < 64
  · exact checkedRange_apply recurrence_01 (by omega) h1
  by_cases h2 : n.val < 96
  · exact checkedRange_apply recurrence_02 (by omega) h2
  by_cases h3 : n.val < 128
  · exact checkedRange_apply recurrence_03 (by omega) h3
  by_cases h4 : n.val < 160
  · exact checkedRange_apply recurrence_04 (by omega) h4
  by_cases h5 : n.val < 192
  · exact checkedRange_apply recurrence_05 (by omega) h5
  by_cases h6 : n.val < 224
  · exact checkedRange_apply recurrence_06 (by omega) h6
  by_cases h7 : n.val < 256
  · exact checkedRange_apply recurrence_07 (by omega) h7
  by_cases h8 : n.val < 288
  · exact checkedRange_apply recurrence_08 (by omega) h8
  by_cases h9 : n.val < 320
  · exact checkedRange_apply recurrence_09 (by omega) h9
  by_cases h10 : n.val < 352
  · exact checkedRange_apply recurrence_10 (by omega) h10
  by_cases h11 : n.val < 384
  · exact checkedRange_apply recurrence_11 (by omega) h11
  by_cases h12 : n.val < 416
  · exact checkedRange_apply recurrence_12 (by omega) h12
  by_cases h13 : n.val < 448
  · exact checkedRange_apply recurrence_13 (by omega) h13
  by_cases h14 : n.val < 480
  · exact checkedRange_apply recurrence_14 (by omega) h14
  exact checkedRange_apply recurrence_15 (by omega) (by omega)

theorem wLookup500_source_correct (n : ℕ) (hn : n < 500) :
    wLookup500 n = coeff n capacityW :=
  Sparse.lookupValidPrefix_source _ _ _ _ wDenominatorTail_positive wLookup500_valid _ capacityW_sparse_identity n hn

theorem original_W_weak_finite (n : ℕ) (hn : n ≤ 499) :
    25 * coeff n capacityW ≤ 13 * (Nat.fib n : ℤ) := by
  rw [← wLookup500_source_correct n (by omega), ← Nat.fastFib_eq]
  by_cases h0 : n < 32
  · exact weakRange_apply weak_00 (by omega) h0
  by_cases h1 : n < 64
  · exact weakRange_apply weak_01 (by omega) h1
  by_cases h2 : n < 96
  · exact weakRange_apply weak_02 (by omega) h2
  by_cases h3 : n < 128
  · exact weakRange_apply weak_03 (by omega) h3
  by_cases h4 : n < 160
  · exact weakRange_apply weak_04 (by omega) h4
  by_cases h5 : n < 192
  · exact weakRange_apply weak_05 (by omega) h5
  by_cases h6 : n < 224
  · exact weakRange_apply weak_06 (by omega) h6
  by_cases h7 : n < 256
  · exact weakRange_apply weak_07 (by omega) h7
  by_cases h8 : n < 288
  · exact weakRange_apply weak_08 (by omega) h8
  by_cases h9 : n < 320
  · exact weakRange_apply weak_09 (by omega) h9
  by_cases h10 : n < 352
  · exact weakRange_apply weak_10 (by omega) h10
  by_cases h11 : n < 384
  · exact weakRange_apply weak_11 (by omega) h11
  by_cases h12 : n < 416
  · exact weakRange_apply weak_12 (by omega) h12
  by_cases h13 : n < 448
  · exact weakRange_apply weak_13 (by omega) h13
  by_cases h14 : n < 480
  · exact weakRange_apply weak_14 (by omega) h14
  exact weakRange_apply weak_15 (by omega) (by omega)

theorem original_W_sharp_finite (n : ℕ) (hlo : 141 ≤ n) (hn : n ≤ 499) :
    1000 * coeff n capacityW ≤ 13 * (Nat.fib n : ℤ) := by
  rw [← wLookup500_source_correct n (by omega), ← Nat.fastFib_eq]
  by_cases h0 : n < 32
  · exact sharpRange_apply sharp_00 (by omega) h0 hlo
  by_cases h1 : n < 64
  · exact sharpRange_apply sharp_01 (by omega) h1 hlo
  by_cases h2 : n < 96
  · exact sharpRange_apply sharp_02 (by omega) h2 hlo
  by_cases h3 : n < 128
  · exact sharpRange_apply sharp_03 (by omega) h3 hlo
  by_cases h4 : n < 160
  · exact sharpRange_apply sharp_04 (by omega) h4 hlo
  by_cases h5 : n < 192
  · exact sharpRange_apply sharp_05 (by omega) h5 hlo
  by_cases h6 : n < 224
  · exact sharpRange_apply sharp_06 (by omega) h6 hlo
  by_cases h7 : n < 256
  · exact sharpRange_apply sharp_07 (by omega) h7 hlo
  by_cases h8 : n < 288
  · exact sharpRange_apply sharp_08 (by omega) h8 hlo
  by_cases h9 : n < 320
  · exact sharpRange_apply sharp_09 (by omega) h9 hlo
  by_cases h10 : n < 352
  · exact sharpRange_apply sharp_10 (by omega) h10 hlo
  by_cases h11 : n < 384
  · exact sharpRange_apply sharp_11 (by omega) h11 hlo
  by_cases h12 : n < 416
  · exact sharpRange_apply sharp_12 (by omega) h12 hlo
  by_cases h13 : n < 448
  · exact sharpRange_apply sharp_13 (by omega) h13 hlo
  by_cases h14 : n < 480
  · exact sharpRange_apply sharp_14 (by omega) h14 hlo
  exact sharpRange_apply sharp_15 (by omega) (by omega) hlo

#print axioms wLookup500_valid
#print axioms wLookup500_source_correct
#print axioms original_W_weak_finite
#print axioms original_W_sharp_finite
end SubmittedGenus.FiniteArithmetic
