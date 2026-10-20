import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk00
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk01
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk02
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk03
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk04
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk05
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk06
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk07
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk08
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk09
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk10
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk11
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk12
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk13
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk14
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk15
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk16
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk17
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk18
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk19
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk20
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk21
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk22
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk23
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk24
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk25
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk26
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk27
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk28
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk29
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk30
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk31
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk32
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk33
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk34
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk35
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk36
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk37
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk38
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk39
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk40
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk41
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk42
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk43
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk44
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk45
import Results.Genus.FiniteArithmetic.Reservoir.FiniteChunks.Chunk46
import Results.Genus.FiniteArithmetic.Reservoir.NonbinaryTail
import Results.Genus.Injection.ReservoirSources.CoefficientCapacity
namespace SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
open PowerSeries OriginalReservoir

theorem all_rows (n : ℕ) (hn : n<1500) : Row n := by
  by_cases h0 : n<32
  · exact checkedRange_apply recurrence_00 (by omega) h0
  by_cases h1 : n<64
  · exact checkedRange_apply recurrence_01 (by omega) h1
  by_cases h2 : n<96
  · exact checkedRange_apply recurrence_02 (by omega) h2
  by_cases h3 : n<128
  · exact checkedRange_apply recurrence_03 (by omega) h3
  by_cases h4 : n<160
  · exact checkedRange_apply recurrence_04 (by omega) h4
  by_cases h5 : n<192
  · exact checkedRange_apply recurrence_05 (by omega) h5
  by_cases h6 : n<224
  · exact checkedRange_apply recurrence_06 (by omega) h6
  by_cases h7 : n<256
  · exact checkedRange_apply recurrence_07 (by omega) h7
  by_cases h8 : n<288
  · exact checkedRange_apply recurrence_08 (by omega) h8
  by_cases h9 : n<320
  · exact checkedRange_apply recurrence_09 (by omega) h9
  by_cases h10 : n<352
  · exact checkedRange_apply recurrence_10 (by omega) h10
  by_cases h11 : n<384
  · exact checkedRange_apply recurrence_11 (by omega) h11
  by_cases h12 : n<416
  · exact checkedRange_apply recurrence_12 (by omega) h12
  by_cases h13 : n<448
  · exact checkedRange_apply recurrence_13 (by omega) h13
  by_cases h14 : n<480
  · exact checkedRange_apply recurrence_14 (by omega) h14
  by_cases h15 : n<512
  · exact checkedRange_apply recurrence_15 (by omega) h15
  by_cases h16 : n<544
  · exact checkedRange_apply recurrence_16 (by omega) h16
  by_cases h17 : n<576
  · exact checkedRange_apply recurrence_17 (by omega) h17
  by_cases h18 : n<608
  · exact checkedRange_apply recurrence_18 (by omega) h18
  by_cases h19 : n<640
  · exact checkedRange_apply recurrence_19 (by omega) h19
  by_cases h20 : n<672
  · exact checkedRange_apply recurrence_20 (by omega) h20
  by_cases h21 : n<704
  · exact checkedRange_apply recurrence_21 (by omega) h21
  by_cases h22 : n<736
  · exact checkedRange_apply recurrence_22 (by omega) h22
  by_cases h23 : n<768
  · exact checkedRange_apply recurrence_23 (by omega) h23
  by_cases h24 : n<800
  · exact checkedRange_apply recurrence_24 (by omega) h24
  by_cases h25 : n<832
  · exact checkedRange_apply recurrence_25 (by omega) h25
  by_cases h26 : n<864
  · exact checkedRange_apply recurrence_26 (by omega) h26
  by_cases h27 : n<896
  · exact checkedRange_apply recurrence_27 (by omega) h27
  by_cases h28 : n<928
  · exact checkedRange_apply recurrence_28 (by omega) h28
  by_cases h29 : n<960
  · exact checkedRange_apply recurrence_29 (by omega) h29
  by_cases h30 : n<992
  · exact checkedRange_apply recurrence_30 (by omega) h30
  by_cases h31 : n<1024
  · exact checkedRange_apply recurrence_31 (by omega) h31
  by_cases h32 : n<1056
  · exact checkedRange_apply recurrence_32 (by omega) h32
  by_cases h33 : n<1088
  · exact checkedRange_apply recurrence_33 (by omega) h33
  by_cases h34 : n<1120
  · exact checkedRange_apply recurrence_34 (by omega) h34
  by_cases h35 : n<1152
  · exact checkedRange_apply recurrence_35 (by omega) h35
  by_cases h36 : n<1184
  · exact checkedRange_apply recurrence_36 (by omega) h36
  by_cases h37 : n<1216
  · exact checkedRange_apply recurrence_37 (by omega) h37
  by_cases h38 : n<1248
  · exact checkedRange_apply recurrence_38 (by omega) h38
  by_cases h39 : n<1280
  · exact checkedRange_apply recurrence_39 (by omega) h39
  by_cases h40 : n<1312
  · exact checkedRange_apply recurrence_40 (by omega) h40
  by_cases h41 : n<1344
  · exact checkedRange_apply recurrence_41 (by omega) h41
  by_cases h42 : n<1376
  · exact checkedRange_apply recurrence_42 (by omega) h42
  by_cases h43 : n<1408
  · exact checkedRange_apply recurrence_43 (by omega) h43
  by_cases h44 : n<1440
  · exact checkedRange_apply recurrence_44 (by omega) h44
  by_cases h45 : n<1472
  · exact checkedRange_apply recurrence_45 (by omega) h45
  exact checkedRange_apply recurrence_46 (by omega) (by omega)
theorem ts_source_correct (n : ℕ) (hn : n<1500) : tsLookup n=coeff n (safeCandidateSeries) := by
  apply Sparse.lookupValidPrefix_source tsNumerator tsDenominatorTail tsLookup 1500 ts_denominator_positive
    (fun i=>(all_rows i.val i.isLt).1) _ ts_sparse_identity n hn
theorem te_source_correct (n : ℕ) (hn : n<1500) : teLookup n=coeff n (earlyCandidateSeries) := by
  apply Sparse.lookupValidPrefix_source teNumerator teDenominatorTail teLookup 1500 te_denominator_positive
    (fun i=>(all_rows i.val i.isLt).2.1) _ te_sparse_identity n hn
theorem us_source_correct (n : ℕ) (hn : n<1500) : usLookup n=coeff n (actualFailureSeries safeFamily) := by
  apply Sparse.lookupValidPrefix_source usNumerator usDenominatorTail usLookup 1500 us_denominator_positive
    (fun i=>(all_rows i.val i.isLt).2.2.1) _ us_sparse_identity n hn
theorem ue_source_correct (n : ℕ) (hn : n<1500) : ueLookup n=coeff n (actualFailureSeries earlyFamily) := by
  apply Sparse.lookupValidPrefix_source ueNumerator ueDenominatorTail ueLookup 1500 ue_denominator_positive
    (fun i=>(all_rows i.val i.isLt).2.2.2) _ ue_sparse_identity n hn
theorem all_lower (n : ℕ) (hn : n<1500) (hlo : 305≤n) :
    927*(Nat.fastFib n:ℤ) ≤ 500*(max 0 (tsLookup n-usLookup n)+max 0 (teLookup n-ueLookup n)) := by
  by_cases h0 : n<32
  · exact lowerRange_apply lower_00 (by omega) h0 hlo
  by_cases h1 : n<64
  · exact lowerRange_apply lower_01 (by omega) h1 hlo
  by_cases h2 : n<96
  · exact lowerRange_apply lower_02 (by omega) h2 hlo
  by_cases h3 : n<128
  · exact lowerRange_apply lower_03 (by omega) h3 hlo
  by_cases h4 : n<160
  · exact lowerRange_apply lower_04 (by omega) h4 hlo
  by_cases h5 : n<192
  · exact lowerRange_apply lower_05 (by omega) h5 hlo
  by_cases h6 : n<224
  · exact lowerRange_apply lower_06 (by omega) h6 hlo
  by_cases h7 : n<256
  · exact lowerRange_apply lower_07 (by omega) h7 hlo
  by_cases h8 : n<288
  · exact lowerRange_apply lower_08 (by omega) h8 hlo
  by_cases h9 : n<320
  · exact lowerRange_apply lower_09 (by omega) h9 hlo
  by_cases h10 : n<352
  · exact lowerRange_apply lower_10 (by omega) h10 hlo
  by_cases h11 : n<384
  · exact lowerRange_apply lower_11 (by omega) h11 hlo
  by_cases h12 : n<416
  · exact lowerRange_apply lower_12 (by omega) h12 hlo
  by_cases h13 : n<448
  · exact lowerRange_apply lower_13 (by omega) h13 hlo
  by_cases h14 : n<480
  · exact lowerRange_apply lower_14 (by omega) h14 hlo
  by_cases h15 : n<512
  · exact lowerRange_apply lower_15 (by omega) h15 hlo
  by_cases h16 : n<544
  · exact lowerRange_apply lower_16 (by omega) h16 hlo
  by_cases h17 : n<576
  · exact lowerRange_apply lower_17 (by omega) h17 hlo
  by_cases h18 : n<608
  · exact lowerRange_apply lower_18 (by omega) h18 hlo
  by_cases h19 : n<640
  · exact lowerRange_apply lower_19 (by omega) h19 hlo
  by_cases h20 : n<672
  · exact lowerRange_apply lower_20 (by omega) h20 hlo
  by_cases h21 : n<704
  · exact lowerRange_apply lower_21 (by omega) h21 hlo
  by_cases h22 : n<736
  · exact lowerRange_apply lower_22 (by omega) h22 hlo
  by_cases h23 : n<768
  · exact lowerRange_apply lower_23 (by omega) h23 hlo
  by_cases h24 : n<800
  · exact lowerRange_apply lower_24 (by omega) h24 hlo
  by_cases h25 : n<832
  · exact lowerRange_apply lower_25 (by omega) h25 hlo
  by_cases h26 : n<864
  · exact lowerRange_apply lower_26 (by omega) h26 hlo
  by_cases h27 : n<896
  · exact lowerRange_apply lower_27 (by omega) h27 hlo
  by_cases h28 : n<928
  · exact lowerRange_apply lower_28 (by omega) h28 hlo
  by_cases h29 : n<960
  · exact lowerRange_apply lower_29 (by omega) h29 hlo
  by_cases h30 : n<992
  · exact lowerRange_apply lower_30 (by omega) h30 hlo
  by_cases h31 : n<1024
  · exact lowerRange_apply lower_31 (by omega) h31 hlo
  by_cases h32 : n<1056
  · exact lowerRange_apply lower_32 (by omega) h32 hlo
  by_cases h33 : n<1088
  · exact lowerRange_apply lower_33 (by omega) h33 hlo
  by_cases h34 : n<1120
  · exact lowerRange_apply lower_34 (by omega) h34 hlo
  by_cases h35 : n<1152
  · exact lowerRange_apply lower_35 (by omega) h35 hlo
  by_cases h36 : n<1184
  · exact lowerRange_apply lower_36 (by omega) h36 hlo
  by_cases h37 : n<1216
  · exact lowerRange_apply lower_37 (by omega) h37 hlo
  by_cases h38 : n<1248
  · exact lowerRange_apply lower_38 (by omega) h38 hlo
  by_cases h39 : n<1280
  · exact lowerRange_apply lower_39 (by omega) h39 hlo
  by_cases h40 : n<1312
  · exact lowerRange_apply lower_40 (by omega) h40 hlo
  by_cases h41 : n<1344
  · exact lowerRange_apply lower_41 (by omega) h41 hlo
  by_cases h42 : n<1376
  · exact lowerRange_apply lower_42 (by omega) h42 hlo
  by_cases h43 : n<1408
  · exact lowerRange_apply lower_43 (by omega) h43 hlo
  by_cases h44 : n<1440
  · exact lowerRange_apply lower_44 (by omega) h44 hlo
  by_cases h45 : n<1472
  · exact lowerRange_apply lower_45 (by omega) h45 hlo
  exact lowerRange_apply lower_46 (by omega) (by omega) hlo
theorem original_nonbinary_finite (g : ℕ) (hlo : 305≤g) (hhi : g≤1499) :
    927*Nat.fib g ≤ 500*nonbinaryLowerBound g := by
  have hg : g<1500 := by omega
  have h := all_lower g hg hlo
  rw [Nat.fastFib_eq,ts_source_correct g hg,te_source_correct g hg,
    us_source_correct g hg,ue_source_correct g hg] at h
  have he : (nonbinaryLowerBound g:ℤ)=
      max 0 (coeff g safeCandidateSeries-coeff g (actualFailureSeries safeFamily))+
      max 0 (coeff g earlyCandidateSeries-coeff g (actualFailureSeries earlyFamily)) := by
    simpa only [coefficientNonbinaryLowerBound,map_sub] using nonbinaryLowerBound_eq_coefficient_clip g
  rw [←he] at h
  exact_mod_cast h

end SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
namespace SubmittedGenus.FiniteArithmetic.Reservoir
open OriginalReservoir
/-- Original submitted nonbinary capacity for every genus at least305,
combining all accepted finite source recurrences with the proved analytic tail. -/
theorem original_nonbinary_all (g : ℕ) (hg : 305≤g) :
    927*Nat.fib g ≤ 500*nonbinaryLowerBound g := by
  by_cases h : g<1500
  · exact Certificate1500.original_nonbinary_finite g hg (by omega)
  · exact original_nonbinary_tail g (by omega)
#print axioms Certificate1500.ts_source_correct
#print axioms Certificate1500.te_source_correct
#print axioms Certificate1500.us_source_correct
#print axioms Certificate1500.ue_source_correct
#print axioms Certificate1500.original_nonbinary_finite
#print axioms original_nonbinary_all
end SubmittedGenus.FiniteArithmetic.Reservoir
