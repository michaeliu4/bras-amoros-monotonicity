import Results.Genus.FiniteComparison.Chunks.Chunk00
import Results.Genus.FiniteComparison.Chunks.Chunk01
import Results.Genus.FiniteComparison.Chunks.Chunk02
import Results.Genus.FiniteComparison.Chunks.Chunk03
import Results.Genus.FiniteComparison.Chunks.Chunk04
import Results.Genus.FiniteComparison.Chunks.Chunk05
import Results.Genus.FiniteComparison.Chunks.Chunk06
import Results.Genus.FiniteComparison.Chunks.Chunk07
import Results.Genus.FiniteComparison.Chunks.Chunk08
import Results.Genus.FiniteComparison.Chunks.Chunk09
import Results.Genus.FiniteComparison.Chunks.Chunk10
import Results.Genus.FiniteComparison.Chunks.Chunk11
import Results.Genus.FiniteComparison.Chunks.Chunk12
import Results.Genus.FiniteComparison.Chunks.Chunk13
import Results.Genus.FiniteComparison.Chunks.Chunk14
import Results.Genus.FiniteComparison.Chunks.Chunk15
import Results.Genus.FiniteComparison.Chunks.Chunk16
import Results.Genus.FiniteComparison.Chunks.Chunk17
import Results.Genus.FiniteComparison.Chunks.Chunk18
import Results.Genus.FiniteComparison.Chunks.Chunk19
import Results.Genus.FiniteComparison.Chunks.Chunk20
import Results.Genus.FiniteComparison.Chunks.Chunk21
import Results.Genus.FiniteComparison.Chunks.Chunk22
import Results.Genus.FiniteComparison.Chunks.Chunk23
import Results.Genus.FiniteComparison.Chunks.Chunk24
import Results.Genus.FiniteComparison.Chunks.Chunk25
import Results.Genus.FiniteComparison.Chunks.Chunk26
import Results.Genus.FiniteComparison.Chunks.Chunk27
import Results.Genus.FiniteComparison.Chunks.Chunk28
import Results.Genus.FiniteComparison.Chunks.Chunk29
import Results.Genus.FiniteComparison.Chunks.Chunk30
import Results.Genus.FiniteComparison.Chunks.Chunk31
import Results.Genus.FiniteComparison.Chunks.Chunk32
import Results.Genus.FiniteComparison.Chunks.Chunk33
import Results.Genus.FiniteComparison.Chunks.Chunk34
import Results.Genus.FiniteComparison.Chunks.Chunk35
import Results.Genus.FiniteComparison.Chunks.Chunk36
import Results.Genus.FiniteComparison.Chunks.Chunk37
import Results.Genus.FiniteComparison.Chunks.Chunk38
import Results.Genus.FiniteComparison.Chunks.Chunk39
import Results.Genus.FiniteComparison.Chunks.Chunk40
import Results.Genus.FiniteComparison.Chunks.Chunk41
import Results.Genus.FiniteComparison.Chunks.Chunk42
import Results.Genus.FiniteComparison.Chunks.Chunk43
import Results.Genus.FiniteComparison.Chunks.Chunk44
import Results.Genus.FiniteComparison.Chunks.Chunk45
import Results.Genus.FiniteComparison.Chunks.Chunk46
import Results.Genus.FiniteComparison.Chunks.Chunk47
import Results.Genus.FiniteComparison.Chunks.Chunk48
import Results.Genus.FiniteComparison.Chunks.Chunk49
import Results.Genus.FiniteComparison.Chunks.Chunk50
import Results.Genus.FiniteComparison.Chunks.Chunk51
import Results.Genus.FiniteComparison.Chunks.Chunk52

namespace SubmittedGenus.FiniteComparison
open FiniteArithmetic.Reservoir OriginalPopulations OriginalSources
lemma all_comparisons (g : ℕ) (hg : 1≤g) (hg' : g≤836) :
    0≤tableResidual g ∧ tableResidual g≤(capacityLookup837 g:ℤ) := by
  by_cases h0 : g<17
  · exact comparisonRange_apply comparison_00 (by omega) h0
  by_cases h1 : g<33
  · exact comparisonRange_apply comparison_01 (by omega) h1
  by_cases h2 : g<49
  · exact comparisonRange_apply comparison_02 (by omega) h2
  by_cases h3 : g<65
  · exact comparisonRange_apply comparison_03 (by omega) h3
  by_cases h4 : g<81
  · exact comparisonRange_apply comparison_04 (by omega) h4
  by_cases h5 : g<97
  · exact comparisonRange_apply comparison_05 (by omega) h5
  by_cases h6 : g<113
  · exact comparisonRange_apply comparison_06 (by omega) h6
  by_cases h7 : g<129
  · exact comparisonRange_apply comparison_07 (by omega) h7
  by_cases h8 : g<145
  · exact comparisonRange_apply comparison_08 (by omega) h8
  by_cases h9 : g<161
  · exact comparisonRange_apply comparison_09 (by omega) h9
  by_cases h10 : g<177
  · exact comparisonRange_apply comparison_10 (by omega) h10
  by_cases h11 : g<193
  · exact comparisonRange_apply comparison_11 (by omega) h11
  by_cases h12 : g<209
  · exact comparisonRange_apply comparison_12 (by omega) h12
  by_cases h13 : g<225
  · exact comparisonRange_apply comparison_13 (by omega) h13
  by_cases h14 : g<241
  · exact comparisonRange_apply comparison_14 (by omega) h14
  by_cases h15 : g<257
  · exact comparisonRange_apply comparison_15 (by omega) h15
  by_cases h16 : g<273
  · exact comparisonRange_apply comparison_16 (by omega) h16
  by_cases h17 : g<289
  · exact comparisonRange_apply comparison_17 (by omega) h17
  by_cases h18 : g<305
  · exact comparisonRange_apply comparison_18 (by omega) h18
  by_cases h19 : g<321
  · exact comparisonRange_apply comparison_19 (by omega) h19
  by_cases h20 : g<337
  · exact comparisonRange_apply comparison_20 (by omega) h20
  by_cases h21 : g<353
  · exact comparisonRange_apply comparison_21 (by omega) h21
  by_cases h22 : g<369
  · exact comparisonRange_apply comparison_22 (by omega) h22
  by_cases h23 : g<385
  · exact comparisonRange_apply comparison_23 (by omega) h23
  by_cases h24 : g<401
  · exact comparisonRange_apply comparison_24 (by omega) h24
  by_cases h25 : g<417
  · exact comparisonRange_apply comparison_25 (by omega) h25
  by_cases h26 : g<433
  · exact comparisonRange_apply comparison_26 (by omega) h26
  by_cases h27 : g<449
  · exact comparisonRange_apply comparison_27 (by omega) h27
  by_cases h28 : g<465
  · exact comparisonRange_apply comparison_28 (by omega) h28
  by_cases h29 : g<481
  · exact comparisonRange_apply comparison_29 (by omega) h29
  by_cases h30 : g<497
  · exact comparisonRange_apply comparison_30 (by omega) h30
  by_cases h31 : g<513
  · exact comparisonRange_apply comparison_31 (by omega) h31
  by_cases h32 : g<529
  · exact comparisonRange_apply comparison_32 (by omega) h32
  by_cases h33 : g<545
  · exact comparisonRange_apply comparison_33 (by omega) h33
  by_cases h34 : g<561
  · exact comparisonRange_apply comparison_34 (by omega) h34
  by_cases h35 : g<577
  · exact comparisonRange_apply comparison_35 (by omega) h35
  by_cases h36 : g<593
  · exact comparisonRange_apply comparison_36 (by omega) h36
  by_cases h37 : g<609
  · exact comparisonRange_apply comparison_37 (by omega) h37
  by_cases h38 : g<625
  · exact comparisonRange_apply comparison_38 (by omega) h38
  by_cases h39 : g<641
  · exact comparisonRange_apply comparison_39 (by omega) h39
  by_cases h40 : g<657
  · exact comparisonRange_apply comparison_40 (by omega) h40
  by_cases h41 : g<673
  · exact comparisonRange_apply comparison_41 (by omega) h41
  by_cases h42 : g<689
  · exact comparisonRange_apply comparison_42 (by omega) h42
  by_cases h43 : g<705
  · exact comparisonRange_apply comparison_43 (by omega) h43
  by_cases h44 : g<721
  · exact comparisonRange_apply comparison_44 (by omega) h44
  by_cases h45 : g<737
  · exact comparisonRange_apply comparison_45 (by omega) h45
  by_cases h46 : g<753
  · exact comparisonRange_apply comparison_46 (by omega) h46
  by_cases h47 : g<769
  · exact comparisonRange_apply comparison_47 (by omega) h47
  by_cases h48 : g<785
  · exact comparisonRange_apply comparison_48 (by omega) h48
  by_cases h49 : g<801
  · exact comparisonRange_apply comparison_49 (by omega) h49
  by_cases h50 : g<817
  · exact comparisonRange_apply comparison_50 (by omega) h50
  by_cases h51 : g<833
  · exact comparisonRange_apply comparison_51 (by omega) h51
  exact comparisonRange_apply comparison_52 (by omega) (by omega)

/-- Every original integer comparison, with accepted N and original capacity.
Graph table interpretation is deliberately not claimed by this theorem. -/
theorem original_integer_comparisons (g : ℕ) (hg : 1≤g) (hg' : g≤836) :
    0≤residualUpper g (upperFour g) (upperFour (g-1)) (upperFive g) ∧
    residualUpper g (upperFour g) (upperFour (g-1)) (upperFive g)≤(originalCapacity g:ℤ) := by
  have h := all_comparisons g hg hg'
  rwa [tableResidual_eq_source g (by omega),capacityLookup837_correct g (by omega)] at h

/-- The remaining premises are precisely the original raw-table/omitted-tail
and genuine-five upper bounds, not numerical comparison premises. -/
theorem actual_finite_capacity (g : ℕ) (hg : 1≤g) (hg' : g≤836)
    (hU : rawFourCount g≤upperFour g)
    (hUp : rawFourCount (g-1)≤upperFour (g-1))
    (hV : CapFiveMass.count g≤upperFive g) :
    Fintype.card (SourceClass g .E)≤originalCapacity g :=
  finite_capacity_of_integer_comparison g _ _ _ _ hU hUp hV
    (original_integer_comparisons g hg hg').2

#print axioms original_integer_comparisons
#print axioms actual_finite_capacity
end SubmittedGenus.FiniteComparison
