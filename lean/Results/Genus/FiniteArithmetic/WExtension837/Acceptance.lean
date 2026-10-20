import Results.Genus.FiniteArithmetic.WExtension837.Chunk00
import Results.Genus.FiniteArithmetic.WExtension837.Chunk01
import Results.Genus.FiniteArithmetic.WExtension837.Chunk02
import Results.Genus.FiniteArithmetic.WExtension837.Chunk03
import Results.Genus.FiniteArithmetic.WExtension837.Chunk04
import Results.Genus.FiniteArithmetic.WExtension837.Chunk05
import Results.Genus.FiniteArithmetic.WExtension837.Chunk06
import Results.Genus.FiniteArithmetic.WExtension837.Chunk07
import Results.Genus.FiniteArithmetic.WExtension837.Chunk08
import Results.Genus.FiniteArithmetic.WExtension837.Chunk09
import Results.Genus.FiniteArithmetic.WExtension837.Chunk10
import Results.Genus.FiniteArithmetic.WExtension837.Chunk11
import Results.Genus.FiniteArithmetic.WExtension837.Chunk12
import Results.Genus.FiniteArithmetic.WExtension837.Chunk13
import Results.Genus.FiniteArithmetic.WExtension837.Chunk14
import Results.Genus.FiniteArithmetic.WExtension837.Chunk15
import Results.Genus.FiniteArithmetic.WExtension837.Chunk16
import Results.Genus.FiniteArithmetic.WExtension837.Chunk17
import Results.Genus.FiniteArithmetic.WExtension837.Chunk18
import Results.Genus.FiniteArithmetic.WExtension837.Chunk19
import Results.Genus.FiniteArithmetic.WExtension837.Chunk20
import Results.Genus.FiniteArithmetic.WExtension837.Chunk21

namespace SubmittedGenus.FiniteArithmetic
open PowerSeries WExtension837

theorem wLookup837_valid : Sparse.LookupValidPrefix wNumeratorTerms wDenominatorTail wLookup837 837 := by
  intro n
  by_cases hold : n.val<500
  · exact old_row n.val hold
  by_cases h0 : n.val<516
  · exact checkedRange_apply recurrence_00 (by omega) h0
  by_cases h1 : n.val<532
  · exact checkedRange_apply recurrence_01 (by omega) h1
  by_cases h2 : n.val<548
  · exact checkedRange_apply recurrence_02 (by omega) h2
  by_cases h3 : n.val<564
  · exact checkedRange_apply recurrence_03 (by omega) h3
  by_cases h4 : n.val<580
  · exact checkedRange_apply recurrence_04 (by omega) h4
  by_cases h5 : n.val<596
  · exact checkedRange_apply recurrence_05 (by omega) h5
  by_cases h6 : n.val<612
  · exact checkedRange_apply recurrence_06 (by omega) h6
  by_cases h7 : n.val<628
  · exact checkedRange_apply recurrence_07 (by omega) h7
  by_cases h8 : n.val<644
  · exact checkedRange_apply recurrence_08 (by omega) h8
  by_cases h9 : n.val<660
  · exact checkedRange_apply recurrence_09 (by omega) h9
  by_cases h10 : n.val<676
  · exact checkedRange_apply recurrence_10 (by omega) h10
  by_cases h11 : n.val<692
  · exact checkedRange_apply recurrence_11 (by omega) h11
  by_cases h12 : n.val<708
  · exact checkedRange_apply recurrence_12 (by omega) h12
  by_cases h13 : n.val<724
  · exact checkedRange_apply recurrence_13 (by omega) h13
  by_cases h14 : n.val<740
  · exact checkedRange_apply recurrence_14 (by omega) h14
  by_cases h15 : n.val<756
  · exact checkedRange_apply recurrence_15 (by omega) h15
  by_cases h16 : n.val<772
  · exact checkedRange_apply recurrence_16 (by omega) h16
  by_cases h17 : n.val<788
  · exact checkedRange_apply recurrence_17 (by omega) h17
  by_cases h18 : n.val<804
  · exact checkedRange_apply recurrence_18 (by omega) h18
  by_cases h19 : n.val<820
  · exact checkedRange_apply recurrence_19 (by omega) h19
  by_cases h20 : n.val<836
  · exact checkedRange_apply recurrence_20 (by omega) h20
  exact checkedRange_apply recurrence_21 (by omega) (by omega)

theorem wLookup837_source_correct (n : ℕ) (hn : n<837) :
    wLookup837 n=coeff n capacityW :=
  Sparse.lookupValidPrefix_source _ _ _ _ wDenominatorTail_positive wLookup837_valid _ capacityW_sparse_identity n hn

#print axioms wLookup837_valid
#print axioms wLookup837_source_correct
end SubmittedGenus.FiniteArithmetic
