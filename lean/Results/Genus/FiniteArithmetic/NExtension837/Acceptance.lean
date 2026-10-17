import Results.Genus.FiniteArithmetic.NExtension837.Chunk00
import Results.Genus.FiniteArithmetic.NExtension837.Chunk01
import Results.Genus.FiniteArithmetic.NExtension837.Chunk02
import Results.Genus.FiniteArithmetic.NExtension837.Chunk03
import Results.Genus.FiniteArithmetic.NExtension837.Chunk04
import Results.Genus.FiniteArithmetic.NExtension837.Chunk05
import Results.Genus.FiniteArithmetic.NExtension837.Chunk06

namespace SubmittedGenus.FiniteArithmetic
open PowerSeries NExtension837

theorem nLookup837_valid : Sparse.LookupValidPrefix numeratorTerms denominatorTail nLookup837 837 := by
  intro n
  by_cases h0 : n.val<128
  · exact checkedRange_apply recurrence_00 (by omega) h0
  by_cases h1 : n.val<256
  · exact checkedRange_apply recurrence_01 (by omega) h1
  by_cases h2 : n.val<384
  · exact checkedRange_apply recurrence_02 (by omega) h2
  by_cases h3 : n.val<512
  · exact checkedRange_apply recurrence_03 (by omega) h3
  by_cases h4 : n.val<640
  · exact checkedRange_apply recurrence_04 (by omega) h4
  by_cases h5 : n.val<768
  · exact checkedRange_apply recurrence_05 (by omega) h5
  exact checkedRange_apply recurrence_06 (by omega) (by omega)

theorem nLookup837_source_correct (n : ℕ) (hn : n<837) :
    nLookup837 n=coeff n capacityN :=
  Sparse.lookupValidPrefix_source _ _ _ _ denominator_positive nLookup837_valid _ source_identity n hn

theorem nLookup837_card_correct (n : ℕ) (hn : n<837) :
    nLookup837 n=(Fintype.card (NWords n):ℤ) := by
  rw [nLookup837_source_correct n hn,capacityN_source_coeff]

#print axioms nLookup837_valid
#print axioms nLookup837_source_correct
#print axioms nLookup837_card_correct
end SubmittedGenus.FiniteArithmetic
