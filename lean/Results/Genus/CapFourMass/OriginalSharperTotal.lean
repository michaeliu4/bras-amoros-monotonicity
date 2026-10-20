import Results.Genus.CapFourMass.MasterAssembly
import Results.Genus.CapFourMass.CompleteEnvelope
import Results.Genus.CapFourMass.OriginalPureTailStrict
import Results.Genus.CapFourMass.OriginalMixedTailTight
import Results.Genus.CapFourMass.OriginalTailStrictness

/-! The manuscript's sharper displayed total, conditional on its three original
pre-rounding prefix-unit bounds. These finite prefix premises remain unaccepted.
All source geometry and all omitted-tail bounds below are supplied by proofs. -/
noncomputable section
namespace SubmittedGenus.CapFourMass
open OriginalPopulations

 theorem original_pre_rounding_six_sum_lt :
    purePrefixUnits + shortPrefixUnits + mixedPrefixUnits + shortTailCeiling +
      (3745874303724769 : ℝ) / 1000000000000000 +
      (446302688776605197 : ℝ) / 1000000000000000 <
      (2023449583867101 : ℝ) / 1000000000000 := by
  norm_num [purePrefixUnits, shortPrefixUnits, mixedPrefixUnits, intervalUnit,
    shortTailCeiling]

 /-- Conditional original display178. This does not assert the three finite
 prefix acceptances, and is stronger than the six rounded-ceiling assembly. -/
 theorem mass_four_sharper_of_original_prefix_units
    (hshort : originalShortPrefix 100 ≤ shortPrefixUnits)
    (hpure : originalPurePrefix 400 ≤ purePrefixUnits)
    (hmixed : originalMixedPrefix 100 ≤ mixedPrefixUnits) :
    Summable (fun g => (countFour g : ℝ) * ((1247 : ℝ) / 2000)^g) ∧
      massFour ((1247 : ℝ) / 2000) < (2023449583867101 : ℝ) / 1000000000000 := by
  have h := genuine_mass_six_sectors completeSourceEnvelope 100 400 100
  have hs := Interval.original_short_tail_le
  have hp := Interval.original_pure_tail_tight
  have hm := Interval.original_mixed_tail_tight
  refine ⟨h.1, ?_⟩
  change massFour radius < (2023449583867101 : ℝ) / 1000000000000
  linarith only [h.2, hs, hp, hm, hshort, hpure, hmixed,
    original_pre_rounding_six_sum_lt]

 theorem original_prefix_units_give_strict_rows
    (hshort : originalShortPrefix 100 ≤ shortPrefixUnits)
    (hpure : originalPurePrefix 400 ≤ purePrefixUnits)
    (hmixed : originalMixedPrefix 100 ≤ mixedPrefixUnits) :
    originalShortPrefix 100 < shortPrefixCeiling ∧
      originalPurePrefix 400 < purePrefixCeiling ∧
      originalMixedPrefix 100 < mixedPrefixCeiling :=
  ⟨hshort.trans_lt prefix_outward_rounding.2.1,
    hpure.trans_lt prefix_outward_rounding.1,
    hmixed.trans_lt prefix_outward_rounding.2.2⟩

#print axioms original_pre_rounding_six_sum_lt
#print axioms mass_four_sharper_of_original_prefix_units
#print axioms original_prefix_units_give_strict_rows
end SubmittedGenus.CapFourMass
