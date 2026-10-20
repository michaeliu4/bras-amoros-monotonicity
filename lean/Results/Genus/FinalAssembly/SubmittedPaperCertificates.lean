import Results.Genus.FinalAssembly.FiniteCertificates
import Results.Genus.CapFourMass.OriginalSharperTotal

/-! One explicit finite-certificate interface for the submitted main theorem
and its sharper literal mass display. No instance of these still-open finite
acceptance fields is supplied. The original ranges/cutoffs are unchanged. -/
noncomputable section
namespace SubmittedGenus.FinalAssembly
open CapFourMass OriginalPopulations

structure SubmittedPaperCertificates : Prop where
  arrays : OriginalArrayCertificates
  shortPrefixUnits : originalShortPrefix 100 ≤ CapFourMass.shortPrefixUnits
  purePrefixUnits : originalPurePrefix 400 ≤ CapFourMass.purePrefixUnits
  mixedPrefixUnits : originalMixedPrefix 100 ≤ CapFourMass.mixedPrefixUnits

namespace SubmittedPaperCertificates

 theorem toOriginalFiniteCertificates (h : SubmittedPaperCertificates) :
    OriginalFiniteCertificates where
  arrays := h.arrays
  shortPrefix := h.shortPrefixUnits.trans prefix_outward_rounding.2.1.le
  purePrefix := h.purePrefixUnits.trans prefix_outward_rounding.1.le
  mixedPrefix := h.mixedPrefixUnits.trans prefix_outward_rounding.2.2.le

 theorem weak_monotonicity (h : SubmittedPaperCertificates) :
    ∀ g, NumericalSemigroup.count g ≤ NumericalSemigroup.count (g+1) :=
  weak_growth_of_finite_certificates h.toOriginalFiniteCertificates

 theorem original_sharper_mass (h : SubmittedPaperCertificates) :
    Summable (fun g => (countFour g : ℝ) * ((1247 : ℝ)/2000)^g) ∧
      massFour ((1247 : ℝ)/2000) < (2023449583867101 : ℝ)/1000000000000 :=
  mass_four_sharper_of_original_prefix_units h.shortPrefixUnits h.purePrefixUnits h.mixedPrefixUnits

 theorem original_strict_prefix_rows (h : SubmittedPaperCertificates) :
    originalShortPrefix 100 < shortPrefixCeiling ∧
      originalPurePrefix 400 < purePrefixCeiling ∧
      originalMixedPrefix 100 < mixedPrefixCeiling :=
  original_prefix_units_give_strict_rows h.shortPrefixUnits h.purePrefixUnits h.mixedPrefixUnits

#print axioms toOriginalFiniteCertificates
#print axioms weak_monotonicity
#print axioms original_sharper_mass
#print axioms original_strict_prefix_rows
end SubmittedPaperCertificates
end SubmittedGenus.FinalAssembly
