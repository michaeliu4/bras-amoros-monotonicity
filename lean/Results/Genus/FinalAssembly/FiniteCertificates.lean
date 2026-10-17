import Results.Genus.FinalAssembly.ArrayCertificates
import Results.Genus.CapFourMass.CompleteEnvelope

/-! The submitted theorem now requires only concrete finite certificate acceptance.
All geometric and omitted-tail premises are supplied by proved source theorems. -/
noncomputable section
namespace SubmittedGenus.FinalAssembly
open CapFourMass

/-- Remaining finite acceptance obligations, with the original ranges unchanged. -/
structure OriginalFiniteCertificates : Prop where
  arrays : OriginalArrayCertificates
  shortPrefix : originalShortPrefix 100 ≤ shortPrefixCeiling
  purePrefix : originalPurePrefix 400 ≤ purePrefixCeiling
  mixedPrefix : originalMixedPrefix 100 ≤ mixedPrefixCeiling

/-- Conditional assembly only: this theorem does not assert that the concrete
finite certificates have yet been accepted. -/
theorem weak_growth_of_finite_certificates (h : OriginalFiniteCertificates) :
    ∀ g, NumericalSemigroup.count g ≤ NumericalSemigroup.count (g+1) :=
  weak_growth_of_array_and_mass_certificates h.arrays completeSourceEnvelope
    h.shortPrefix h.purePrefix h.mixedPrefix

#print axioms weak_growth_of_finite_certificates
end SubmittedGenus.FinalAssembly
