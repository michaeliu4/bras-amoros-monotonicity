import Results.Genus.FinalAssembly.SourceCertificates
import Results.Genus.FiniteComparison.GoldenEnvelope

/-! Original finite array acceptance is now the only finite-source premise.
The original omitted-pivot theorem is fully discharged. -/
noncomputable section
namespace SubmittedGenus.FinalAssembly
open CapFourMass FiniteComparison SourceBoxes

structure OriginalArrayCertificates : Prop where
  capFour : ∀ g,g≤897 → retainedFour g=capFourTable g
  capFive : ∀ g,g≤300 → box 5 294 g=capFiveTable g

lemma OriginalArrayCertificates.sourceCertificates (h : OriginalArrayCertificates) :
    OriginalSourceCertificates := by
  refine ⟨h.capFour,h.capFive,?_⟩
  intro g hg hg'
  simpa only [if_pos hg] using GoldenEnvelope.original_retained_envelope g (by omega)

/-- Exact submitted theorem, conditional only on original array acceptance,
the actual complete-mode source envelope and the three original finite prefixes. -/
theorem weak_growth_of_array_and_mass_certificates (h : OriginalArrayCertificates)
    (henv : CompleteSourceEnvelope)
    (hshort : originalShortPrefix 100≤shortPrefixCeiling)
    (hpure : originalPurePrefix 400≤purePrefixCeiling)
    (hmixed : originalMixedPrefix 100≤mixedPrefixCeiling) :
    ∀ g,NumericalSemigroup.count g≤NumericalSemigroup.count (g+1) :=
  weak_growth_of_source_certificates h.sourceCertificates henv hshort hpure hmixed

/-- The exact two aggregate equality statements consumed from the sound packed
checker. The smaller cap-five range covers the original file by proved support. -/
theorem arrayCertificates_of_range_checks
    (h4 : ∀ g,g≤897 → (RawGraph.PackedAcceptance.rangePolynomial 597 300 4).coeff g=capFourTable g)
    (h5 : ∀ g,g≤300 → (RawGraph.PackedAcceptance.rangePolynomial 149 149 5).coeff g=capFiveTable g) :
    OriginalArrayCertificates := by
  constructor
  · intro g hg
    rw [←RangeSourceBridge.originalFour_range]
    exact h4 g hg
  · intro g hg
    rw [←RangeSourceBridge.originalFive_range,RangeSourceBridge.originalFive_eq_sufficient g hg]
    exact h5 g hg

#print axioms weak_growth_of_array_and_mass_certificates
#print axioms arrayCertificates_of_range_checks
end SubmittedGenus.FinalAssembly
