import Results.Genus.FinalAssembly.Tail
import Results.Genus.CapFourMass.MasterAssembly
import Results.Genus.FiniteComparison.Acceptance
import Results.Genus.FiniteComparison.FiveUpper

/-! Exact remaining obligations for the submitted proof. This file is an
assembly interface, not an assertion that the original certificates pass. -/
noncomputable section
namespace SubmittedGenus.FinalAssembly
open OriginalPopulations CapFourMass FiniteComparison

/-- The remaining original mathematical/source-certificate obligations.
The fields are hypotheses, never project axioms. -/
structure OriginalObligations : Prop where
  completeSourceEnvelope : CompleteSourceEnvelope
  shortPrefix : originalShortPrefix 100 ≤ shortPrefixCeiling
  purePrefix : originalPurePrefix 400 ≤ purePrefixCeiling
  mixedPrefix : originalMixedPrefix 100 ≤ mixedPrefixCeiling
  rawFourUpper : ∀ g, g ≤ 836 → rawFourCount g ≤ upperFour g
  genuineFiveLow : ∀ g, 1 ≤ g → g ≤ 300 → CapFiveMass.count g ≤ upperFive g

/-- Conditional assembly of the exact submitted weak monotonicity theorem.
No instance of OriginalObligations is asserted here. -/
theorem weak_growth_of_original_obligations (h : OriginalObligations) :
    ∀ g, NumericalSemigroup.count g ≤ NumericalSemigroup.count (g+1) := by
  have hm := mass_four_of_original_prefix_certificates h.completeSourceEnvelope
    h.shortPrefix h.purePrefix h.mixedPrefix
  apply weak_growth_of_original_certificates hm.1 hm.2
  intro g hg hg'
  apply actual_finite_capacity g hg hg' (h.rawFourUpper g hg')
    (h.rawFourUpper (g-1) (by omega))
  by_cases hsmall : g ≤ 300
  · exact h.genuineFiveLow g hg hsmall
  · exact genuineFive_le_upperFive g (by omega)

#print axioms weak_growth_of_original_obligations
end SubmittedGenus.FinalAssembly
