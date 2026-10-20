import Results.Genus.FinalAssembly.OriginalObligations
import Results.Genus.FiniteComparison.SourceBoxes

/-! The original raw source tables and omitted-pivot estimate suffice for the
finite-source fields of OriginalObligations. No table equality is assumed as an axiom. -/
noncomputable section
namespace SubmittedGenus.FinalAssembly
open OriginalPopulations CapFourMass FiniteComparison FiniteComparison.SourceBoxes

/-- Source acceptance statements for the two unchanged original arrays,
plus the original omitted-pivot bound on precisely its used finite range. -/
structure OriginalSourceCertificates : Prop where
  retainedFourTable : ∀ g, g ≤ 897 → retainedFour g = capFourTable g
  retainedFiveTable : ∀ g, g ≤ 300 → box 5 294 g = capFiveTable g
  omittedFourBound : ∀ g, 604 ≤ g → g ≤ 836 →
    rawFourCount g ≤ retainedFour g + 221715 * Nat.fastFib g / 1000000

lemma OriginalSourceCertificates.rawFourUpper (h : OriginalSourceCertificates)
    (g : ℕ) (hg : g ≤ 836) : rawFourCount g ≤ upperFour g := by
  by_cases hl : g < 604
  · rw [rawFourCount_eq_retained g hl,h.retainedFourTable g (by omega)]
    simp only [upperFour,if_neg (show ¬604 ≤ g by omega),Nat.add_zero,le_refl]
  · have hb := h.omittedFourBound g (by omega) hg
    rw [h.retainedFourTable g (by omega)] at hb
    simpa only [upperFour,if_pos (show 604 ≤ g by omega)] using hb

lemma OriginalSourceCertificates.genuineFiveLow (h : OriginalSourceCertificates)
    (g : ℕ) (hg : g ≤ 300) : CapFiveMass.count g ≤ upperFive g := by
  have hb := genuineFive_le_box g hg
  rw [originalFive_box g hg,h.retainedFiveTable g hg] at hb
  simpa only [upperFive,if_pos hg] using hb

/-- Conditional exact submitted theorem, with all remaining source/certificate
premises visible. Neither the hypotheses nor their existence are claimed here. -/
theorem weak_growth_of_source_certificates
    (h : OriginalSourceCertificates) (henv : CompleteSourceEnvelope)
    (hshort : originalShortPrefix 100 ≤ shortPrefixCeiling)
    (hpure : originalPurePrefix 400 ≤ purePrefixCeiling)
    (hmixed : originalMixedPrefix 100 ≤ mixedPrefixCeiling) :
    ∀ g, NumericalSemigroup.count g ≤ NumericalSemigroup.count (g+1) := by
  apply weak_growth_of_original_obligations
  exact ⟨henv,hshort,hpure,hmixed,h.rawFourUpper,fun g _ hg => h.genuineFiveLow g hg⟩

#print axioms weak_growth_of_source_certificates
end SubmittedGenus.FinalAssembly
