import Results.Genus.FinalAssembly.SubmittedPaperCertificates
import Results.Genus.ArrayNative.Final

/-! Final glue for the compiled-evaluation route (PI trust decision, 17 October 2026).
The cap-five array field is closed by `ArrayNative.Cap5.range_coeff` (native shards).
The remaining inputs are exactly: the cap-four array equality and the three original
prefix inequalities in their submitted 2^56-unit form.  `Main.lean` instantiates them. -/
noncomputable section
namespace SubmittedGenus.Native
open FinalAssembly CapFourMass OriginalPopulations RawGraph.PackedAcceptance

/-- The submitted certificate interface from the four still-external inputs. -/
theorem certificates_of_remaining
    (h4 : ∀ g, g ≤ 897 → (rangePolynomial 597 300 4).coeff g = FiniteComparison.capFourTable g)
    (hshort : originalShortPrefix 100 ≤ CapFourMass.shortPrefixUnits)
    (hpure : originalPurePrefix 400 ≤ CapFourMass.purePrefixUnits)
    (hmixed : originalMixedPrefix 100 ≤ CapFourMass.mixedPrefixUnits) :
    SubmittedPaperCertificates :=
  ⟨ArrayNative.arrayCertificates_of_cap4_and_native_cap5 h4, hshort, hpure, hmixed⟩

/-- Main theorem (`thm:main`), conditional only on the four remaining computations. -/
theorem weak_monotonicity_of_remaining
    (h4 : ∀ g, g ≤ 897 → (rangePolynomial 597 300 4).coeff g = FiniteComparison.capFourTable g)
    (hshort : originalShortPrefix 100 ≤ CapFourMass.shortPrefixUnits)
    (hpure : originalPurePrefix 400 ≤ CapFourMass.purePrefixUnits)
    (hmixed : originalMixedPrefix 100 ≤ CapFourMass.mixedPrefixUnits) :
    ∀ g, NumericalSemigroup.count g ≤ NumericalSemigroup.count (g+1) :=
  (certificates_of_remaining h4 hshort hpure hmixed).weak_monotonicity

#print axioms weak_monotonicity_of_remaining
end SubmittedGenus.Native
