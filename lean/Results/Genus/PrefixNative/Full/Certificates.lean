import Results.Genus.FinalAssembly.SubmittedPaperCertificates
import Results.Genus.PrefixNative.Full.Final.Short100
import Results.Genus.PrefixNative.Full.Final.Pure400
import Results.Genus.PrefixNative.Full.Final.Mixed100

/-! The three prefix fields of `SubmittedPaperCertificates`, discharged by compiled evaluation.
Builds only after ALL chunk modules of `Full/Chunks` have been built (see ci-matrix.json). -/
noncomputable section
namespace SubmittedGenus.FinalAssembly.PrefixNativeCertificates
open CapFourMass
open SubmittedGenus.CapFourMass.Interval.PrefixNative

theorem short100 : originalShortPrefix 100 ≤ CapFourMass.shortPrefixUnits :=
  FullFinal.short_prefix_native_100

theorem pure400 : originalPurePrefix 400 ≤ CapFourMass.purePrefixUnits :=
  FullFinal.pure_prefix_native_400

theorem mixed100 : originalMixedPrefix 100 ≤ CapFourMass.mixedPrefixUnits :=
  FullFinal.mixed_prefix_native_100

/-- The array certificates are supplied separately (they are not part of this work). -/
theorem submitted (arrays : OriginalArrayCertificates) : SubmittedPaperCertificates :=
  ⟨arrays, short100, pure400, mixed100⟩

#print axioms submitted

end SubmittedGenus.FinalAssembly.PrefixNativeCertificates
