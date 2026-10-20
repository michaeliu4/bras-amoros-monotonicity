import Results.Genus.ArrayNative.Cap5.Final
import Results.Genus.FinalAssembly.ArrayCertificates

/-! M5 glue (cap-5 half closed natively): the native `h5` has exactly the shape consumed
by `arrayCertificates_of_range_checks`.  `h4` is still an explicit hypothesis until the
cap-4 shards (PLAN-CAP4.md) have been produced and checked. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative

theorem arrayCertificates_of_cap4_and_native_cap5
    (h4 : ∀ g, g ≤ 897 → (rangePolynomial 597 300 4).coeff g = FiniteComparison.capFourTable g) :
    FinalAssembly.OriginalArrayCertificates :=
  FinalAssembly.arrayCertificates_of_range_checks h4 Cap5.range_coeff

#print axioms arrayCertificates_of_cap4_and_native_cap5
end SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative
