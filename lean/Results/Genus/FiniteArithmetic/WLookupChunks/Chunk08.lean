import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_08 : CheckedRange 256 32 := by decide
#print axioms recurrence_08
theorem weak_08 : WeakRange 256 32 := by decide
theorem sharp_08 : SharpRange 256 32 := by decide
#print axioms weak_08
#print axioms sharp_08
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
