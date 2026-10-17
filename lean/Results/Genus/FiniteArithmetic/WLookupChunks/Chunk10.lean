import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_10 : CheckedRange 320 32 := by decide
#print axioms recurrence_10
theorem weak_10 : WeakRange 320 32 := by decide
theorem sharp_10 : SharpRange 320 32 := by decide
#print axioms weak_10
#print axioms sharp_10
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
