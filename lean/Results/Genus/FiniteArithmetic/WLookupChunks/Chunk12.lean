import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_12 : CheckedRange 384 32 := by decide
#print axioms recurrence_12
theorem weak_12 : WeakRange 384 32 := by decide
theorem sharp_12 : SharpRange 384 32 := by decide
#print axioms weak_12
#print axioms sharp_12
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
