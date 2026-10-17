import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_13 : CheckedRange 416 32 := by decide
#print axioms recurrence_13
theorem weak_13 : WeakRange 416 32 := by decide
theorem sharp_13 : SharpRange 416 32 := by decide
#print axioms weak_13
#print axioms sharp_13
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
