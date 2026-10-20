import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_14 : CheckedRange 448 32 := by decide
#print axioms recurrence_14
theorem weak_14 : WeakRange 448 32 := by decide
theorem sharp_14 : SharpRange 448 32 := by decide
#print axioms weak_14
#print axioms sharp_14
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
