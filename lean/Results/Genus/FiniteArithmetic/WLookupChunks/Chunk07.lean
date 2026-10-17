import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_07 : CheckedRange 224 32 := by decide
#print axioms recurrence_07
theorem weak_07 : WeakRange 224 32 := by decide
theorem sharp_07 : SharpRange 224 32 := by decide
#print axioms weak_07
#print axioms sharp_07
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
