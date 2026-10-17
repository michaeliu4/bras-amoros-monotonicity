import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_06 : CheckedRange 192 32 := by decide
#print axioms recurrence_06
theorem weak_06 : WeakRange 192 32 := by decide
theorem sharp_06 : SharpRange 192 32 := by decide
#print axioms weak_06
#print axioms sharp_06
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
