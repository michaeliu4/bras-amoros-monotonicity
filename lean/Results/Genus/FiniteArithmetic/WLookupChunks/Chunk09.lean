import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_09 : CheckedRange 288 32 := by decide
#print axioms recurrence_09
theorem weak_09 : WeakRange 288 32 := by decide
theorem sharp_09 : SharpRange 288 32 := by decide
#print axioms weak_09
#print axioms sharp_09
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
