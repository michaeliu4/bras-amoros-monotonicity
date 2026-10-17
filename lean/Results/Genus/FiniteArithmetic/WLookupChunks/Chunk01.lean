import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_01 : CheckedRange 32 32 := by decide
#print axioms recurrence_01
theorem weak_01 : WeakRange 32 32 := by decide
theorem sharp_01 : SharpRange 32 32 := by decide
#print axioms weak_01
#print axioms sharp_01
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
