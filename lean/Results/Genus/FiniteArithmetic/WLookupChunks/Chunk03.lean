import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_03 : CheckedRange 96 32 := by decide
#print axioms recurrence_03
theorem weak_03 : WeakRange 96 32 := by decide
theorem sharp_03 : SharpRange 96 32 := by decide
#print axioms weak_03
#print axioms sharp_03
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
