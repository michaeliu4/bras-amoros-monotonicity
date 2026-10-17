import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_02 : CheckedRange 64 32 := by decide
#print axioms recurrence_02
theorem weak_02 : WeakRange 64 32 := by decide
theorem sharp_02 : SharpRange 64 32 := by decide
#print axioms weak_02
#print axioms sharp_02
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
