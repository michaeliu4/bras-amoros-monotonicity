import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_11 : CheckedRange 352 32 := by decide
#print axioms recurrence_11
theorem weak_11 : WeakRange 352 32 := by decide
theorem sharp_11 : SharpRange 352 32 := by decide
#print axioms weak_11
#print axioms sharp_11
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
