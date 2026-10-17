import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_15 : CheckedRange 480 20 := by decide
#print axioms recurrence_15
theorem weak_15 : WeakRange 480 20 := by decide
theorem sharp_15 : SharpRange 480 20 := by decide
#print axioms weak_15
#print axioms sharp_15
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
