import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_05 : CheckedRange 160 32 := by decide
#print axioms recurrence_05
theorem weak_05 : WeakRange 160 32 := by decide
theorem sharp_05 : SharpRange 160 32 := by decide
#print axioms weak_05
#print axioms sharp_05
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
