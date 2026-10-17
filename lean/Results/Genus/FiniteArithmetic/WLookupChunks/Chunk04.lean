import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_04 : CheckedRange 128 32 := by decide
#print axioms recurrence_04
theorem weak_04 : WeakRange 128 32 := by decide
theorem sharp_04 : SharpRange 128 32 := by decide
#print axioms weak_04
#print axioms sharp_04
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
