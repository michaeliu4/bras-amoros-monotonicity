import Results.Genus.FiniteArithmetic.WLookupData
namespace SubmittedGenus.FiniteArithmetic.WLookupCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem recurrence_00 : CheckedRange 0 32 := by decide
#print axioms recurrence_00
theorem weak_00 : WeakRange 0 32 := by decide
theorem sharp_00 : SharpRange 0 32 := by decide
#print axioms weak_00
#print axioms sharp_00
end SubmittedGenus.FiniteArithmetic.WLookupCertificate
