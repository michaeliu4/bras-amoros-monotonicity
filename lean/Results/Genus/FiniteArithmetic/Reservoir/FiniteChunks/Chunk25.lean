import Results.Genus.FiniteArithmetic.Reservoir.Lookup1500
namespace SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
theorem recurrence_25 : CheckedRange 800 32 := by decide
theorem lower_25 : LowerRange 800 32 := by decide
#print axioms recurrence_25
#print axioms lower_25
end SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
