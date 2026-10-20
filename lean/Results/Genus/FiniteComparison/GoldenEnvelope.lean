import Results.Genus.FiniteComparison.RetainedPrefix
import Results.Genus.GoldenTail.FiniteBound

/-! The submitted raw:integer-envelope corollary, now with every source and
analytic multiplier premise discharged. Original array values remain separate. -/
noncomputable section
namespace SubmittedGenus.FiniteComparison.GoldenEnvelope
open OriginalPopulations SourceBoxes AllGenusOmittedSource RetainedPrefix

/-- Original all-genus integer envelope for the full raw cap-four population. -/
theorem original_integer_envelope (g : ℕ) : rawFourCount g ≤ retainedPrefix g+
    if 604≤g then 221715*Nat.fastFib g/1000000 else 0 :=
  integer_envelope_of_multiplier GoldenTail.coefficientMultiplier
    (fun g p r _ hr hrp => GoldenTail.coefficientMultiplier_source_bound g p r hr hrp)
    GoldenTail.omitted_multiplier_sum_le g

/-- The original omitted-pivot bound expressed in the exact retained source
polynomial used by all898 stored cap-four coefficients. -/
theorem original_retained_envelope (g : ℕ) (hg : g≤897) : rawFourCount g ≤ retainedFour g+
    if 604≤g then 221715*Nat.fastFib g/1000000 else 0 := by
  rw [retainedFour_eq_prefix g hg]
  exact original_integer_envelope g

#print axioms original_integer_envelope
#print axioms original_retained_envelope
end SubmittedGenus.FiniteComparison.GoldenEnvelope
