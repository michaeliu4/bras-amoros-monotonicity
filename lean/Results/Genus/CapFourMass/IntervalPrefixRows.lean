import Results.Genus.CapFourMass.OriginalPrefixTargets

open scoped BigOperators
namespace SubmittedGenus.CapFourMass
noncomputable section

def originalShortRow (p : ℕ) : ℝ :=
  ∑r∈Finset.Ico 1 p,∑m∈Finset.Ico (p+1) (2*p+1),
    Polynomial.eval₂ (Nat.castRingHom ℝ) radius (RawGraph.rawPolynomial m r p 4)

/-- Exact source decomposition permits separately checked bounded row batches. -/
theorem originalShortPrefix_succ (P : ℕ) :
    originalShortPrefix (P+1)=originalShortPrefix P+originalShortRow (P+1) := by
  unfold originalShortPrefix originalShortRow
  rw [Finset.sum_range_succ]

end
end SubmittedGenus.CapFourMass
