import Results.Genus.Semigroup
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! # The cited asymptotic `eq:known-asymptotic`

Manuscript (blob e04fb276), lines 68–73: "Zhai proved that n_g ∼ C φ^g, φ = (1+√5)/2,
C > 0.  Consequently n_{g+1}/n_g → φ > 1, so eventual strict increase was already known."

The paper cites this published theorem (Zhai) as background; it does not prove it and
the proof of `thm:main` does not use it.  Following the lab rule for outside results
(state them explicitly, never add them as axioms), the statement is recorded here as a
named proposition about the same `NumericalSemigroup.count`.  It is NOT proved here and
nothing in `Native.Main` depends on it. -/
namespace SubmittedGenus.Native

/-- `eq:known-asymptotic` (Zhai; cited, not proved in the manuscript):
`n_g ∼ C φ^g` for some `C > 0`, with `φ` the golden ratio. -/
def ZhaiAsymptotic : Prop :=
  ∃ C : ℝ, 0 < C ∧
    Asymptotics.IsEquivalent Filter.atTop
      (fun g : ℕ => (NumericalSemigroup.count g : ℝ)) (fun g : ℕ => C * Real.goldenRatio ^ g)

end SubmittedGenus.Native
