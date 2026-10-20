import Results.Genus.Native.Main
import Results.Genus.Native.CoverageCore
import Results.Genus.SubmittedPaperProduction

/-! # Coverage statements, unconditional

Manuscript: Git blob `e04fb276e8ceed829059cf724ead1e18e8bc9e9f` (line numbers
refer to that blob).  Each theorem of `Native/CoverageCore.lean` that takes the
certificate hypothesis `h : FinalAssembly.SubmittedPaperCertificates` is stated
here unconditionally by applying it to `Native.submitted_certificates`, under the
trust model of `Native/Main.lean` (the named cap-four/cap-five array shards and
prefix chunks are trusted `native_decide` computations; `#print axioms` lists
them).  The certificate-free theorems of `CoverageCore` are re-exported under the
same `Native` names; they use only `propext`, `Classical.choice`, `Quot.sound`.

This module also puts `Native.Main` and the complete 668-module submitted
framework `SubmittedPaperProduction` (including the 56 production-only modules
outside the `Main` closure) into one audited closure (coverage proposal G0). -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.Native
open OriginalSources OriginalPopulations FiniteArithmetic.Reservoir TailComparison
open FiniteComparison FiniteComparison.SourceBoxes FiniteComparison.AllGenusOmittedSource
open RawGraph RawGraph.SignedCounterexample

/-! ## Certificate-dependent statements (native trust via `submitted_certificates`) -/

/-- **`mass:residual`** (blob e04fb276, lines 2370-2373), unconditional:
`|E_g| < 2024 z₄^{-g} + 113 z₅^{-g}` for every `g`. -/
theorem residual_mass_bound (g : ℕ) :
    (Fintype.card (SourceClass g .E) : ℝ) <
      2024 * z4 ^ (-(g : ℤ)) + 113 * z5 ^ (-(g : ℤ)) :=
  Coverage.residual_mass_bound submitted_certificates g

/-- **`mass:tail`** (Proposition, blob e04fb276, lines 2375-2379), unconditional:
`|E_g| < L(g)` for every `g ≥ 837`. -/
theorem mass_tail (g : ℕ) (hg : 837 ≤ g) :
    Fintype.card (SourceClass g .E) < originalCapacity g :=
  Coverage.mass_tail submitted_certificates g hg

/-- **`cmp:finite`** consequence (blob e04fb276, lines 2461-2464, 2552-2558),
unconditional: `|E_g| ≤ L(g)` for `1 ≤ g ≤ 836`. -/
theorem finite_capacity (g : ℕ) (hg : 1 ≤ g) (hg' : g ≤ 836) :
    Fintype.card (SourceClass g .E) ≤ originalCapacity g :=
  Coverage.finite_capacity submitted_certificates g hg hg'

/-- Proof of `thm:main` (blob e04fb276, lines 2552-2558), unconditional:
`|E_g| ≤ L(g)` for every `g ≥ 1`. -/
theorem exceptional_le_capacity (g : ℕ) (hg : 1 ≤ g) :
    Fintype.card (SourceClass g .E) ≤ originalCapacity g :=
  Coverage.exceptional_le_capacity submitted_certificates g hg

/-- **`cmp:U`** (blob e04fb276, lines 2425-2437), unconditional table
identification: `upperFour g = C_g(300) + 1_{g ≥ 604} ⌊221715 F_g / 10^6⌋`
for `g ≤ 897`. -/
theorem upperFour_eq_source (g : ℕ) (hg : g ≤ 897) :
    upperFour g = retainedPrefix g + if 604 ≤ g then 221715 * Nat.fib g / 1000000 else 0 :=
  Coverage.upperFour_eq_source submitted_certificates g hg

/-- **`cmp:U`** (blob e04fb276, lines 2425-2437), unconditional upper bound:
`rawFourCount g ≤ U_g` for `g ≤ 897`. -/
theorem rawFour_le_upperFour (g : ℕ) (hg : g ≤ 897) : rawFourCount g ≤ upperFour g :=
  Coverage.rawFour_le_upperFour submitted_certificates g hg

/-- **`cmp:V`** (blob e04fb276, lines 2441-2450), unconditional table
identification: `upperFive g = C^{(5)}_g` (complete raw cap-five coefficient,
any box `n ≥ g + 2`) for `g ≤ 300`. -/
theorem upperFive_eq_source (g : ℕ) (hg : g ≤ 300) (n : ℕ) (hn : g + 2 ≤ n) :
    upperFive g = box 5 n g :=
  Coverage.upperFive_eq_source submitted_certificates g hg n hn

/-- **`cmp:V`** (blob e04fb276, lines 2441-2450), unconditional upper bound:
`B_g ≤ V_g` for every `g`. -/
theorem genuineFive_le_upperFive (g : ℕ) : CapFiveMass.count g ≤ upperFive g :=
  Coverage.genuineFive_le_upperFive submitted_certificates g

/-! ## Certificate-free statements (standard axioms), re-exported -/

/-- **`cmp:V`** second line (blob e04fb276, lines 2441-2450):
`V_g = ⌊113 (1000/633)^g⌋` for `g ≥ 301`. -/
theorem upperFive_eq_floor (g : ℕ) (hg : 301 ≤ g) :
    upperFive g = ⌊(113 : ℝ) * (1000 / 633) ^ g⌋₊ :=
  Coverage.upperFive_eq_floor g hg

/-- **`raw:tail`/`raw:main`** (blob e04fb276, lines 780-788), every finite pivot
horizon `N`. -/
theorem raw_tail_partial (g N : ℕ) :
    (∑ p ∈ Finset.Ico 301 N, ∑ r ∈ Finset.Ico 1 p, (fixedPivotCoeff r p g : ℝ)) ≤
      (221715 : ℝ) / 1000000 * Nat.fib g :=
  Coverage.raw_tail_partial g N

/-- **`raw:tail`/`raw:main`** (blob e04fb276, lines 780-788), literal:
`∑_{p>300} ∑_{r=1}^{p-1} [z^g] F_{r,p} ≤ 0.221715 F_g` (summable, finitely
supported in `p`). -/
theorem raw_tail (g : ℕ) :
    Summable (Coverage.omittedPivotRow g) ∧
      (∑' p, Coverage.omittedPivotRow g p) ≤ (221715 : ℝ) / 1000000 * Nat.fib g :=
  Coverage.raw_tail g

/-- **`raw:tail`** (blob e04fb276, lines 786-787): the omitted sum vanishes for
`g < 604`. -/
theorem raw_tail_zero (g : ℕ) (hg : g < 604) : (∑' p, Coverage.omittedPivotRow g p) = 0 :=
  Coverage.raw_tail_zero g hg

/-- **`mass:spectral-majorization`** (blob e04fb276, lines 1888-1891):
`0 ≤ Z ≤ P + M = A^{abs}` for `m > 2p`. -/
theorem raw_le_sourceAbsolute {r N d : ℕ} (hr : 0 < r) (hd : 0 < d) (hN : d < N)
    (hbig : r + 2 * d < N) :
    0 ≤ Polynomial.eval₂ (Nat.castRingHom ℝ) CapFourMass.radius
        (rawPolynomial (r+N) r (r+d) 4) ∧
      Polynomial.eval₂ (Nat.castRingHom ℝ) CapFourMass.radius
          (rawPolynomial (r+N) r (r+d) 4) ≤
        CapFourMass.sourcePure r N d hN + CapFourMass.sourceMixed r N d hN ∧
      CapFourMass.sourcePure r N d hN + CapFourMass.sourceMixed r N d hN =
        CapFourMass.sourceAbsolute r N d hN :=
  Coverage.raw_le_sourceAbsolute hr hd hN hbig

/-- **`mass:spectral-majorization`** (blob e04fb276, lines 1888-1891):
`0 ≤ P ≤ A^{abs}` and `Z ≤ A^{abs}` for `m > 2p`. -/
theorem spectral_majorization {r N d : ℕ} (hr : 0 < r) (hd : 0 < d) (hN : d < N)
    (hbig : r + 2 * d < N) :
    0 ≤ CapFourMass.sourcePure r N d hN ∧
      CapFourMass.sourcePure r N d hN ≤ CapFourMass.sourceAbsolute r N d hN ∧
      Polynomial.eval₂ (Nat.castRingHom ℝ) CapFourMass.radius
          (rawPolynomial (r+N) r (r+d) 4) ≤ CapFourMass.sourceAbsolute r N d hN :=
  Coverage.spectral_majorization hr hd hN hbig

/-- **Example** (blob e04fb276, lines 720-723): `(5,4,2,1)` is a leaf with ordinary
parent `(4,4,2,1)` (sole `1` final), effective generator `21`. -/
theorem example_5421 :
    Coverage.childData.toSemigroup.IsLeaf ∧
      Coverage.parentData.toSemigroup.IsEffectiveGenerator 21 ∧
      (∀ n, n ∈ Coverage.childData.toSemigroup ↔
        n ∈ Coverage.parentData.toSemigroup ∧ n ≠ 21) ∧
      Coverage.parentData.toSemigroup.IsOrdinaryChild Coverage.childData.toSemigroup ∧
      OriginalSources.finalOneFour Coverage.parentData ∧
      Coverage.childData.weight = 12 ∧ OriginalSources.sector Coverage.childData = .E :=
  Coverage.example_5421

/-- **Remark** (blob e04fb276, lines 1987-1991): `ν₂/R² > 3/25 > (u vᵀ)₂₂`, so the
block bound fails for a bare strong run (`n = 0`). -/
theorem remark_bare_strong_run :
    (3 : ℝ) / 25 < (CapFourMass.qminus ⬝ᵥ
        ((CapFourMass.strongMatrix ^ 2) *ᵥ CapFourMass.qminus)) / CapFourMass.strongBound ^ 2 ∧
      CapFourMass.modeU 1 * CapFourMass.modeV 1 < 3 / 25 ∧
      ¬ (|CapFourMass.coupledBlock (CapFourMass.strongMatrix ^ 2) 0 1 1| ≤
          CapFourMass.strongBound ^ 2 * CapFourMass.lam ^ 0 *
            CapFourMass.modeU 1 * CapFourMass.modeV 1) :=
  Coverage.remark_bare_strong_run

end SubmittedGenus.Native

namespace SubmittedGenus.Native
#print axioms residual_mass_bound
#print axioms mass_tail
#print axioms finite_capacity
#print axioms exceptional_le_capacity
#print axioms upperFour_eq_source
#print axioms rawFour_le_upperFour
#print axioms upperFive_eq_source
#print axioms genuineFive_le_upperFive
#print axioms upperFive_eq_floor
#print axioms raw_tail_partial
#print axioms raw_tail
#print axioms raw_tail_zero
#print axioms raw_le_sourceAbsolute
#print axioms spectral_majorization
#print axioms example_5421
#print axioms remark_bare_strong_run
end SubmittedGenus.Native

/-! Coverage proposal G0: production-only declarations of the submitted framework
(outside the `Native.Main` closure), audited in the same closure as `Main`.
These names were checked locally against the built `SubmittedPaperProduction`
closure (standard axioms only). -/
#print axioms SubmittedGenus.FiniteComparison.MultiplicityThree.count_nine
#print axioms SubmittedGenus.FiniteComparison.MultiplicityThree.count_ten
#print axioms SubmittedGenus.FiniteComparison.MultiplicityThree.cited_counting_inequality_false
#print axioms SubmittedGenus.FiniteComparison.MultiplicityThree.valid_iff
#print axioms SubmittedGenus.FiniteComparison.MultiplicityThree.count_eq_pair_card
#print axioms SubmittedGenus.OriginalMaps.original_partial_map_all
#print axioms SubmittedGenus.OriginalMaps.originalPhi_binary_capacity
#print axioms SubmittedGenus.OriginalMaps.originalPhi_sharp_binary_capacity
#print axioms SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate.safe_identity
#print axioms SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate.early_identity
#print axioms SubmittedGenus.FixedPivot.correctedNumerator_natDegree_sharp
#print axioms SubmittedGenus.GoldenSpectral.actual_strong_block_orthonormal
#print axioms SubmittedGenus.GoldenSpectral.strong_operator_norm_lt
#print axioms SubmittedGenus.GoldenSpectral.restricted_operator_norm_lt
#print axioms SubmittedGenus.GoldenSpectral.projected_restricted_eq_orthonormal
#print axioms SubmittedGenus.QuadraticGeometric.tsum_tail
#print axioms SubmittedGenus.GoldenTail.quadraticTailReal_tsum
#print axioms SubmittedGenus.GoldenTail.quadraticTail_hasSum
#print axioms SubmittedGenus.CapFiveMass.General.mass_five_general
#print axioms SubmittedGenus.FiniteComparison.original_multiplicity_class_count
#print axioms SubmittedGenus.FiniteComparison.Slack.integer_minimum
#print axioms SubmittedGenus.FiniteComparison.Slack.integer_minimum_only
#print axioms SubmittedGenus.FiniteComparison.Slack.fibonacci_minimum
#print axioms SubmittedGenus.FiniteComparison.Slack.fibonacci_minimum_attained
#print axioms SubmittedGenus.FiniteComparison.Slack.fibonacci_minimum_decimal
#print axioms SubmittedGenus.FiniteComparison.Slack.capacity_minimum
#print axioms SubmittedGenus.FiniteComparison.Slack.capacity_minimum_attained
#print axioms SubmittedGenus.FiniteComparison.Slack.capacity_minimum_decimal
#print axioms SubmittedGenus.FiniteComparison.Slack.delta_eq_source
#print axioms SubmittedGenus.FiniteComparison.Slack.transition_300
#print axioms SubmittedGenus.FiniteComparison.Slack.transition_301
#print axioms SubmittedGenus.FiniteComparison.Slack.transition_603
#print axioms SubmittedGenus.FiniteComparison.Slack.transition_604
#print axioms SubmittedGenus.FiniteComparison.Slack.transition_605
#print axioms SubmittedGenus.FiniteComparison.Slack.transition_836
#print axioms SubmittedGenus.FiniteComparison.Slack.five_before_switch
#print axioms SubmittedGenus.FiniteComparison.Slack.five_after_switch
#print axioms SubmittedGenus.FiniteComparison.Slack.four_before_switch
#print axioms SubmittedGenus.FiniteComparison.Slack.four_after_switch
#print axioms SubmittedGenus.TailComparison.scalar_failure_836
#print axioms SubmittedGenus.TailComparison.joining_absolute_margin
#print axioms SubmittedGenus.TailComparison.joining_relative_margin
#print axioms SubmittedGenus.GoldenTail.omittedMultiplierRow_tsum_le
#print axioms SubmittedGenus.CapFourMass.strong_operator_norm_lt
#print axioms SubmittedGenus.CapFourMass.actual_strong_block_orthonormal
#print axioms SubmittedGenus.FixedPivot.sourceP_monic
#print axioms SubmittedGenus.FixedPivot.sourceP_map_eq_roots
#print axioms SubmittedGenus.FixedPivot.rawPolynomialZ_recurrence_original
#print axioms SubmittedGenus.OriginalMaps.binaryEndTwo_card_all
#print axioms SubmittedGenus.FiniteComparison.exceptional_le_signed_envelope
