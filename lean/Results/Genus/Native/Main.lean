import Results.Genus.Native.Interface
import Results.Genus.ArrayNative.Cap4.Final
import Results.Genus.PrefixNative.Full.Certificates

/-! # Bras-Amorós weak monotonicity: unconditional main theorem

Exact submitted manuscript (Git blob e04fb276e8ceed829059cf724ead1e18e8bc9e9f),
Theorem `thm:main`: for every integer g ≥ 0, n_g ≤ n_{g+1}, where n_g counts the
additive submonoids of ℕ with finite complement of size g.

Trust model (PI decision, 17 October 2026): verified in Lean, trusting compiled
evaluation for the named shard computations:
* cap-four array shards `ArrayNative.Cap4.S*.shard` (rangePolynomial 597 300 4, g ≤ 897),
* cap-five array shards `ArrayNative.Cap5.S*.shard` (rangePolynomial 149 149 5, g ≤ 300),
* prefix chunks `PrefixNative.Full.Chunks.*` (short P=100, pure P=400, mixed P=100).
Each is a `native_decide` theorem whose generated axiom is listed by `#print axioms`;
everything else uses only `propext`, `Classical.choice`, `Quot.sound`. -/
noncomputable section
namespace SubmittedGenus.Native
open FinalAssembly CapFourMass OriginalPopulations RawGraph.PackedAcceptance

/-- All five original finite certificates of the submitted proof. -/
theorem submitted_certificates : SubmittedPaperCertificates :=
  certificates_of_remaining ArrayNative.Cap4.range_coeff
    PrefixNativeCertificates.short100 PrefixNativeCertificates.pure400
    PrefixNativeCertificates.mixed100

/-- **Main theorem** (`thm:main`): the number of numerical semigroups of genus g is
weakly increasing in g, for every g ≥ 0. -/
theorem bras_amoros_weak_monotonicity :
    ∀ g : ℕ, NumericalSemigroup.count g ≤ NumericalSemigroup.count (g+1) :=
  submitted_certificates.weak_monotonicity

/-- The sharper literal mass display of the submitted manuscript. -/
theorem submitted_sharper_mass :
    Summable (fun g => (countFour g : ℝ) * ((1247 : ℝ)/2000)^g) ∧
      massFour ((1247 : ℝ)/2000) < (2023449583867101 : ℝ)/1000000000000 :=
  submitted_certificates.original_sharper_mass

/-- The submitted strict prefix rows. -/
theorem submitted_strict_prefix_rows :
    originalShortPrefix 100 < shortPrefixCeiling ∧
      originalPurePrefix 400 < purePrefixCeiling ∧
      originalMixedPrefix 100 < mixedPrefixCeiling :=
  submitted_certificates.original_strict_prefix_rows

#print axioms bras_amoros_weak_monotonicity
end SubmittedGenus.Native
