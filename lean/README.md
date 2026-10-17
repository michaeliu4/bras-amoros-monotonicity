# Lean formalization

This directory contains the Lean 4 formalization of the weak monotonicity
theorem for the number of numerical semigroups of each genus. The project uses
Lean `v4.32.1` and the dependencies pinned in `lake-manifest.json`.

## Main theorem

`Results/Genus/Native/Main.lean` proves:

```lean
SubmittedGenus.Native.bras_amoros_weak_monotonicity :
  ∀ g : ℕ, NumericalSemigroup.count g ≤ NumericalSemigroup.count (g + 1)
```

`NumericalSemigroup.count g` is defined from the finite type of numerical
semigroups whose complements in `ℕ` have cardinality `g`. Thus the theorem is
about actual numerical semigroups, rather than only a table or relaxed
Kunz-word population.

## Theorem map

- `Results/Genus/Semigroup.lean` defines numerical semigroups, genus fibres, and
  `NumericalSemigroup.count`.
- `Results/Genus/Kunz.lean` relates valid Kunz words to numerical semigroups and
  proves the genus/weight correspondence.
- `Results/Genus/Injection/` formalizes the parent map and the reduction of weak
  monotonicity to bounding exceptional source classes.
- `Results/Genus/RawGraph/`, `CapFourMass/`, `CapFiveMass/`,
  `FiniteComparison/`, and `TailComparison/` formalize the finite and analytic
  estimates used by the submitted argument.
- `Results/Genus/Native/Interface.lean` packages the remaining finite
  computations as an explicit certificate interface.
- `Results/Genus/Native/Main.lean` instantiates that interface with the native
  certificates and proves the main theorem with no remaining certificate hypotheses.
- `Results/Genus/Native/Coverage.lean` exposes named manuscript-level
  consequences and imports the complete submitted-framework closure for audit.
- `Results/Genus/Native/KnownAsymptotic.lean` defines
  `SubmittedGenus.Native.ZhaiAsymptotic`, the published asymptotic result cited
  as background. It is a proposition only: this project does not prove it, and
  the main theorem does not depend on it.

## Local build

From the repository root, first verify that the published sources and pinned
configuration match the committed manifest:

```sh
python3 -I .github/lean/prepare.py
```

Install the pinned Lean toolchain with Elan before building. Then build the
three public roots:


```sh
cd lean
lake build Results.Genus.Native.Main \
  Results.Genus.Native.Coverage \
  Results.Genus.Native.KnownAsymptotic
```

This builds all dependencies on one machine and can take substantial time. The
public GitHub Actions workflow distributes the native certificate modules.

After a complete build, run the generated exact axiom audit and fresh replays:

```sh
lake env lean ../.ci-plan/AxiomAudit.lean
lake env leanchecker --fresh Results.Genus.Native.Coverage
lake env leanchecker --fresh Results.Genus.Native.KnownAsymptotic
```

The CI workflow runs the planner again after artifact restoration and after the
final build, so any missing, extra, or modified source/configuration file causes
the run to fail.

## Certificate coverage

The formalization contains 279 `native_decide` certificate theorems:

- 224 cap-four shards for the coefficient array through the required range;
- 12 cap-five shards; and
- 43 prefix chunks for the short, pure, and mixed guarded prefix bounds.

CI compiles each certificate from checked-out source in the current run. It then
merges only build outputs whose public commit, run, source manifest, toolchain,
module, archive, and member identities match. All 279 modules are required
before the main theorem is built.

## Trust boundary

The axiom audit permits the standard axioms `propext`, `Classical.choice`, and
`Quot.sound`, plus one exact generated axiom for each of the 279 native
certificate theorems. The expected generated suffix is
`._native.native_decide.ax_1_1`; a different name fails the audit rather than
widening the policy.

The source planner rejects `sorry`, `admit`, declared axioms, `opaque`, `unsafe`,
external implementations, and listed trust-bypass constructs throughout the
project closure. The fresh `leanchecker` replay rechecks the proof terms in a
new process. It still trusts compiled evaluation for the 279 named native
computations; it does not independently re-prove those calculations by kernel
reduction.

Public CI verification of this exported project is pending. The existing
standalone Python/C++ checks remain separately reproducible as described in the
repository root `README.md` and `VERIFICATION.md`.
