# Verification map

## Standalone computational checks

| Computational claim | Inputs | Command | Coverage |
|---|---|---|---|
| Capacity and reservoir coefficients | `data/exact-capacity-lower.json`, `data/refined-binary-coefficients.json` | `python3 checks/capacity/verify_numerical_inputs.py` | Exact rational recurrences through degree 1500 |
| Raw omitted-pivot multiplier | none beyond checker constants | `python3 checks/raw-tail/check_raw_tail_scalars.py` | Exact scalar premises and multiplier `< 221715/1000000` |
| Finite mass inputs | two JSON files in `data/mass/` | `python3 checks/mass/check_mass.py` | Guarded-box schema and exact scalar assembly |
| Final mass and analytic join | preceding mass check | `python3 checks/mass/check_mass_refinement.py` | Mass `< 2024`; comparison fails at 836 and passes from 837 |
| Finite comparison | four top-level JSON files in `data/` | `python3 checks/check_finite.py --output build/finite-check.json` | Every row `1 <= g <= 836`, including switches 300/301, 603/604/605, and 836/837 |

The finite checker reports both absolute and normalized margins. Its smallest
absolute slack is 1 at genera 1 and 2. The minimum Fibonacci-normalized slack is
`15028705/33489287` at genus 42. The minimum capacity-normalized slack occurs at
genus 605 and is approximately `0.1798619157307901`.

The guarded-box and coefficient generators are deterministic mathematical
programs, but executable hashes can vary across compilers and platforms. Compare
the exact JSON fields or coefficient arrays, and record the compiler, GMP
version, command, and source hash for a new regeneration.

The v1 computational inputs are pinned at commit
`26d999739c7233f8131790efcbc367c0463caf09`. Later license and documentation
updates leave the generators and six exact data files unchanged. Provenance
fields naming historical shard manifests do not denote replay dependencies:
the direct generator commands rebuild the aggregate without those manifests.

## Lean proof verification

| Claim or check | Lean root or input | Command | Coverage |
|---|---|---|---|
| Published source identity and certificate plan | `lean/**/*.lean`, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `.github/lean/source-sha256.json` | `python3 -I .github/lean/prepare.py` | Rejects missing, extra, or modified project source/configuration; plans exactly 279 native certificates |
| Full theorem build | `Results.Genus.Native.Main`, `Results.Genus.Native.Coverage`, `Results.Genus.Native.KnownAsymptotic` | `cd lean && lake build Results.Genus.Native.Main Results.Genus.Native.Coverage Results.Genus.Native.KnownAsymptotic` | Builds the main theorem, audited submitted-framework closure, and separate background proposition |
| Exact axiom audit | generated `.ci-plan/AxiomAudit.lean` | `cd lean && lake env lean ../.ci-plan/AxiomAudit.lean` | Requires only `propext`, `Classical.choice`, `Quot.sound`, and the exact generated axiom for each of 279 native theorems |
| Fresh kernel replay | `Results.Genus.Native.Coverage` | `cd lean && lake env leanchecker --fresh Results.Genus.Native.Coverage` | Rechecks the full proof closure in a fresh checker process |
| Background replay | `Results.Genus.Native.KnownAsymptotic` | `cd lean && lake env leanchecker --fresh Results.Genus.Native.KnownAsymptotic` | Rechecks the separate definition of the cited Zhai asymptotic proposition; this proposition is not proved or used by the main theorem |

The theorem checked at the end of `Results.Genus.Native.Main` is

```lean
SubmittedGenus.Native.bras_amoros_weak_monotonicity :
  ∀ g : ℕ, NumericalSemigroup.count g ≤ NumericalSemigroup.count (g + 1)
```

The 279 native computations consist of 224 cap-four array shards, 12 cap-five
array shards, and 43 prefix chunks. The planner rejects `sorry`, `admit`, declared
axioms, unsafe or externally implemented code, and trust-bypass constructs in
the project closure. It also checks the exact native module count and generated
axiom names.

The fresh replay verifies the proof terms again, but it does not independently
recompute the semantics of compiled native evaluation. The trust boundary is the
Lean kernel, the standard axioms listed above, and compiled evaluation for the
279 named certificate theorems. `SubmittedGenus.Native.ZhaiAsymptotic` is only a
background `Prop`; it is neither proved in this project nor a dependency of the
main theorem.

The default workflow performs a clean, distributed rebuild of every native
certificate from checked-out source before the final build, axiom audit, and
fresh replay. It does not use a project build cache or a prior-run proof
artifact. The narrowly scoped PR 2 recovery described below is an explicit
exception for continuing the same verification after an audit-helper repair.
Public verification completed on 20 October 2026, with the provenance below.

### Audit-helper recovery on PR 2

Public run `39069868966`, on head
`a5d34b7027d21d1c3ad39ba61bd468a1b9ae0bb6` and PR merge commit
`161425b091a24e6b5afc3f03d9979dc3d930f382`, successfully compiled all 279
native certificates and all three published proof roots. Its generated axiom
audit then failed to elaborate an unannotated declaration counter as a natural
number. The repair annotates that counter with `Nat`; it does not change any
proof source, allowed axiom, provenance check, or coverage requirement.

For this same-repository PR and branch only, the workflow resumes from that
exact public run's base and native artifacts. The recovery helper requires the
original source-manifest digest, all actual source/configuration hashes, the
pinned toolchain, the reviewed helper hashes, and the original artifact
run/commit identity. Archive/member digests, shared-base identity and exactly
279 native modules are still checked. Recovery downloads use the official GitHub
CLI with complete pagination, sequential named batches, pacing and bounded
backoff after failures. Other PRs and manual runs retain the
clean native build. Recovery fails closed if the proof/configuration changes;
it does not fall back to silently reusing incompatible outputs.

The repaired run passed the full root build, the exact axiom audit and both
fresh replays. Its evidence records the original computation run and the
repaired commit separately.

### Completed public verification

[Run 39422414504](https://github.com/michaeliu4/bras-amoros-monotonicity/actions/runs/39422414504)
completed successfully on 20 October 2026 at 13:06 UTC. Its source head is
`6a69a6fbffa54e91336c4ad5bcac6d9b7556d7cf`; the checked PR merge commit is
`945274f36ca5a832f48b7ea725f4c09f9173d61b`.
The subsequent documentation update changes no proof, build configuration,
audit policy or verification helper.

| Evidence | Result |
|---|---|
| Original native computations | All 279 certificates compiled in [run 39069868966](https://github.com/michaeliu4/bras-amoros-monotonicity/actions/runs/39069868966), attempts 1 and 2 |
| Source identity | All 1,196 project modules matched the committed source manifest throughout recovery |
| Artifact recovery | Exact 279-module set restored with producer identity, toolchain, shared-base and archive/member checks |
| Full root build | 4,327 build jobs completed successfully; exit status 0 |
| Exact axiom audit | 19,680 declarations checked; 612 distinct declarations use native evaluation; exactly 279 native axioms |
| Fresh replay of `Results.Genus.Native.Coverage` | Exit status 0 |
| Fresh replay of `Results.Genus.Native.KnownAsymptotic` | Exit status 0 |

The full log is attached to
[verification job 118626529370](https://github.com/michaeliu4/bras-amoros-monotonicity/actions/runs/39422414504/job/118626529370).
The run's single `verification-evidence` artifact has ID `12265818948` and
SHA-256 digest
`1052c103a6f438a228bf9f4df173305e2534d3b12b68076b33896a4c430fe14b`.
It contains the build, audit and replay logs, the exact certificate plan,
recovery provenance and source manifest. GitHub artifact retention is finite;
the recorded expiry is 19 November 2026.

This verifies the all-genus weak-monotonicity theorem over actual numerical
semigroups under the trust boundary stated above. The 612 declarations counted
by the audit are users of native evaluation, not 612 separate computations.
Fresh replay retains trust in the 279 compiled computations, and the separate
Zhai asymptotic proposition remains background only.
