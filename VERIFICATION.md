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

The public workflow performs a clean, distributed rebuild of every native
certificate from checked-out source before the final build, axiom audit, and
fresh replay. It does not use a project build cache or a prior-run proof
artifact. Public CI verification of this export is pending.
