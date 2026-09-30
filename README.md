# Genus monotonicity for numerical semigroups — computational companion

This repository contains the exact data and source code used by the
computer-assisted parts of *Genus monotonicity for numerical semigroups*.
It verifies coefficient bounds for relaxed Kunz-word populations; it does not
enumerate all numerical semigroups through genus 836.

Repository: <https://github.com/michaeliu4/bras-amoros-monotonicity>

## Contents

- `src/packed_relaxation.cpp` generates the cap-four and cap-five coefficient
  arrays with arbitrary-precision integer arithmetic.
- `src/certify_perron_box.cpp` generates the two guarded finite interval boxes.
- `data/` contains the exact coefficient, capacity, and guarded-box inputs.
- `checks/` contains exact Python checks for the capacity recurrences, raw
  omitted-pivot constant, finite mass bound, analytic join, and finite rows.
- `VERIFICATION.md` maps each computational claim to its inputs and command.
- `MANIFEST.json` records SHA-256 identities and coverage.

The mathematical proofs that connect these computations to numerical
semigroups are in the paper. A successful run of these programs checks the
specified computational claims, not the paper's noncomputational arguments.

## Requirements

- Python 3.11 or later; the checks use only the standard library.
- For C++ regeneration: GCC or Clang with C++17, `__int128`, and
  `__builtin_*_overflow` support.
- GMP with C++ bindings and `pkg-config` metadata for `gmpxx`.

## Quick verification

Run from the repository root:

```sh
python3 checks/capacity/verify_numerical_inputs.py
python3 checks/raw-tail/check_raw_tail_scalars.py
python3 checks/mass/check_mass.py
python3 checks/mass/check_mass_refinement.py
python3 checks/check_finite.py --output build/finite-check.json
```

The first four programs write their JSON results beside the scripts; those
generated files are ignored by Git. The last command writes the complete 836-row
certificate to `build/finite-check.json`.

The expected conclusions are:

- the capacity arrays agree with exact rational recurrences through degree 1500;
- the raw omitted-pivot multiplier is below `221715/1000000`;
- the refined finite mass is below 2024 and the analytic comparison begins at
  genus 837; and
- every finite row for genera 1 through 836 has nonnegative slack.

## Coefficient regeneration

Build outside the source tree:

```sh
mkdir -p build
c++ -std=c++17 -O3 -DCAP=4 src/packed_relaxation.cpp \
  -o build/cap4 $(pkg-config --cflags --libs gmpxx)
c++ -std=c++17 -O2 -DCAP=5 src/packed_relaxation.cpp \
  -o build/cap5 $(pkg-config --cflags --libs gmpxx)
```

Regenerate cap five through degree 300 and compare all 301 coefficients:

```sh
build/cap5 300 build/cap5-degree300.json 3 149 300 2
python3 checks/check_finite.py \
  --compare-cap5 build/cap5-degree300.json \
  --output build/cap5-replay-check.json
```

The support inequality makes multiplicities 3 through 149 sufficient. This run
visits 540,274 graph triples.

A direct cap-four regeneration is:

```sh
build/cap4 897 build/cap4-degree897.json 3 597 300 2
python3 checks/check_finite.py \
  --compare-cap4 build/cap4-degree897.json \
  --output build/cap4-replay-check.json
```

This is a substantially longer computation: 17,775,550 graph triples. The
stored aggregate was assembled from 595 fixed-multiplicity shards. Of these,
552 were computed through degree 897; 43 pre-existing arrays were computed
through degree 1106 and used only through degree 897. Higher-degree terms cannot
affect retained coefficients because all subsequent polynomial shifts have
nonnegative degree.

## Guarded Perron-box regeneration

```sh
c++ -std=c++17 -O3 src/certify_perron_box.cpp \
  -o build/perron-box $(pkg-config --cflags --libs gmpxx)

build/perron-box 400 1247 2000 \
  70651823329321825 73338785529844359 73338785529844360 \
  73854862990399022 73854862990399023 1 \
  > build/P400-pure.json

build/perron-box 100 1247 2000 \
  70651823329321825 73338785529844359 73338785529844360 \
  73854862990399022 73854862990399023 0 \
  > build/P100-all.json

cmp build/P400-pure.json data/mass/P400_z1247_2000_pure_guarded.json
cmp build/P100-all.json data/mass/P100_z1247_2000_all_guarded.json
```

The two boxes cover 159,600 and 666,600 graphs respectively. The retained JSON
files contain exact integer interval endpoints with common scale `2^56`.

## Reproducibility boundary

Stored-data verification and source regeneration are distinct. The quick checks
verify hashes, exact arithmetic, and the theorem's finite and analytic joins.
The regeneration commands recompute the coefficient arrays or interval boxes
from their C++ sources. `MANIFEST.json` identifies every distributed file.

## License

The original code, computed data, and documentation are distributed under the
[MIT License](LICENSE). This grant also covers the v1 release at commit
`26d999739c7233f8131790efcbc367c0463caf09`. The manuscript and third-party
literature are not included in this grant.
