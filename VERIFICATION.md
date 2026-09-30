# Verification map

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
