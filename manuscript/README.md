# Genus monotonicity for numerical semigroups — V1

This directory preserves Mingchang Liu’s final V1 author manuscript.

- [Read the paper](genus-monotonicity_V1.pdf)
- [Download the buildable LaTeX source](genus-monotonicity-V1-source.zip)
- [Source](manuscript.tex)
- [File identities](MANIFEST.json)

The paper proves weak genus monotonicity, `n_(g+1) >= n_g` for every integer `g >= 0`. It does not prove the stronger Fibonacci inequality. The computer-assisted part compares bounds for relaxed counts in genera 1–836; it is not a census of all numerical semigroups in that range. Generating-function estimates cover the analytic tail from genus 837.

This is an author manuscript, not a peer-reviewed publication. The separate journal-specific derivative and submission record are not included here. The existing code/data release `v1` remains unchanged.

## Build

The bibliography is embedded, and no external figures are required. For the pinned build, install Tectonic 0.17.0 and run:

```sh
python3 build.py --tectonic /path/to/tectonic
```

After the specified TeX bundle is cached, replay with:

```sh
python3 build.py --tectonic /path/to/tectonic --only-cached
```

The PDF is written to `build/manuscript.pdf`. The build checks the engine and bundle identities in `tex_environment.json`. The source archive contains `manuscript.tex`, `build.py`, `tex_environment.json` and this README.

## Rights

The repository’s MIT grant covers its original code, computed data and documentation. It does not grant an MIT license to the manuscript text or PDF. No additional manuscript license is granted by this upload.
