#!/usr/bin/env python3
"""Reconstruct the finite comparison in exact arithmetic.

This is an arithmetic checker, not a graph-classification rerun.  It reads the
preserved exact coefficient arrays, rebuilds every comparison row from their
definitions, and records the finite/analytic joining data.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

sys.set_int_max_str_digits(100000)

EXPECTED = {
    "cap4": "4783f633270e69fb7974bef8d417999d48004e68f68f761976a83b30553c6057",
    "cap5": "85089c63450cc3ea28680759d17948e3dd15b9cfed70e7171814c8845679b1e6",
    "capacity": "5b733be738964a0ffc42c9fc6207dadb7a8d47abd5eff6f78cf53f35899a62a1",
    "binary": "1a7572dfe522bdebc597293f5809a667b80e9c28c44ed04e3d42975a35ba29d8",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path):
    return json.loads(path.read_text())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def frac_record(value: Q) -> dict:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
        "decimal": float(value),
    }


def finite_row_record(row: dict, fib: int) -> dict:
    out = dict(row)
    out["slack_over_capacity"] = frac_record(Q(row["slack"], row["capacity_lower"]))
    out["slack_over_fibonacci"] = frac_record(Q(row["slack"], fib))
    out["residual_over_capacity"] = frac_record(Q(row["residual_upper"], row["capacity_lower"]))
    return out


def resolve_inputs(data_root: Path | None, script: Path) -> tuple[dict, dict]:
    local_data = script.resolve().parent.parent / "data"
    if data_root is None:
        data_root = local_data
    root = data_root.resolve()
    paths = {
        "cap4": root / "cap4-p300-degree897.json",
        "cap5": root / "cap5-degree300.json",
        "capacity": root / "exact-capacity-lower.json",
        "binary": root / "refined-binary-coefficients.json",
    }
    for name, path in paths.items():
        require(path.is_file(), f"missing {name} input: {path}")
        require(sha256(path) == EXPECTED[name], f"unexpected {name} SHA-256")
    return paths, {name: load(path) for name, path in paths.items()}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data-root", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--compare-cap4", type=Path,
                        help="fresh engine JSON whose degree-897 coefficients must match")
    parser.add_argument("--compare-cap5", type=Path,
                        help="fresh engine JSON whose degree-300 coefficients must match")
    args = parser.parse_args()
    script = Path(__file__)
    paths, inputs = resolve_inputs(args.data_root, script)

    cap4, cap5 = inputs["cap4"], inputs["cap5"]
    require(cap4["N"] == 897 and cap4["cap"] == 4 and cap4["pmin"] == 2 and cap4["pmax"] == 300,
            "cap-four scope")
    require(len(cap4["all"]) == 898 and all(type(x) is int and x >= 0 for x in cap4["all"]),
            "cap-four coefficient array")
    require(cap5["N"] == 300 and cap5["cap"] == 5 and len(cap5["all"]) == 301,
            "cap-five scope")
    require(all(type(x) is int and x >= 0 for x in cap5["all"]), "cap-five coefficient array")

    replay = {}
    for label, candidate, stored, degree, cap in (
        ("cap4", args.compare_cap4, cap4, 897, 4),
        ("cap5", args.compare_cap5, cap5, 300, 5),
    ):
        if candidate:
            fresh = load(candidate)
            require(fresh["cap"] == cap and fresh["N"] >= degree, f"fresh {label} scope")
            require(fresh["all"][: degree + 1] == stored["all"][: degree + 1],
                    f"fresh {label} coefficient mismatch")
            replay[label] = {
                "path": str(candidate),
                "sha256": sha256(candidate),
                "coefficients_compared": degree + 1,
                "match": True,
            }

    # Fibonacci and the no-one coefficients (words on {2,3,4} with >=2 fours).
    N = 897
    fib = [0, 1]
    for _ in range(2, N + 1):
        fib.append(fib[-1] + fib[-2])
    zero = [0] * (N + 1)
    one = [0] * (N + 1)
    many = [0] * (N + 1)
    zero[0] = 1
    for g in range(1, N + 1):
        zero[g] = sum(zero[g - k] for k in (2, 3) if g >= k)
        one[g] = sum(one[g - k] for k in (2, 3) if g >= k) + (zero[g - 4] if g >= 4 else 0)
        many[g] = sum(many[g - k] for k in (2, 3, 4) if g >= k) + (one[g - 4] if g >= 4 else 0)

    capacity_rows = inputs["capacity"]["rows"]
    binary_rows = inputs["binary"]["rows"]
    require(len(capacity_rows) > N and len(binary_rows) > N, "capacity input range")

    def no_one(g: int) -> int:
        return many[g] if g >= 0 else 0

    def omitted_pivot(g: int) -> int:
        return 221715 * fib[g] // 1_000_000 if g >= 604 else 0

    def raw_upper(g: int) -> int:
        return cap4["all"][g] + omitted_pivot(g) if g >= 0 else 0

    rows = []
    for g in range(1, 837):
        q4 = raw_upper(g) - no_one(g) - no_one(g - 3) - no_one(g - 4)
        unique5 = raw_upper(g - 1) - no_one(g - 1)
        multiple5 = cap5["all"][g] if g <= 300 else 113 * 1000**g // 633**g
        caprow = capacity_rows[g]
        binrow = binary_rows[g]
        require(caprow["g"] == g and binrow["g"] == g, f"capacity row identity {g}")
        safe = caprow["free_safe_lower"]
        early = caprow["free_early_one_lower"]
        binary = binrow["free_binary_lower"]
        lower = safe + early + binary
        upper = q4 + unique5 + multiple5
        slack = lower - upper
        require(min(q4, unique5, multiple5, slack) >= 0, f"finite row {g}")
        rows.append({
            "g": g,
            "raw_prefix": cap4["all"][g],
            "main_pivot_tail": omitted_pivot(g),
            "parent_pivot_tail": omitted_pivot(g - 1),
            "no_one": no_one(g),
            "sole_final_one": no_one(g - 3) + no_one(g - 4),
            "q4_upper": q4,
            "unique5_upper": unique5,
            "multiple5_upper": multiple5,
            "multiple5_method": "exact structural coefficients" if g <= 300 else "floor(113*(1000/633)^g)",
            "residual_upper": upper,
            "safe_lower": safe,
            "early_lower": early,
            "binary_lower": binary,
            "capacity_lower": lower,
            "slack": slack,
        })

    absolute_min = min(r["slack"] for r in rows)
    relative_capacity_min = min((Q(r["slack"], r["capacity_lower"]), r["g"]) for r in rows)
    relative_fib_min = min((Q(r["slack"], fib[r["g"]]), r["g"]) for r in rows)

    # Exact analytic tail comparison from Proposition mass:tail.
    q, sqrt5 = Q(309017, 500000), Q(223607, 100000)
    rstar, z4, z5 = Q(809, 500), Q(1247, 2000), Q(633, 1000)

    def analytic_upper(g: int) -> Q:
        return sqrt5 * (2024 * (q / z4) ** g + 113 * (q / z5) ** g) / (1 - q ** (2 * g))

    def analytic_capacity(g: int) -> Q:
        return 1 + Q(927, 500) - 50 * rstar * rstar / ((Q(63, 100) * rstar) ** g)

    analytic = {}
    for g in (836, 837):
        upper, lower = analytic_upper(g), analytic_capacity(g)
        gap = lower - upper
        analytic[str(g)] = {
            "source_upper_over_fibonacci": frac_record(upper),
            "capacity_lower_over_fibonacci": frac_record(lower),
            "capacity_minus_source": frac_record(gap),
            "relative_margin_over_capacity": frac_record(gap / lower),
            "passes": gap > 0,
        }
    require(not analytic["836"]["passes"] and analytic["837"]["passes"], "analytic join 836/837")

    transition_genera = (300, 301, 603, 604, 605, 836)
    transition_rows = {str(g): finite_row_record(rows[g - 1], fib[g]) for g in transition_genera}

    result = {
        "status": "PASS",
        "scope": "Exact revised Section 9 arithmetic: finite genera 1..836 and analytic join 836/837; no graph-classification rerun",
        "cap5_switch": {"exact_through": 300, "analytic_from": 301},
        "cap4_omitted_pivot_bound": {"main_enters": 604, "shifted_parent_enters": 605},
        "finite_rows_checked": 836,
        "all_finite_rows_nonnegative": True,
        "smallest_absolute_slack": absolute_min,
        "smallest_absolute_slack_genera": [r["g"] for r in rows if r["slack"] == absolute_min],
        "smallest_relative_margin_over_capacity": {"g": relative_capacity_min[1], **frac_record(relative_capacity_min[0])},
        "smallest_relative_margin_over_fibonacci": {"g": relative_fib_min[1], **frac_record(relative_fib_min[0])},
        "transition_rows": transition_rows,
        "analytic_transition": analytic,
        "fresh_replay_comparisons": replay,
        "input_sha256": {name: sha256(path) for name, path in paths.items()},
        "rows": [finite_row_record(r, fib[r["g"]]) for r in rows],
        "limits": [
            "Stored aggregate checking is not source regeneration.",
            "A coefficient match against a regenerated file checks the supplied generator, not a second implementation.",
            "The finite arithmetic does not by itself prove the combinatorial or analytic lemmas that connect these arrays to the theorem.",
        ],
    }
    output = args.output or script.with_name("finite-section-check.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("rows", "transition_rows", "analytic_transition")}, indent=2))


if __name__ == "__main__":
    main()
