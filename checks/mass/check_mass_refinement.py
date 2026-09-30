"""Verify the final finite-difference refinement and analytic join exactly."""
import contextlib
import io
import itertools
import json
from fractions import Fraction as F

with contextlib.redirect_stdout(io.StringIO()):
    import check_mass as c

J = (c.L * c.w) ** 2
c.require(0 < J < 1, "rounded normalization")


def H(theta):
    A = c.eta / theta**2
    B = c.eta * c.L**4 * theta**2
    return sum(
        (
            c.L ** (2 * v)
            * theta ** (v - u)
            * c.tail_strip(A, B, c.sigma, u, v, 100)
            for u, v in itertools.product((1, 2), repeat=2)
        ),
        F(0),
    )


first, second, third = H(c.cube), H(c.cube * J), H(c.cube * J * J)
c.require(first > second > third > 0, "positive successive finite differences")
prefactor = c.prefactor * (1 + c.L) * c.L**-2 * c.T / c.eta
mu2 = c.tmu * c.tmu
mixed = prefactor / (1 - J) * (
    (first - second) + mu2 / (1 - mu2) * (second - third)
)
total = c.mass - c.pieces["mixed_tail_100"] + mixed
c.require(0 < mixed < c.pieces["mixed_tail_100"] and total < 2024, "mass bound")

r = F(809, 500)
c.require(r * r < r + 1 and F(63, 100) * r > 1, "capacity scalar decay")


def capacity(g):
    return 1 - 50 * r * r / (F(63, 100) * r) ** g + F(927, 500)


def ratio(g):
    return c.sqrt5up * (
        2024 * (c.qup / c.z) ** g + 113 * (c.qup / c.z5) ** g
    ) / (1 - c.qup ** (2 * g))


c.require(ratio(837) < capacity(837) and ratio(836) > capacity(836), "analytic join")
report = {
    "status": "PASS exact mass-2024 refinement and analytic join",
    "J": str(J),
    "mixed_upper_ceiling": c.upper(mixed),
    "total_mass_upper_ceiling": c.upper(total),
    "integer_mass_bound": 2024,
    "analytic_cutoff": 837,
    "ratio_837_upper_ceiling": c.upper(ratio(837)),
    "capacity_837_lower_floor": str(-F(c.upper(-capacity(837)))),
    "ratio_836_upper_ceiling": c.upper(ratio(836)),
}
(c.HERE / "check_mass_refinement.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
