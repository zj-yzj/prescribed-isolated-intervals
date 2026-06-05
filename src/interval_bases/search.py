"""Finite searches for classical and signed interval bases."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from math import comb
from typing import Iterable

from .core import ell, ell_sharp


# OEIS A001208: best h-range with three positive denominations and h stamps.
# In this package that is n_h(4), because zero is also included in the basis.
OEIS_A001208_THREE_DENOMINATIONS = {
    1: 3,
    2: 8,
    3: 15,
    4: 26,
    5: 35,
    6: 52,
}

# OEIS A001209: best h-range with four positive denominations and h stamps.
# In this package that is n_h(5), because zero is also included in the basis.
OEIS_A001209_FOUR_DENOMINATIONS = {
    1: 4,
    2: 12,
    3: 24,
    4: 44,
    5: 71,
    6: 114,
}


@dataclass(frozen=True)
class Extremum:
    value: int
    witness: tuple[int, ...]

    def to_dict(self) -> dict[str, object]:
        return {"value": self.value, "witness": list(self.witness)}


@dataclass(frozen=True)
class WindowScan:
    h: int
    k: int
    lower_bound: int
    upper_bound: int
    sets_checked: int
    best_prefix: Extremum
    best_interval: Extremum

    def to_dict(self) -> dict[str, object]:
        return {
            "h": self.h,
            "k": self.k,
            "lower_bound": self.lower_bound,
            "upper_bound": self.upper_bound,
            "sets_checked": self.sets_checked,
            "best_prefix": self.best_prefix.to_dict(),
            "best_interval": self.best_interval.to_dict(),
        }


def postage_stamp_counting_upper_bound(h: int, k: int) -> int:
    """Upper bound for n_h(k) from the number of unordered h-term sums."""

    if h < 1 or k < 1:
        raise ValueError("h and k must be positive")
    return comb(h + k - 1, k - 1) - 1


def _best(current: Extremum, value: int, witness: Iterable[int]) -> Extremum:
    normalized = tuple(witness)
    if value > current.value:
        return Extremum(value, normalized)
    return current


def enumerate_exact_prefix_extremum(h: int, k: int) -> Extremum:
    """Compute n_h(k) exactly by an exhaustive finite search.

    An extremal nonnegative basis can be taken inside [0, n_h(k)]. The
    counting bound therefore supplies a finite search window. For k >= 2 an
    extremal basis contains 0 and 1.
    """

    if h < 1 or k < 1:
        raise ValueError("h and k must be positive")
    if k == 1:
        return Extremum(0, (0,))

    upper_bound = postage_stamp_counting_upper_bound(h, k)
    best = Extremum(-1, ())
    for tail in combinations(range(2, upper_bound + 1), k - 2):
        basis = (0, 1, *tail)
        best = _best(best, ell(basis, h), basis)
    return best


def scan_nonnegative_window(h: int, k: int, max_element: int) -> WindowScan:
    """Scan k-element subsets of [0, max_element] that include zero."""

    if h < 1 or k < 1:
        raise ValueError("h and k must be positive")
    if max_element < 0:
        raise ValueError("max_element must be nonnegative")

    best_prefix = Extremum(-1, ())
    best_interval = Extremum(-1, ())
    checked = 0
    for tail in combinations(range(1, max_element + 1), k - 1):
        basis = (0, *tail)
        best_prefix = _best(best_prefix, ell(basis, h), basis)
        best_interval = _best(best_interval, ell_sharp(basis, h), basis)
        checked += 1
    return WindowScan(
        h=h,
        k=k,
        lower_bound=0,
        upper_bound=max_element,
        sets_checked=checked,
        best_prefix=best_prefix,
        best_interval=best_interval,
    )


def scan_signed_window(
    h: int, k: int, min_element: int, max_element: int
) -> WindowScan:
    """Scan signed k-element subsets in a finite window with a negative term."""

    if h < 1 or k < 1:
        raise ValueError("h and k must be positive")
    if min_element >= 0:
        raise ValueError("min_element must be negative")
    if max_element < 0:
        raise ValueError("max_element must be nonnegative")

    best_prefix = Extremum(-1, ())
    best_interval = Extremum(-1, ())
    checked = 0
    for basis in combinations(range(min_element, max_element + 1), k):
        if basis[0] >= 0:
            break
        best_prefix = _best(best_prefix, ell(basis, h), basis)
        best_interval = _best(best_interval, ell_sharp(basis, h), basis)
        checked += 1
    return WindowScan(
        h=h,
        k=k,
        lower_bound=min_element,
        upper_bound=max_element,
        sets_checked=checked,
        best_prefix=best_prefix,
        best_interval=best_interval,
    )


def check_oeis_values(max_stamps: int = 3) -> list[dict[str, object]]:
    """Return exact computations alongside selected OEIS postage-stamp values."""

    if max_stamps < 1:
        raise ValueError("max_stamps must be positive")
    checks: list[dict[str, object]] = []
    sequences = (
        ("A001208", 4, OEIS_A001208_THREE_DENOMINATIONS),
        ("A001209", 5, OEIS_A001209_FOUR_DENOMINATIONS),
    )
    for oeis_id, k, expected_values in sequences:
        for h in range(1, min(max_stamps, max(expected_values)) + 1):
            computed = enumerate_exact_prefix_extremum(h, k)
            expected = expected_values[h]
            checks.append(
                {
                    "oeis_id": oeis_id,
                    "h": h,
                    "k": k,
                    "expected": expected,
                    "computed": computed.value,
                    "witness": list(computed.witness),
                    "ok": computed.value == expected,
                }
            )
    return checks

