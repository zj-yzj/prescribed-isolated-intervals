"""Core sumset and interval operations."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Iterable, Sequence


@dataclass(frozen=True, order=True)
class Interval:
    """A closed integer interval [start, end]."""

    start: int
    end: int

    def __post_init__(self) -> None:
        if self.end < self.start:
            raise ValueError("interval end must not be smaller than its start")

    @property
    def length(self) -> int:
        """Nathanson's interval length: end - start."""

        return self.end - self.start

    @property
    def size(self) -> int:
        return self.length + 1

    def points(self) -> range:
        return range(self.start, self.end + 1)

    def to_dict(self) -> dict[str, int]:
        return asdict(self)


@dataclass(frozen=True)
class PatternVerification:
    """Comparison between expected intervals and the nontrivial runs in hA."""

    ok: bool
    h: int
    expected_intervals: tuple[Interval, ...]
    actual_nontrivial_intervals: tuple[Interval, ...]
    unexpected_intervals: tuple[Interval, ...]
    missing_intervals: tuple[Interval, ...]
    missing_target_points: tuple[int, ...]
    isolated_exceptional_points: tuple[int, ...]
    first_failure: str | None

    def to_dict(self, *, include_isolated_points: bool = True) -> dict[str, object]:
        result: dict[str, object] = {
            "ok": self.ok,
            "h": self.h,
            "expected_intervals": [
                interval.to_dict() for interval in self.expected_intervals
            ],
            "actual_nontrivial_intervals": [
                interval.to_dict() for interval in self.actual_nontrivial_intervals
            ],
            "unexpected_intervals": [
                interval.to_dict() for interval in self.unexpected_intervals
            ],
            "missing_intervals": [
                interval.to_dict() for interval in self.missing_intervals
            ],
            "missing_target_points": list(self.missing_target_points),
            "isolated_exceptional_point_count": len(self.isolated_exceptional_points),
            "first_failure": self.first_failure,
        }
        if include_isolated_points:
            result["isolated_exceptional_points"] = list(
                self.isolated_exceptional_points
            )
        return result


def _as_sorted_unique_tuple(values: Iterable[int]) -> tuple[int, ...]:
    return tuple(sorted(set(values)))


def hfold_sumset(values: Iterable[int], h: int) -> frozenset[int]:
    """Return all sums of exactly h terms, with repetition allowed."""

    if h < 1:
        raise ValueError("h must be positive")
    terms = tuple(set(values))
    if not terms:
        return frozenset()

    sums = {0}
    for _ in range(h):
        sums = {subtotal + term for subtotal in sums for term in terms}
    return frozenset(sums)


def consecutive_intervals(
    values: Iterable[int], *, min_length: int = 0
) -> tuple[Interval, ...]:
    """Return maximal consecutive runs with end - start >= min_length."""

    if min_length < 0:
        raise ValueError("min_length must be nonnegative")
    ordered = _as_sorted_unique_tuple(values)
    if not ordered:
        return ()

    intervals: list[Interval] = []
    start = previous = ordered[0]
    for value in ordered[1:]:
        if value != previous + 1:
            interval = Interval(start, previous)
            if interval.length >= min_length:
                intervals.append(interval)
            start = value
        previous = value

    interval = Interval(start, previous)
    if interval.length >= min_length:
        intervals.append(interval)
    return tuple(intervals)


def ell(values: Iterable[int], h: int) -> int:
    """Return the largest n with [0, n] contained in hA, or -1 if 0 is absent."""

    sums = hfold_sumset(values, h)
    n = 0
    while n in sums:
        n += 1
    return n - 1


def ell_sharp(values: Iterable[int], h: int) -> int:
    """Return the largest length of a consecutive interval contained in hA."""

    intervals = consecutive_intervals(hfold_sumset(values, h))
    return max((interval.length for interval in intervals), default=-1)


def verify_pattern(
    values: Iterable[int], h: int, starts: Sequence[int], n: int
) -> PatternVerification:
    """Verify that the only nontrivial maximal runs in hA are [c, c+n]."""

    if n < 1:
        raise ValueError("n must be positive")
    normalized_starts = tuple(sorted(set(starts)))
    if len(normalized_starts) != len(starts):
        raise ValueError("starts must be distinct")

    expected = tuple(Interval(start, start + n) for start in normalized_starts)
    sums = hfold_sumset(values, h)
    actual = consecutive_intervals(sums, min_length=1)
    expected_set = set(expected)
    actual_set = set(actual)
    unexpected = tuple(interval for interval in actual if interval not in expected_set)
    missing = tuple(interval for interval in expected if interval not in actual_set)
    target_points = {point for interval in expected for point in interval.points()}
    missing_points = tuple(sorted(target_points - sums))
    all_runs = consecutive_intervals(sums)
    isolated_exceptions = tuple(
        interval.start
        for interval in all_runs
        if interval.length == 0 and interval.start not in target_points
    )

    failures: list[str] = []
    if missing_points:
        failures.append(f"missing target point {missing_points[0]}")
    if missing:
        failures.append(f"missing target interval {missing[0]}")
    if unexpected:
        failures.append(f"unexpected nontrivial interval {unexpected[0]}")

    return PatternVerification(
        ok=not failures,
        h=h,
        expected_intervals=expected,
        actual_nontrivial_intervals=actual,
        unexpected_intervals=unexpected,
        missing_intervals=missing,
        missing_target_points=missing_points,
        isolated_exceptional_points=isolated_exceptions,
        first_failure=failures[0] if failures else None,
    )
