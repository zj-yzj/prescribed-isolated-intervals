"""Explicit constructions of signed interval bases."""

from __future__ import annotations

from dataclasses import dataclass
from math import isqrt
from typing import Sequence

from .core import Interval


@dataclass(frozen=True)
class IsolatedIntervalConstruction:
    """A set A whose h-fold sumset has exactly the requested nontrivial runs."""

    starts: tuple[int, ...]
    h: int
    n: int
    isolation_distance: int
    base: int
    target_radius: int
    scale: int
    label_scheme: str
    target_translation: int
    basis_translation: int
    relation_order: int
    labels: tuple[int, ...]
    positive_terms: tuple[int, ...]
    negative_terms: tuple[int, ...]
    values: tuple[int, ...]

    @property
    def target_intervals(self) -> tuple[Interval, ...]:
        return tuple(Interval(start, start + self.n) for start in self.starts)

    @property
    def cardinality(self) -> int:
        return len(self.values)

    @property
    def diameter(self) -> int:
        return self.values[-1] - self.values[0]

    @property
    def diameter_upper_bound(self) -> int:
        return self.h * self.labels[-1] + self.target_radius

    def to_dict(self) -> dict[str, object]:
        return {
            "starts": list(self.starts),
            "h": self.h,
            "n": self.n,
            "isolation_distance": self.isolation_distance,
            "base": self.base,
            "target_radius": self.target_radius,
            "scale": self.scale,
            "label_scheme": self.label_scheme,
            "target_translation": self.target_translation,
            "basis_translation": self.basis_translation,
            "relation_order": self.relation_order,
            "labels": list(self.labels),
            "positive_terms": list(self.positive_terms),
            "negative_terms": list(self.negative_terms),
            "values": list(self.values),
            "cardinality": self.cardinality,
            "diameter": self.diameter,
            "diameter_upper_bound": self.diameter_upper_bound,
            "target_intervals": [
                interval.to_dict() for interval in self.target_intervals
            ],
        }


@dataclass(frozen=True)
class SparsePairSeparatedConstruction:
    """Starts-only sparse construction for pair-sum separated starts."""

    starts: tuple[int, ...]
    n: int
    a: int
    b: int
    g: int
    u: int
    v: int
    r_bound: int
    s_bound: int
    pair_sum_gap: int
    minimum_shift: int
    shift: int
    x_packet: tuple[int, ...]
    y_packet: tuple[int, ...]
    values: tuple[int, ...]

    @property
    def h(self) -> int:
        return 2

    @property
    def target_intervals(self) -> tuple[Interval, ...]:
        return tuple(Interval(start, start + self.n) for start in self.starts)

    @property
    def cardinality(self) -> int:
        return len(self.values)

    @property
    def cardinality_upper_bound(self) -> int:
        return len(self.x_packet) + len(self.starts) * len(self.y_packet)

    @property
    def diameter(self) -> int:
        return self.values[-1] - self.values[0]

    def to_dict(self) -> dict[str, object]:
        return {
            "starts": list(self.starts),
            "h": self.h,
            "n": self.n,
            "a": self.a,
            "b": self.b,
            "g": self.g,
            "u": self.u,
            "v": self.v,
            "r_bound": self.r_bound,
            "s_bound": self.s_bound,
            "pair_sum_gap": self.pair_sum_gap,
            "minimum_shift": self.minimum_shift,
            "shift": self.shift,
            "x_packet": list(self.x_packet),
            "y_packet": list(self.y_packet),
            "values": list(self.values),
            "cardinality": self.cardinality,
            "cardinality_upper_bound": self.cardinality_upper_bound,
            "diameter": self.diameter,
            "target_intervals": [
                interval.to_dict() for interval in self.target_intervals
            ],
        }


def _normalized_starts(starts: Sequence[int]) -> tuple[int, ...]:
    normalized = tuple(sorted(set(starts)))
    if not normalized:
        raise ValueError("at least one start is required")
    if len(normalized) != len(starts):
        raise ValueError("starts must be distinct")
    return normalized


def _pair_sums(starts: Sequence[int]) -> tuple[int, ...]:
    return tuple(
        sorted(
            {
                left + right
                for index, left in enumerate(starts)
                for right in starts[index:]
            }
        )
    )


def _sparse_packet_parameters(n: int) -> tuple[int, int, int, int, int, int, int]:
    if n < 16:
        raise ValueError("n must be at least 16 for the sparse packet")
    a = isqrt(n) - 1
    b = a + 1
    g = a * (a - 1)
    n0 = n - (2 * a - 1)
    v = n0 % a
    u = (n0 - (a + 1) * v) // a
    if u < 0:
        raise AssertionError("sparse packet parameter u should be nonnegative")
    r_bound = a + u
    s_bound = a - 1 + v
    return a, b, g, u, v, r_bound, s_bound


def construct_isolated_intervals(
    starts: Sequence[int],
    n: int,
    isolation_distance: int = 2,
    *,
    h: int = 2,
    base: int | None = None,
) -> IsolatedIntervalConstruction:
    """Construct A so the only nontrivial runs in hA are [c, c+n].

    The starts must be distinct and separated by at least n + 2. For each target
    point t, assign a label a and include both t + (h - 1) * a and -a. One
    positive label and h - 1 matching negative labels cancel to t. Positional
    separation keeps every unmatched sum isolated.
    """

    if n < 1:
        raise ValueError("n must be positive")
    if h < 2:
        raise ValueError("h must be at least 2")
    if isolation_distance < 2:
        raise ValueError("isolation_distance must be at least 2")
    minimum_base = 2 * h * (h - 1)
    selected_base = minimum_base if base is None else base
    if selected_base < minimum_base:
        raise ValueError(f"base must be at least {minimum_base} when h={h}")

    normalized_starts = _normalized_starts(starts)
    if any(
        right - left < n + 2
        for left, right in zip(normalized_starts, normalized_starts[1:])
    ):
        raise ValueError("consecutive starts must differ by at least n + 2")

    target_points = tuple(
        start + offset for start in normalized_starts for offset in range(n + 1)
    )
    target_radius = max(abs(point) for point in target_points)
    scale = 2 * h * target_radius + isolation_distance
    labels = tuple(
        scale * selected_base**index for index in range(len(target_points))
    )
    positive_terms = tuple(
        point + (h - 1) * label for point, label in zip(target_points, labels)
    )
    negative_terms = tuple(-label for label in labels)
    values = tuple(sorted((*positive_terms, *negative_terms)))

    if len(set(values)) != 2 * len(target_points):
        raise AssertionError("construction produced duplicate elements")

    return IsolatedIntervalConstruction(
        starts=normalized_starts,
        h=h,
        n=n,
        isolation_distance=isolation_distance,
        base=selected_base,
        target_radius=target_radius,
        scale=scale,
        label_scheme="powers",
        target_translation=0,
        basis_translation=0,
        relation_order=2 * h * (h - 1),
        labels=labels,
        positive_terms=positive_terms,
        negative_terms=negative_terms,
        values=values,
    )


def _nearest_multiple_to_midpoint(points: Sequence[int], modulus: int) -> int:
    """Choose a multiple of modulus minimizing the radius of translated points."""

    doubled_midpoint = min(points) + max(points)
    quotient = doubled_midpoint // (2 * modulus)
    candidates = tuple(modulus * (quotient + offset) for offset in (-1, 0, 1, 2))
    return min(
        candidates,
        key=lambda candidate: (
            max(abs(point - candidate) for point in points),
            abs(candidate),
            candidate,
        ),
    )


def _moment_labels(count: int, h: int, scale: int) -> tuple[int, int, tuple[int, ...]]:
    """Return polynomial-size labels separating all relevant coefficient vectors."""

    relation_order = 2 * h * (h - 1)
    maximum_index = max(1, count - 1)
    moment_bound = relation_order * maximum_index ** (relation_order - 1)
    encoding_base = relation_order * moment_bound
    labels = tuple(
        scale
        * sum(
            index**power * encoding_base**power
            for power in range(relation_order)
        )
        for index in range(count)
    )
    return encoding_base, relation_order, labels


def _is_prime(value: int) -> bool:
    """Return whether value is prime."""

    if value < 2:
        return False
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 1
    return True


def _least_odd_prime_at_least(value: int) -> int:
    """Return the least odd prime greater than or equal to value."""

    candidate = max(3, value)
    if candidate % 2 == 0:
        candidate += 1
    while not _is_prime(candidate):
        candidate += 2
    return candidate


def _sidon_labels(count: int, scale: int) -> tuple[int, tuple[int, ...]]:
    """Return quadratic-size labels separating all relations of l1 norm at most 4."""

    prime = _least_odd_prime_at_least(count)
    translation = 2 * prime * prime
    labels = tuple(
        scale * (translation + 2 * prime * index + index * index % prime)
        for index in range(count)
    )
    return prime, labels


def construct_sidon_isolated_intervals(
    starts: Sequence[int],
    n: int,
    isolation_distance: int = 2,
) -> IsolatedIntervalConstruction:
    """Construct isolated intervals in 2A using quadratic-size Sidon labels."""

    if n < 1:
        raise ValueError("n must be positive")
    if isolation_distance < 2:
        raise ValueError("isolation_distance must be at least 2")

    normalized_starts = _normalized_starts(starts)
    if any(
        right - left < n + 2
        for left, right in zip(normalized_starts, normalized_starts[1:])
    ):
        raise ValueError("consecutive starts must differ by at least n + 2")

    h = 2
    target_points = tuple(
        start + offset for start in normalized_starts for offset in range(n + 1)
    )
    target_translation = _nearest_multiple_to_midpoint(target_points, h)
    basis_translation = target_translation // h
    centered_target_points = tuple(
        point - target_translation for point in target_points
    )
    target_radius = max(abs(point) for point in centered_target_points)
    scale = 2 * h * target_radius + isolation_distance
    prime, labels = _sidon_labels(len(target_points), scale)
    positive_terms = tuple(
        point + label + basis_translation
        for point, label in zip(centered_target_points, labels)
    )
    negative_terms = tuple(-label + basis_translation for label in labels)
    values = tuple(sorted((*positive_terms, *negative_terms)))

    if len(set(values)) != 2 * len(target_points):
        raise AssertionError("construction produced duplicate elements")

    return IsolatedIntervalConstruction(
        starts=normalized_starts,
        h=h,
        n=n,
        isolation_distance=isolation_distance,
        base=prime,
        target_radius=target_radius,
        scale=scale,
        label_scheme="sidon",
        target_translation=target_translation,
        basis_translation=basis_translation,
        relation_order=4,
        labels=labels,
        positive_terms=positive_terms,
        negative_terms=negative_terms,
        values=values,
    )


def construct_polynomial_isolated_intervals(
    starts: Sequence[int],
    n: int,
    isolation_distance: int = 2,
    *,
    h: int = 2,
) -> IsolatedIntervalConstruction:
    """Construct isolated intervals using polynomial-size moment labels.

    For fixed h, the largest label is polynomial rather than exponential in
    the number of target points. A translation by a multiple of h centers the
    target pattern without changing the diameter of the resulting basis.
    """

    if n < 1:
        raise ValueError("n must be positive")
    if h < 2:
        raise ValueError("h must be at least 2")
    if isolation_distance < 2:
        raise ValueError("isolation_distance must be at least 2")

    normalized_starts = _normalized_starts(starts)
    if any(
        right - left < n + 2
        for left, right in zip(normalized_starts, normalized_starts[1:])
    ):
        raise ValueError("consecutive starts must differ by at least n + 2")

    target_points = tuple(
        start + offset for start in normalized_starts for offset in range(n + 1)
    )
    target_translation = _nearest_multiple_to_midpoint(target_points, h)
    basis_translation = target_translation // h
    centered_target_points = tuple(
        point - target_translation for point in target_points
    )
    target_radius = max(abs(point) for point in centered_target_points)
    scale = 2 * h * target_radius + isolation_distance
    encoding_base, relation_order, labels = _moment_labels(
        len(target_points), h, scale
    )
    positive_terms = tuple(
        point + (h - 1) * label + basis_translation
        for point, label in zip(centered_target_points, labels)
    )
    negative_terms = tuple(-label + basis_translation for label in labels)
    values = tuple(sorted((*positive_terms, *negative_terms)))

    if len(set(values)) != 2 * len(target_points):
        raise AssertionError("construction produced duplicate elements")

    return IsolatedIntervalConstruction(
        starts=normalized_starts,
        h=h,
        n=n,
        isolation_distance=isolation_distance,
        base=encoding_base,
        target_radius=target_radius,
        scale=scale,
        label_scheme="moments",
        target_translation=target_translation,
        basis_translation=basis_translation,
        relation_order=relation_order,
        labels=labels,
        positive_terms=positive_terms,
        negative_terms=negative_terms,
        values=values,
    )


def construct_sparse_pair_separated_intervals(
    starts: Sequence[int],
    n: int,
    *,
    shift: int | None = None,
) -> SparsePairSeparatedConstruction:
    """Construct a starts-only sparse double-sumset pattern.

    The starts must satisfy the pair-sum separation hypothesis from the paper:
    distinct elements of C+C are separated by at least
    max(n + 2g + 2, 2Sb + 2).
    """

    normalized_starts = _normalized_starts(starts)
    a, b, g, u, v, r_bound, s_bound = _sparse_packet_parameters(n)
    pair_sum_gap = max(n + 2 * g + 2, 2 * s_bound * b + 2)

    pair_sums = _pair_sums(normalized_starts)
    if any(
        right - left < pair_sum_gap
        for left, right in zip(pair_sums, pair_sums[1:])
    ):
        raise ValueError(
            "distinct pair sums must differ by at least "
            f"{pair_sum_gap} for this sparse construction"
        )

    x_packet = tuple(index * a for index in range(r_bound + 1))
    y_packet = tuple(index * b for index in range(s_bound + 1))
    cross_max = max(normalized_starts) + n + g
    cross_min = min(normalized_starts) - g
    pair_max = max(pair_sums)
    lower_from_cross_to_x = (cross_max + 3) // 2
    lower_from_y_to_cross = (
        pair_max - 2 * g + 2 * s_bound * b - cross_min + 3
    ) // 2
    minimum_shift = max(1, lower_from_cross_to_x, lower_from_y_to_cross)
    if shift is None:
        shift = minimum_shift
    elif shift < minimum_shift:
        raise ValueError(f"shift must be at least {minimum_shift}")

    values = {shift + term for term in x_packet}
    for start in normalized_starts:
        values.update(start - g - shift + term for term in y_packet)

    return SparsePairSeparatedConstruction(
        starts=normalized_starts,
        n=n,
        a=a,
        b=b,
        g=g,
        u=u,
        v=v,
        r_bound=r_bound,
        s_bound=s_bound,
        pair_sum_gap=pair_sum_gap,
        minimum_shift=minimum_shift,
        shift=shift,
        x_packet=x_packet,
        y_packet=y_packet,
        values=tuple(sorted(values)),
    )
