"""Serializable verification certificates for explicit constructions."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Iterable

from .constructions import IsolatedIntervalConstruction
from .core import hfold_sumset, verify_pattern


def _minimum_spacing(values: Iterable[int]) -> int | None:
    ordered = sorted(set(values))
    if len(ordered) < 2:
        return None
    return min(right - left for left, right in zip(ordered, ordered[1:]))


def _minimum_cross_distance(left: Iterable[int], right: Iterable[int]) -> int | None:
    ordered_left = sorted(set(left))
    ordered_right = sorted(set(right))
    if not ordered_left or not ordered_right:
        return None

    i = j = 0
    minimum: int | None = None
    while i < len(ordered_left) and j < len(ordered_right):
        distance = abs(ordered_left[i] - ordered_right[j])
        minimum = distance if minimum is None else min(minimum, distance)
        if ordered_left[i] < ordered_right[j]:
            i += 1
        else:
            j += 1
    return minimum


def _digest(values: Iterable[int]) -> str:
    payload = json.dumps(sorted(set(values)), separators=(",", ":")).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def build_certificate(
    construction: IsolatedIntervalConstruction, *, include_sumset: bool = False
) -> dict[str, object]:
    """Recompute hA and return a JSON-serializable verification certificate."""

    sums = hfold_sumset(construction.values, construction.h)
    target_points = {
        point
        for interval in construction.target_intervals
        for point in interval.points()
    }
    exceptional_points = sums - target_points
    verification = verify_pattern(
        construction.values, construction.h, construction.starts, construction.n
    )

    result: dict[str, object] = {
        "schema_version": 1,
        "construction": construction.to_dict(),
        "verification": verification.to_dict(include_isolated_points=False),
        "statistics": {
            "sumset_cardinality": len(sums),
            "sumset_sha256": _digest(sums),
            "target_point_count": len(target_points),
            "exceptional_point_count": len(exceptional_points),
            "minimum_exceptional_spacing": _minimum_spacing(exceptional_points),
            "minimum_exceptional_to_target_distance": _minimum_cross_distance(
                exceptional_points, target_points
            ),
        },
    }
    if include_sumset:
        result["sumset"] = sorted(sums)
        result["exceptional_points"] = sorted(exceptional_points)
    return result


def save_certificate(
    path: str | Path,
    construction: IsolatedIntervalConstruction,
    *,
    include_sumset: bool = False,
) -> dict[str, object]:
    """Write a construction certificate and return its contents."""

    certificate = build_certificate(construction, include_sumset=include_sumset)
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return certificate
