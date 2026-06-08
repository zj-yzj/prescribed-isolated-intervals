import random
from itertools import product

import pytest

from interval_bases import (
    build_certificate,
    construct_isolated_intervals,
    construct_polynomial_isolated_intervals,
    construct_sparse_pair_separated_intervals,
    construct_sidon_isolated_intervals,
    interval_starts_of_length,
    save_certificate,
    verify_pattern,
)


def test_single_interval_construction() -> None:
    construction = construct_isolated_intervals((7,), 3, 4)
    report = verify_pattern(construction.values, 2, construction.starts, construction.n)

    assert report.ok
    assert construction.cardinality == 8
    assert construction.diameter <= construction.diameter_upper_bound


def test_multiple_interval_construction_certificate() -> None:
    construction = construct_isolated_intervals((-10, 0, 15), 3, 5)
    certificate = build_certificate(construction, include_sumset=True)

    assert certificate["verification"]["ok"]
    assert certificate["construction"]["cardinality"] == 24
    assert certificate["statistics"]["minimum_exceptional_spacing"] >= 5
    assert certificate["statistics"]["minimum_exceptional_to_target_distance"] >= 5


def test_higher_order_construction_certificate() -> None:
    construction = construct_isolated_intervals((-6, 2), 2, 3, h=4)
    certificate = build_certificate(construction)

    assert certificate["verification"]["ok"]
    assert certificate["construction"]["h"] == 4
    assert certificate["construction"]["cardinality"] == 12
    assert certificate["statistics"]["minimum_exceptional_spacing"] >= 3
    assert certificate["statistics"]["minimum_exceptional_to_target_distance"] >= 3


def test_certificate_can_be_saved(tmp_path) -> None:
    construction = construct_isolated_intervals((0, 8), 2)
    output = tmp_path / "certificate.json"
    certificate = save_certificate(output, construction)

    assert output.exists()
    assert certificate["verification"]["ok"]


def test_close_starts_are_rejected() -> None:
    with pytest.raises(ValueError, match="differ by at least"):
        construct_isolated_intervals((0, 3), 2)


def test_random_small_constructions() -> None:
    randomizer = random.Random(20260602)
    for _ in range(16):
        n = randomizer.randint(1, 3)
        q = randomizer.randint(1, 3)
        starts = [randomizer.randint(-12, 0)]
        for _ in range(q - 1):
            starts.append(starts[-1] + n + 2 + randomizer.randint(0, 4))
        distance = randomizer.randint(2, 5)
        h = randomizer.randint(2, 5)
        construction = construct_isolated_intervals(starts, n, distance, h=h)
        certificate = build_certificate(construction)

        assert certificate["verification"]["ok"]
        assert (
            certificate["statistics"]["minimum_exceptional_to_target_distance"]
            >= distance
        )
        assert certificate["statistics"]["minimum_exceptional_spacing"] >= distance


def test_polynomial_label_construction_with_large_translation() -> None:
    construction = construct_polynomial_isolated_intervals((1_000_000,), 3, 4)
    certificate = build_certificate(construction)

    assert certificate["verification"]["ok"]
    assert construction.label_scheme == "moments"
    assert construction.target_translation % construction.h == 0
    assert construction.target_radius <= 2
    assert certificate["statistics"]["minimum_exceptional_spacing"] >= 4
    assert certificate["statistics"]["minimum_exceptional_to_target_distance"] >= 4


def test_polynomial_label_higher_order_construction() -> None:
    construction = construct_polynomial_isolated_intervals((-9, 1), 1, 3, h=3)
    certificate = build_certificate(construction)

    assert certificate["verification"]["ok"]
    assert construction.relation_order == 12
    assert certificate["statistics"]["minimum_exceptional_spacing"] >= 3
    assert certificate["statistics"]["minimum_exceptional_to_target_distance"] >= 3


def test_moment_labels_separate_relevant_small_vectors() -> None:
    construction = construct_polynomial_isolated_intervals((0,), 2, h=2)
    relation_order = construction.relation_order

    for coefficients in product(range(-relation_order, relation_order + 1), repeat=3):
        if not any(coefficients) or sum(abs(value) for value in coefficients) > relation_order:
            continue
        encoded = sum(
            coefficient * label
            for coefficient, label in zip(coefficients, construction.labels)
        )
        assert abs(encoded) >= construction.scale


def test_sidon_label_construction_with_large_translation() -> None:
    construction = construct_sidon_isolated_intervals((1_000_000,), 3, 4)
    certificate = build_certificate(construction)

    assert certificate["verification"]["ok"]
    assert construction.label_scheme == "sidon"
    assert construction.h == 2
    assert construction.base == 5
    assert construction.target_radius <= 2
    assert certificate["statistics"]["minimum_exceptional_spacing"] >= 4
    assert certificate["statistics"]["minimum_exceptional_to_target_distance"] >= 4


def test_sidon_labels_separate_relevant_small_vectors() -> None:
    construction = construct_sidon_isolated_intervals((0,), 2)

    for coefficients in product(range(-4, 5), repeat=3):
        if not any(coefficients) or sum(abs(value) for value in coefficients) > 4:
            continue
        encoded = sum(
            coefficient * label
            for coefficient, label in zip(coefficients, construction.labels)
        )
        assert abs(encoded) >= construction.scale


def test_sparse_pair_separated_multi_interval_model() -> None:
    construction = construct_sparse_pair_separated_intervals((0, 50, 150), 16)

    assert construction.cardinality <= construction.cardinality_upper_bound
    assert construction.cardinality_upper_bound == 20
    assert interval_starts_of_length(construction.values, 2, 16) == (0, 50, 150)


def test_sparse_pair_separated_rejects_close_pair_sums() -> None:
    with pytest.raises(ValueError, match="distinct pair sums"):
        construct_sparse_pair_separated_intervals((0, 20, 60), 16)


def test_sparse_pair_separated_rejects_small_shift() -> None:
    construction = construct_sparse_pair_separated_intervals((0, 50, 150), 16)

    with pytest.raises(ValueError, match="shift must be at least"):
        construct_sparse_pair_separated_intervals(
            (0, 50, 150), 16, shift=construction.minimum_shift - 1
        )
