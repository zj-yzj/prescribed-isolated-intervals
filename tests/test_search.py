from interval_bases.search import (
    check_oeis_values,
    enumerate_exact_prefix_extremum,
    postage_stamp_counting_upper_bound,
    scan_signed_window,
    scan_strong_single_interval_minima,
)


def test_counting_upper_bound() -> None:
    assert postage_stamp_counting_upper_bound(2, 3) == 5


def test_exact_prefix_extremum_small_case() -> None:
    result = enumerate_exact_prefix_extremum(2, 3)
    assert result.value == 4
    assert result.witness == (0, 1, 2)


def test_signed_window_finds_affine_extremal_example() -> None:
    result = scan_signed_window(2, 3, -3, 4)
    assert result.best_prefix.value == 4
    assert result.best_prefix.witness == (-1, 1, 2)


def test_selected_oeis_values() -> None:
    checks = check_oeis_values(max_stamps=3)
    assert checks
    assert all(check["ok"] for check in checks)


def test_strong_single_interval_scan_small_lengths() -> None:
    results = scan_strong_single_interval_minima(6, 5, 12)
    minima = {result.interval_length: result.k for result in results}
    assert minima == {
        1: 3,
        2: 2,
        3: 4,
        4: 3,
        5: 5,
        6: 4,
    }
    assert results[3].witness == (0, 1, 2)
    assert results[3].interval is not None
    assert results[3].interval.length == 4
