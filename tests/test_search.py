from interval_bases.search import (
    check_oeis_values,
    enumerate_exact_prefix_extremum,
    postage_stamp_counting_upper_bound,
    scan_signed_window,
)


def test_counting_upper_bound() -> None:
    assert postage_stamp_counting_upper_bound(2, 3) == 5


def test_exact_prefix_extremum_small_case() -> None:
    result = enumerate_exact_prefix_extremum(2, 3)
    assert result.value == 4
    assert result.witness == (0, 1, 2)


def test_problem_7_strict_inequality_counterexample_is_found() -> None:
    result = scan_signed_window(2, 3, -3, 4)
    assert result.best_prefix.value == 4
    assert result.best_prefix.witness == (-1, 1, 2)


def test_selected_oeis_values() -> None:
    checks = check_oeis_values(max_stamps=3)
    assert checks
    assert all(check["ok"] for check in checks)

