from interval_bases import (
    Interval,
    consecutive_intervals,
    ell,
    ell_sharp,
    hfold_sumset,
    verify_pattern,
)


def test_hfold_sumset_allows_repetition() -> None:
    assert hfold_sumset({0, 1}, 2) == frozenset({0, 1, 2})


def test_consecutive_intervals_filters_singletons() -> None:
    assert consecutive_intervals({-2, 0, 1, 2, 5}, min_length=1) == (
        Interval(0, 2),
    )


def test_ell_and_ell_sharp_for_problem_7_counterexample() -> None:
    basis = {-1, 1, 2}
    assert ell(basis, 2) == 4
    assert ell_sharp(basis, 2) == 4


def test_verify_pattern_reports_an_extension() -> None:
    report = verify_pattern({0, 1}, 2, (0,), 1)
    assert not report.ok
    assert report.actual_nontrivial_intervals == (Interval(0, 2),)
    assert report.first_failure == "missing target interval Interval(start=0, end=1)"

