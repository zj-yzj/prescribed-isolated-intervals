"""Tools for experiments with interval additive bases."""

from .certificates import build_certificate, save_certificate
from .constructions import (
    IsolatedIntervalConstruction,
    SparseCrtSeparatedConstruction,
    SparsePairSeparatedConstruction,
    construct_isolated_intervals,
    construct_polynomial_isolated_intervals,
    construct_sparse_crt_separated_intervals,
    construct_sparse_pair_separated_intervals,
    construct_sidon_isolated_intervals,
)
from .core import (
    Interval,
    PatternVerification,
    consecutive_intervals,
    ell,
    ell_sharp,
    hfold_sumset,
    interval_starts_of_length,
    verify_pattern,
)

__all__ = [
    "Interval",
    "IsolatedIntervalConstruction",
    "PatternVerification",
    "SparseCrtSeparatedConstruction",
    "SparsePairSeparatedConstruction",
    "build_certificate",
    "consecutive_intervals",
    "construct_isolated_intervals",
    "construct_polynomial_isolated_intervals",
    "construct_sparse_crt_separated_intervals",
    "construct_sparse_pair_separated_intervals",
    "construct_sidon_isolated_intervals",
    "ell",
    "ell_sharp",
    "hfold_sumset",
    "interval_starts_of_length",
    "save_certificate",
    "verify_pattern",
]
