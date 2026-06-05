"""Tools for experiments with interval additive bases."""

from .certificates import build_certificate, save_certificate
from .constructions import (
    IsolatedIntervalConstruction,
    construct_isolated_intervals,
    construct_polynomial_isolated_intervals,
    construct_sidon_isolated_intervals,
)
from .core import (
    Interval,
    PatternVerification,
    consecutive_intervals,
    ell,
    ell_sharp,
    hfold_sumset,
    verify_pattern,
)

__all__ = [
    "Interval",
    "IsolatedIntervalConstruction",
    "PatternVerification",
    "build_certificate",
    "consecutive_intervals",
    "construct_isolated_intervals",
    "construct_polynomial_isolated_intervals",
    "construct_sidon_isolated_intervals",
    "ell",
    "ell_sharp",
    "hfold_sumset",
    "save_certificate",
    "verify_pattern",
]
