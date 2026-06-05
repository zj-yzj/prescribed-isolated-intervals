"""Command-line interface for reproducible interval-basis experiments."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from .certificates import build_certificate, save_certificate
from .constructions import (
    construct_isolated_intervals,
    construct_polynomial_isolated_intervals,
    construct_sidon_isolated_intervals,
)
from .search import (
    check_oeis_values,
    enumerate_exact_prefix_extremum,
    scan_nonnegative_window,
    scan_signed_window,
)


def _parse_starts(value: str) -> tuple[int, ...]:
    try:
        starts = tuple(int(part.strip()) for part in value.split(",") if part.strip())
    except ValueError as error:
        raise argparse.ArgumentTypeError("starts must be comma-separated integers") from error
    if not starts:
        raise argparse.ArgumentTypeError("at least one start is required")
    return starts


def _print_json(value: object) -> None:
    print(json.dumps(value, indent=2, sort_keys=True))


def _construct(args: argparse.Namespace) -> int:
    if args.scheme == "powers":
        construction = construct_isolated_intervals(
            args.starts, args.length, args.distance, h=args.h, base=args.base
        )
    elif args.scheme == "moments":
        if args.base is not None:
            raise ValueError("--base is only available for the powers scheme")
        construction = construct_polynomial_isolated_intervals(
            args.starts, args.length, args.distance, h=args.h
        )
    else:
        if args.base is not None:
            raise ValueError("--base is only available for the powers scheme")
        if args.h != 2:
            raise ValueError("the sidon scheme is only available when h=2")
        construction = construct_sidon_isolated_intervals(
            args.starts, args.length, args.distance
        )
    if args.output:
        certificate = save_certificate(
            args.output, construction, include_sumset=args.include_sumset
        )
        print(f"wrote {Path(args.output).resolve()}")
    else:
        certificate = build_certificate(
            construction, include_sumset=args.include_sumset
        )
    _print_json(certificate)
    return 0 if certificate["verification"]["ok"] else 1


def _scan(args: argparse.Namespace) -> int:
    exact_prefix = enumerate_exact_prefix_extremum(args.h, args.k)
    nonnegative = scan_nonnegative_window(args.h, args.k, args.max_element)
    result: dict[str, object] = {
        "exact_prefix": exact_prefix.to_dict(),
        "nonnegative_window": nonnegative.to_dict(),
    }
    if args.min_element is not None:
        result["signed_window"] = scan_signed_window(
            args.h, args.k, args.min_element, args.max_element
        ).to_dict()
    _print_json(result)
    return 0


def _oeis_check(args: argparse.Namespace) -> int:
    checks = check_oeis_values(args.max_stamps)
    _print_json(checks)
    return 0 if all(check["ok"] for check in checks) else 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    construct = subparsers.add_parser("construct", help="build and verify hA")
    construct.add_argument("--starts", required=True, type=_parse_starts)
    construct.add_argument("--h", type=int, default=2)
    construct.add_argument("--length", required=True, type=int)
    construct.add_argument("--distance", type=int, default=2)
    construct.add_argument("--base", type=int)
    construct.add_argument(
        "--scheme", choices=("powers", "moments", "sidon"), default="powers"
    )
    construct.add_argument("--output")
    construct.add_argument("--include-sumset", action="store_true")
    construct.set_defaults(handler=_construct)

    scan = subparsers.add_parser("scan", help="run exact and bounded searches")
    scan.add_argument("--h", required=True, type=int)
    scan.add_argument("--k", required=True, type=int)
    scan.add_argument("--max-element", required=True, type=int)
    scan.add_argument("--min-element", type=int)
    scan.set_defaults(handler=_scan)

    oeis = subparsers.add_parser("oeis-check", help="compare against OEIS values")
    oeis.add_argument("--max-stamps", type=int, default=3)
    oeis.set_defaults(handler=_oeis_check)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return args.handler(args)


if __name__ == "__main__":
    raise SystemExit(main())
