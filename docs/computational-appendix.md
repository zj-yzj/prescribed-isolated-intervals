# Computational Appendix

## Definitions

For a finite integer set `A`, the implementation computes the exact sumset

```text
hA = {a_1 + ... + a_h : a_i in A}.
```

The function `ell(A, h)` returns the largest `n` such that `[0, n]` is
contained in `hA`. The function `ell_sharp(A, h)` returns the largest value of
`v - u` over all consecutive intervals `[u, v]` contained in `hA`.
The function `interval_starts_of_length(A, h, n)` returns all starts `c` for
which `[c, c + n]` is contained in `hA`; this is the computational form of the
starts-only questions.

## Exact Versus Bounded Searches

`enumerate_exact_prefix_extremum(h, k)` computes `n_h(k)` exactly. It uses the
counting bound

```text
n_h(k) <= binomial(h + k - 1, k - 1) - 1
```

and the fact that an extremal nonnegative basis can be taken inside
`[0, n_h(k)]`.

The functions `scan_nonnegative_window(...)` and `scan_signed_window(...)`
only report extrema inside the requested finite window. They are discovery
tools and must not be cited as global proofs.

The function `scan_strong_single_interval_minima(...)` is another bounded
discovery tool. It normalizes candidates by translating them so that
`min(A) = 0`, then searches for sets whose double sumset has exactly one
nontrivial maximal interval of a prescribed length. This is useful for testing
whether a proposed cardinality lower bound for the strong single-interval
problem is plausible before trying to prove it.

## Reproduction

```powershell
python -m pytest
python -m interval_bases oeis-check --max-stamps 3
python -m interval_bases construct `
  --starts=-6,2 `
  --h 3 `
  --length 2 `
  --distance 2 `
  --output certificates/example-h3.json `
  --include-sumset
python -m interval_bases construct `
  --scheme moments `
  --starts=1000000 `
  --h 2 `
  --length 3 `
  --distance 4 `
  --output certificates/moments-large-translation.json
python -m interval_bases construct `
  --scheme sidon `
  --starts=1000000 `
  --h 2 `
  --length 3 `
  --distance 4 `
  --output certificates/sidon-large-translation.json
python -m interval_bases sparse-pair-construct `
  --starts=0,50,150 `
  --length 16
python -m interval_bases sparse-crt-construct `
  --starts=0,2116800 `
  --length 705600
python -m interval_bases strong-single-scan --max-length 8 --max-k 6 --max-element 18
```

The certificate records the label scheme, constructed set, all maximal nontrivial runs in
`hA`, the minimum spacing between exceptional points, the minimum distance
from an exceptional point to a target point, and a SHA-256 digest of `2A`.

The `moments` scheme implements the polynomial-diameter refinement. It first
centers the target pattern by a multiple of `h`, then replaces exponential
positional labels with the finite moment labels proved in the paper.

The `sidon` scheme is specialized to `h = 2`. It uses shifted Sidon labels
whose largest value is quadratic in the number of target points. This gives a
sharper quadratic diameter bound for double sumsets. The Lean development
also checks that the explicit basis has quadratic diameter from below.

The `strong-single-scan` command reports, for each `1 <= n <= max_length`, the
first cardinality found in the requested finite window for which `2A` has
exactly one nontrivial maximal interval of length `n`. It is deliberately
separate from the OEIS checks: it studies the no-extra-proper-interval
condition used in the paper, not only the prefix invariant `n_2(k)`.

The `sparse-pair-construct` command builds the pair-sum-separated sparse
multi-interval model from the paper and uses `interval_starts_of_length` to
verify that the length-`n` interval starts are exactly the prescribed starts.

The `sparse-crt-construct` command builds the arbitrary-start sparse model
from the CRT-incompatible colour theorem. It records the chosen primes,
modulus, CRT steps, packet bounds, and positional labels. By default its
verification is structural, following the congruence proof in the paper;
`--include-sumset` additionally enumerates `2A` and should only be used for
small examples, such as the one-interval case.

## Lean Verification

The arithmetic, representation-decoding, exceptional-count uniqueness,
set-level isolation, interval-family packaging, maximal-run characterization,
and exact-cardinality theorem are checked separately:

```powershell
$env:PATH="$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
```

The precise scope is recorded in
[`formalization-status.md`](formalization-status.md).
The finite moment separation lemma, closed diameter estimate, midpoint
centering theorem, and interval-family polynomial-label closure are now part
of the Lean boundary. For the shifted-Sidon
formula, Lean checks pair-sum injectivity, order-four short-relation freedom,
the concrete set-level isolation theorem, translation invariance, the
quadratic diameter upper and lower bounds, tightened Bertrand-prime estimate,
exact cardinality after translation, and the final separated-interval
wrapper. Lean also selects a midpoint translation, centered radius, and scale
automatically. Exact
Python tests and the saved certificate provide an independent computational
check. The sparse Frobenius, pair-sum-separated, and CRT-incompatible
constructions are implemented and tested in Python but are not part of the
Lean formalization boundary.

## Classical Cross-Checks

The test suite compares exact computations with:

- [OEIS A001208](https://oeis.org/A001208), the postage-stamp problem with
  three positive denominations. In the notation used here this is `n_h(4)`.
- [OEIS A001209](https://oeis.org/A001209), the postage-stamp problem with
  four positive denominations. In the notation used here this is `n_h(5)`.
