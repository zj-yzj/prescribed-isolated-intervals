# Signed Interval Additive Bases

Copyright (c) 2026 Zijie Yu. All rights reserved. This repository is public
for timestamped inspection and reproducibility review only. No permission is
granted to copy, redistribute, publish, submit, or prepare derivative scholarly
work from the manuscript, code, Lean formalization, certificates, or
documentation without prior written permission.

This repository supports a constructive study of Problems 9-11 in Melvyn
Nathanson's [*Problems in additive number theory, VII*][nathanson]. The main
result implemented here is an explicit construction of a finite integer set
`A` whose `h`-fold sumset has any prescribed, sufficiently separated family
of nontrivial consecutive intervals and no others, for every `h >= 2`.

For starts `C = {c_1, ..., c_q}`, interval length `n >= 1`, and isolation
distance `d >= 2`, the construction has

```text
|A| = 2 q (n + 1).
```

It works whenever consecutive starts differ by at least `n + 2`. The Python
code creates machine-checkable JSON certificates, but the proof is elementary
and is recorded in
[`paper/prescribed-isolated-intervals.tex`](paper/prescribed-isolated-intervals.tex).

## Setup

```powershell
python -m pip install -e .
python -m pytest
```

Generate and verify a certificate:

```powershell
python -m interval_bases construct `
  --starts=-6,2 `
  --h 3 `
  --length 2 `
  --distance 2 `
  --output certificates/example-h3.json `
  --include-sumset
```

Generate a translation-normalized certificate using the polynomial-size
moment labels:

```powershell
python -m interval_bases construct `
  --scheme moments `
  --starts=1000000 `
  --h 2 `
  --length 3 `
  --distance 4 `
  --output certificates/moments-large-translation.json
```

For double sumsets, generate a much smaller certificate using the
quadratic-size Sidon labels:

```powershell
python -m interval_bases construct `
  --scheme sidon `
  --starts=1000000 `
  --h 2 `
  --length 3 `
  --distance 4 `
  --output certificates/sidon-large-translation.json
```

Run exact classical checks and bounded exploratory scans:

```powershell
python -m interval_bases oeis-check --max-stamps 3
python -m interval_bases scan --h 4 --k 5 --max-element 24 --min-element -8
```

## What The Commands Mean

- `construct` proves a concrete instance by recomputing `hA`, locating all
  consecutive runs, and recording spacing statistics.
- `construct --scheme moments` uses the polynomial-size finite moment labels
  from the refinement theorem and centers the target pattern modulo `h`.
- `construct --scheme sidon` uses the quadratic-size shifted Sidon labels
  available for `h = 2`.
- `oeis-check` computes exact values of `n_h(k)` and compares selected values
  with [OEIS A001208][a001208] and [OEIS A001209][a001209].
- `scan` is exploratory. Nonnegative results are bounded-window results unless
  labeled `exact_prefix`; signed results are always bounded-window results.

Lean is intentionally optional. The key separation lemma is short enough to
audit by hand, and a Mathlib-backed Lean 4 formalization is now included.

## Lean Formalization

The project pins Lean `v4.30.0` and Mathlib `v4.30.0`. On a machine with Elan:

```powershell
$env:PATH="$env:USERPROFILE\.elan\bin;$env:PATH"
lake update
lake build
```

The checked files currently cover:

- positional separation of scaled base labels;
- preservation of the required gap after bounded offsets are added;
- the count argument showing that a zero-label `h`-term sum contains exactly
  one positive term and `h - 1` matching negative terms;
- the explicit `h`-fold sumset API, constructed basis, and membership of every
  prescribed target point in the constructed sumset;
- tagged representation decoding, coefficient-norm and offset bounds;
- uniqueness of exceptional count vectors;
- the set-level theorem that every non-target sum is isolated by the required
  distance from every other sum;
- interval-family flattening and the proof that the maximal nontrivial
  intervals are exactly the listed intervals;
- the injectivity argument for the signed generators and the exact cardinality
  `|A| = 2 q (n + 1)`;
- a closed theorem that chooses the target radius automatically and substitutes
  the paper's explicit scale and positional base.

See [`docs/formalization-status.md`](docs/formalization-status.md) for the exact
boundary. The positional-label construction is fully represented as a Lean
declaration. The newer moment-label construction now also has a kernel-checked
Vandermonde separation lemma, set-level isolation theorem, exact cardinality,
closed diameter estimate, general translation rule, and automatically
centered position-independent interval-family wrapper. An abstract
`BoundedLabelSeparation` theorem factors the combinatorial proof from the label
formula and recovers both the power-label and moment-label constructions.
For `h = 2`, the paper also gives a shifted-Sidon instance with quadratic
diameter. Its explicit pair-sum arithmetic, order-four short-relation
separation, set-level isolation theorem, translation invariance, diameter
upper and lower bounds, tightened Bertrand-prime estimate, exact cardinality,
and automatically centered interval-family wrapper are also kernel-checked
in Lean.
The direct Problem 7(2) audit witness `A = {-1, 1, 2}` and
`[0, 4] subseteq 2A` is kernel-checked as well.

## Paper And Documentation

- [`paper/prescribed-isolated-intervals.tex`](paper/prescribed-isolated-intervals.tex)
  contains the paper source.
- [`paper/prescribed-isolated-intervals.pdf`](paper/prescribed-isolated-intervals.pdf)
  is the compiled review copy.
- [`arxiv/main.tex`](arxiv/main.tex) is a single-file arXiv source copy.
- [`docs/computational-appendix.md`](docs/computational-appendix.md)
  explains the reproducibility boundary.
- [`docs/formalization-status.md`](docs/formalization-status.md)
  records the Lean verification boundary.
- [`docs/referee-checklist.md`](docs/referee-checklist.md) is an
  adversarial mathematical review pass before circulation.
- [`docs/reproduction-checklist.md`](docs/reproduction-checklist.md)
  records clean commands and expected results for reproducing the checks.
- [`docs/next-results.md`](docs/next-results.md) separates low-risk
  cleanup from the next genuinely mathematical strengthening directions.

[nathanson]: https://arxiv.org/abs/2605.26425
[a001208]: https://oeis.org/A001208
[a001209]: https://oeis.org/A001209
