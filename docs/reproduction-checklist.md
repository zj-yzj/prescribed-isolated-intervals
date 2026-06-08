# Reproduction checklist

Run commands from the workspace root.

## Python environment

```powershell
python -m pip install -e .[dev]
python -m pytest
```

Expected test result: `19 passed`.

## Lean formalization

```powershell
lake build
```

Expected result: all Lean targets compile. The main closed theorem is
`IntervalBases.explicitPrescribedIsolatedIntervalsWithRadius` in
`Formalization/Cardinality.lean`. The polynomial-label set-level theorem is
`IntervalBases.momentConstructedBasis_has_isolated_exceptional_pattern` in
`Formalization/MomentSetLevelPackaging.lean`. The reusable theorem behind both
label choices is
`IntervalBases.genericConstructedBasis_has_isolated_exceptional_pattern` in
`Formalization/GenericLabels.lean`. The double-sumset bridge from
order-four short-relation freedom is
`IntervalBases.genericConstructedBasis_has_isolated_exceptional_pattern_h2_of_shortRelationFree`
in `Formalization/SidonLabels.lean`. The explicit shifted-Sidon instance is
`IntervalBases.shiftedSidonLabels_have_isolated_exceptional_pattern` in the
same file. The translated quadratic-diameter closure is
`IntervalBases.exists_shiftedSidonLabels_have_translated_pattern_and_quadratic_diameter`
in `Formalization/SidonDiameter.lean`; its tightened bound is
`T + 8 M (2m - 1)^2`. The explicit quadratic lower bound is
`IntervalBases.shiftedSidonBasis_diameter_lower_bound` in the same file.
The reusable midpoint-rounding lemma is
`IntervalBases.exists_shift_targetRadius_centerTargets_le_natHalfCeil`
in `Formalization/Centering.lean`. The paper-facing translated
interval-family closure, including maximal intervals and exact cardinality,
is
`IntervalBases.exists_centeredShiftedSidonBasis_has_exactly_intervals_and_quadratic_diameter`
in `Formalization/SidonPaperCorollary.lean`.
The version that automatically selects the centered radius and scale after a
translation is supplied is
`IntervalBases.exists_explicitCenteredShiftedSidonBasis_has_exactly_intervals`
in the same file.
The automatically centered shifted-Sidon interval theorem is
`IntervalBases.exists_explicitCenteredShiftedSidonBasis_has_exactly_intervals_enclosed`
in the same file. The corresponding automatically centered finite-moment
theorem is
`IntervalBases.exists_explicitTranslatedMomentBasis_has_exactly_intervals_enclosed`
in `Formalization/MomentDiameter.lean`.
## Classical cross-check

```powershell
python -m interval_bases oeis-check --max-stamps 3
```

This compares the exact small search against the bundled initial values from
OEIS A001209.

## Construction certificate

```powershell
python -m interval_bases construct --starts=-7,3,14 --length 3 --h 2 --distance 2 --output certificates/reproduction-negative-starts.json
```

The constructor recomputes `hA` before writing the JSON certificate. It should
report no missing target values and no unexpected nontrivial interval.

## Polynomial-label certificate

```powershell
python -m interval_bases construct --scheme moments --starts=1000000 --length 3 --h 2 --distance 4 --output certificates/moments-large-translation.json
```

This exercises the translation-normalized finite moment labels. It should
report `label_scheme` as `moments`, a small normalized `target_radius`, and no
unexpected nontrivial interval.

## Quadratic-label certificate for `h = 2`

```powershell
python -m interval_bases construct --scheme sidon --starts=1000000 --length 3 --h 2 --distance 4 --output certificates/sidon-large-translation.json
```

This exercises the shifted Sidon labels. It should report `label_scheme` as
`sidon`, a small normalized `target_radius`, and no unexpected nontrivial
interval.

## Bounded side scan

```powershell
python -m interval_bases scan --h 3 --k 5 --max-element 8 --min-element -8
```

This is exploratory evidence only. It is not a proof of any unrestricted
equality among the stamp-problem variants.

## Paper build

```powershell
New-Item -ItemType Directory -Force output/latex-build | Out-Null
pdflatex -interaction=nonstopmode -halt-on-error -output-directory output/latex-build paper/prescribed-isolated-intervals.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory output/latex-build paper/prescribed-isolated-intervals.tex
```

Review the build log and rendered pages. The curated review copy committed in
the repository is `paper/prescribed-isolated-intervals.pdf`.
