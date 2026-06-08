# Lean Formalization Status

## Environment

- Lean: `v4.30.0`
- Mathlib: `v4.30.0`
- Build command:

```powershell
$env:PATH="$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
```

## Kernel-Checked Results

[`Formalization/PositionalSeparation.lean`](../Formalization/PositionalSeparation.lean)
checks the label arithmetic:

- a nonzero signed coefficient vector with `l1Norm <= B` cannot vanish when
  evaluated in base `B`;
- multiplying labels by `M` gives a gap of at least `M`;
- two distinct bounded vectors therefore have scaled positional values at
  least `M` apart.

[`Formalization/OffsetSeparation.lean`](../Formalization/OffsetSeparation.lean)
checks the bounded-offset step:

- if label values are at least `M` apart;
- offsets differ by at most `R`;
- and `R + d <= M`;
- then the represented integers are at least `d` apart.

[`Formalization/MatchedCounts.lean`](../Formalization/MatchedCounts.lean)
checks the zero-label counting step:

- an `h`-term zero-label sum contains exactly one positive term in total;
- some index therefore contributes one positive term and `h - 1` matching
  negative terms.

[`Formalization/Construction.lean`](../Formalization/Construction.lean)
defines the constructed sumset and tagged generators:

- `hFoldSumset` defines exact `h`-term sumsets with repetition;
- `constructedBasis` defines the explicit signed basis from the paper;
- every basis term and every sumset element can be decoded into a tagged
  generator representation;
- `target_mem_hFoldSumset_constructedBasis` checks that every prescribed
  target point has its intended matched representation.

[`Formalization/Representation.lean`](../Formalization/Representation.lean)
checks the representation budgets:

- positive and negative counts sum to the representation length;
- the label contribution is exactly the scaled positional value of the
  extracted coefficient list;
- an `h`-term representation has label `l1Norm <= h(h - 1)`;
- every representation offset has absolute value at most `hT`;
- a zero-label representation is one of the prescribed target points.

[`Formalization/ExceptionalCounts.lean`](../Formalization/ExceptionalCounts.lean)
checks the exceptional-count uniqueness argument:

- if positive counts differ at an index, the coefficient equations consume
  the full `h`-term budget and force a matched target representation;
- a common nonzero coefficient vector therefore uniquely determines the
  positive and negative counts.

[`Formalization/SetLevelPackaging.lean`](../Formalization/SetLevelPackaging.lean)
checks the main set-level isolation theorem:

- every listed target belongs to the constructed `h`-fold sumset;
- every non-target sum is at distance at least `d` from every listed target;
- more strongly, every non-target sum is at distance at least `d` from every
  other distinct sumset element.

[`Formalization/PaperCorollary.lean`](../Formalization/PaperCorollary.lean)
checks the interval-family layer:

- `intervalTargets` flattens `[c_i, c_i + n]` into the target list;
- the flattened prescribed target set is exactly the desired interval union;
- every adjacent pair in the sumset lies inside one listed interval;
- `IsMaximalNontrivialInterval` captures maximal closed integer runs of
  positive length;
- the maximal nontrivial intervals are exactly the listed intervals.

[`Formalization/Cardinality.lean`](../Formalization/Cardinality.lean)
checks the exact-size layer:

- distinct tagged generators have distinct integer values;
- `constructedBasis` is their range;
- its exact cardinality is `2 q (n + 1)`;
- `explicitPrescribedIsolatedIntervalsWithRadius` automatically selects the
  target radius, substitutes `M = 2hT + d` and `B = 2h(h - 1)`, and proves the
  paper-facing maximal-interval and cardinality conclusions.

[`Formalization/MomentSeparation.lean`](../Formalization/MomentSeparation.lean)
checks the arithmetic core of the polynomial-diameter refinement:

- a nonzero coefficient function has a nonzero low-order power moment, via
  Mathlib's Vandermonde theorem;
- the first `L` moments have total `l1` norm at most
  `momentEncodingBase m L = L^2 max(1, m - 1)^(L - 1)`;
- evaluating the encoded moment labels is positional evaluation of that
  moment vector;
- distinct bounded coefficient functions remain separated after scaling and
  after adding bounded offsets.

[`Formalization/MomentConstruction.lean`](../Formalization/MomentConstruction.lean),
[`Formalization/MomentRepresentation.lean`](../Formalization/MomentRepresentation.lean),
and
[`Formalization/MomentSetLevelPackaging.lean`](../Formalization/MomentSetLevelPackaging.lean)
check the polynomial-label construction:

- every target has its intended matched representation;
- the usual count coefficient function controls the moment-label value;
- zero-label representations are prescribed targets;
- every non-target sum is at distance at least `d` from every target and
  every other distinct exceptional sum.

[`Formalization/GenericLabels.lean`](../Formalization/GenericLabels.lean)
extracts the reusable label-family framework:

- `BoundedLabelSeparation` is the only arithmetic hypothesis on a label
  family;
- `genericConstructedBasis_has_isolated_exceptional_pattern` proves the
  complete set-level isolation theorem from that hypothesis;
- the matched-count and exceptional-count arguments are therefore independent
  of the particular label formula.

[`Formalization/GenericLabelInstances.lean`](../Formalization/GenericLabelInstances.lean)
checks both concrete instances:

- positional power labels satisfy `BoundedLabelSeparation`;
- finite moment labels satisfy `BoundedLabelSeparation`;
- both concrete set-level theorems are recovered from the abstract framework.

[`Formalization/GenericCardinality.lean`](../Formalization/GenericCardinality.lean)
checks exact cardinality for arbitrary separated labels:

- the tagged-generator value map is injective under the generic separation
  budget;
- the generic constructed basis is its range;
- every separated-label instance therefore has exact cardinality `2m`.

[`Formalization/TranslatedPatterns.lean`](../Formalization/TranslatedPatterns.lean)
and
[`Formalization/Centering.lean`](../Formalization/Centering.lean)
check the reusable translation and midpoint-rounding layer:

- translating a basis by `shift` translates its `h`-fold sumset by
  `h * shift`;
- isolated exceptional patterns and exact cardinality survive translation;
- a finite target list inside `[lower, upper]` admits a centering shift with
  radius at most `ceil ((upper - lower + h) / 2)`.

[`Formalization/MomentDiameter.lean`](../Formalization/MomentDiameter.lean)
checks the closed paper-facing finite-moment theorem:

- finite moment labels have an explicit largest-label bound;
- the centered basis has the polynomial diameter estimate from the paper;
- translation restores the original target list;
- `exists_explicitTranslatedMomentBasis_has_exactly_intervals_enclosed`
  automatically selects a midpoint shift and packages the interval pattern,
  maximal-interval characterization, exact cardinality, and
  position-independent diameter bound.

[`Formalization/SidonLabels.lean`](../Formalization/SidonLabels.lean)
records the sharper double-sumset interface:

- `ShortRelationFree` packages the absence of nonzero relations of bounded
  `l1` norm;
- scaling a short-relation-free family gives `BoundedLabelSeparation`;
- the explicit shifted-Sidon formula is defined and its bounds
  `2 p^2 <= b_r < 4 p^2` are checked;
- equality of pair sums is decoded modulo `2p`, then resolved over `ZMod p`
  to prove pair-sum injectivity;
- positive and negative multiplicity lists convert that Sidon property into
  coefficient-vector short-relation freedom of order four;
- `shiftedSidonLabels_have_isolated_exceptional_pattern` feeds the explicit
  labels directly into the complete set-level isolation theorem for `h = 2`.

[`Formalization/SidonDiameter.lean`](../Formalization/SidonDiameter.lean)
checks the quantitative double-sumset layer:

- `SetDiameterAtMost` packages an elementary integer-set diameter bound;
- translating a basis preserves that bound in both directions and translates
  its double sumset by twice the translation;
- the centered shifted-Sidon basis has diameter at most `T + 8 M p^2`;
- its negative generators force diameter at least `2 M m (m - 1)`;
- Mathlib's Bertrand theorem supplies an odd prime below `2m`;
- `exists_shiftedSidonLabels_have_translated_pattern_and_quadratic_diameter`
  combines these facts into a translated isolated-target construction with
  diameter at most `T + 8 M (2m - 1)^2`.

[`Formalization/SidonPaperCorollary.lean`](../Formalization/SidonPaperCorollary.lean)
checks the paper-facing shifted-Sidon layer:

- centering a target list by `2 * shift` and translating the basis by `shift`
  restores the original target list;
- any isolated double-sumset realization of flattened separated intervals
  has exactly the listed nontrivial intervals;
- the translated shifted-Sidon basis has exact cardinality `2m`;
- `exists_centeredShiftedSidonBasis_has_exactly_intervals_and_quadratic_diameter`
  packages the interval pattern, maximal-interval characterization, exact
  cardinality, and quadratic diameter estimate in one declaration.
- `exists_explicitCenteredShiftedSidonBasis_has_exactly_intervals`
  automatically selects the centered radius and the scale `M = 4T + d`
  after a translation is supplied.
- `exists_explicitCenteredShiftedSidonBasis_has_exactly_intervals_enclosed`
  also selects a midpoint shift from an enclosing interval.
- `explicitCenteredShiftedSidonBasis_diameter_lower_bound` carries the
  quadratic lower bound through the paper-facing translated basis.

## Boundary

The main constructive theorem is fully represented as a Lean declaration.
The finite moment-label refinement now has Lean declarations through its
position-independent closed interval-family theorem. Independent mathematical
review is still appropriate before submission. The Bose--Chowla diameter
refinement in the paper cites the classical finite-field construction as an
external theorem and is not separately formalized here. The sparse
single-interval Frobenius-packet construction is also an ordinary paper proof
at this stage, not a Lean theorem. For the shifted Sidon refinement, Lean
checks the explicit pair-sum argument over `ZMod p`,
order-four short-relation freedom, set-level isolation, translation
invariance, quadratic upper and lower bounds, tightened Bertrand-prime
selection, exact cardinality after translation, and the automatically
centered interval-family wrapper. The general Sidon-label counting barrier in
the paper remains an ordinary short combinatorial proof.
