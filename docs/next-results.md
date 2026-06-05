# Next Results Roadmap

This note separates submission cleanup from genuinely new mathematics.

## Low-Risk Closures

Completed:

1. The midpoint-rounding argument is formalized for arbitrary `h`. Both the
   moment and shifted-Sidon wrappers now select a near-optimal shift from an
   enclosing interval.
2. The translation-normalized moment-label diameter estimate, exact
   cardinality, and interval-family corollary are packaged in Lean.
3. The shifted-Sidon Bertrand bound now retains the strict inequality
   `p < 2m`, giving `T + 8 M (2m - 1)^2` instead of `T + 32 M m^2`.
4. The explicit shifted-Sidon basis has a formalized lower bound
   `2 M m (m - 1)`, showing that its quadratic order is sharp.

Remaining numerical polish: retaining the target count directly in
`b_r = 2p^2 + 2pr + (r^2 mod p)` gives a slightly smaller prime-level upper
bound. This is not a main theorem by itself.

## Main Mathematical Direction

Let

```text
L = 2 h (h - 1).
```

The separated-label principle needs to rule out nonzero integer relations of
`l1` norm at most `L`. The moment-label construction does this with a
polynomial whose degree is intentionally simple but large.

A stronger route is to use explicit finite `B_s` sets, with `s` chosen as a
function of `L`, together with a translation into a short positive interval.
The intended mechanism is:

1. the short interval forces the two sides of a short relation to use the
   same number of terms;
2. a suitable `B_s` property then forces equality of the two multisets;
3. scaling gives the separated-label hypothesis already consumed by the
   generic Lean theorem.

This should improve the fixed-`h` polynomial diameter exponent if the
unequal-length relation step is closed cleanly. The novelty would not be the
existence of `B_s` sets. It would be their use as a quantitatively sharper
label engine for prescribed isolated intervals, with an explicit theorem and
comparison against the moment construction.

Relevant primary sources:

- Nathanson, [*Problems in additive number theory, VII*](https://arxiv.org/abs/2605.26425)
- O'Bryant, [*Constructing Thick B_h-sets*](https://arxiv.org/abs/2308.12406)

## Lower Bounds

The note records the elementary bounds

```text
m <= binomial(k + h - 1, h)
diam(A) >= diam(S) / h.
```

It now also proves that every Sidon label set has diameter at least
`binomial(m, 2)`, and Lean checks the stronger lower bound
`2 M m (m - 1)` for the explicit shifted-Sidon basis. Remaining useful
targets are:

1. a cardinality lower bound that exploits isolation, not only the number of
   available multisets;
2. a diameter lower bound for arbitrary prescribed `m`-point target sets;
3. lower bounds outside the Sidon-label framework.

These are higher-risk problems. They should not delay circulation of the
current complete draft.

## External Steps

The workspace can prepare but cannot replace:

1. an independent line-by-line review by an additive-combinatorics expert;
2. sending the short note to Nathanson before public posting;
3. final human review of the inserted author metadata before circulation.
