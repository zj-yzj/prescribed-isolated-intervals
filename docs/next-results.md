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
5. The paper now includes a sparse single-interval double-sumset construction
   with `O(sqrt(n))` elements, together with the matching counting lower bound
   `n + 1 <= binomial(|A| + 1, 2)`.
6. The code now includes a bounded `strong-single-scan` command for testing
   the stronger condition that `2A` has exactly one nontrivial interval.
7. A sparse multi-interval theorem now works under a pair-sum separation
   hypothesis on `C + C`, giving `O(q sqrt(n))` elements for the starts-only
   double-sumset problem in that regime.

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
polynomial whose degree is intentionally simple but large. The Bose--Chowla
section now supplies the sharper fixed-`h` polynomial exponent through modular
`B_H` sets.

The best next mathematical direction is no longer another label family. It is
to understand cardinality:

1. prove a lower bound for arbitrary multi-interval isolated patterns that is
   stronger than the trivial multiset count;
2. weaken the pair-sum separation hypothesis in the sparse multi-interval
   theorem, or prove that some additive separation is necessary for this
   packet method;
3. isolate a clean obstruction for arbitrary starts coming from the
   same-colour sums indexed by `c_i + c_j`.
4. compare the bounded strong-single-interval minima against classical
   postage-stamp extremal bases to see whether a sharper theorem is already
   hidden in known `n_2(k)` data.

This would directly address the gap between the strong isolated construction
with `2q(n + 1)` elements and the order-optimal `O(sqrt(n))` single-interval
starts-only construction.

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
`binomial(m, 2)`, Lean checks the stronger lower bound
`2 M m (m - 1)` for the explicit shifted-Sidon basis, and the sparse
single-interval construction is optimal in order by the elementary lower bound
above. Remaining useful targets are:

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
