# Independent referee checklist

Use this as an adversarial review pass before circulating the draft.

## Main theorem

- [ ] Confirm that the hypotheses are exactly `h >= 2`, `n >= 1`, `d >= 2`,
  `q >= 1`, and successive starts differ by at least `n + 2`.
- [ ] Confirm that the target intervals are disjoint and separated by at
  least one missing integer.
- [ ] Verify the formula `|A| = 2 q (n + 1)` and the disjointness of the two
  halves of `A`.
- [ ] Check edge cases explicitly: `h = 2`, `n = 1`, `q = 1`, negative
  interval starts, and the limiting gap `c_(i+1) - c_i = n + 2`.

## Separation argument

- [ ] Derive the coefficient-vector expression for every `h`-term sum.
- [ ] Verify the bound `sum |z_r| <= h(h - 1)`.
- [ ] Prove that a zero coefficient vector forces a matching label and hence
  a prescribed target value.
- [ ] Check largest-digit domination for `B = 2 h(h - 1)`.
- [ ] Include the bounded offset `|u| <= h T` in every separation estimate.
- [ ] Verify separately: exceptional-to-target distance at least `d`, and
  distinct exceptional-to-exceptional distance at least `d`.

## Polynomial diameter refinement

- [ ] Verify the separated-label principle independently of either concrete
  label formula, including the `|A| = 2m` argument.
- [ ] Verify the Vandermonde argument in the moment-separation lemma.
- [ ] Check the bounds `|mu_j| <= K`, `sum_j |mu_j| <= L K = Q`, and
  the positional domination argument in base `Q`.
- [ ] Check that every difference of relevant label vectors has
  `l1`-norm at most `L = 2 h(h - 1)`.
- [ ] Verify that translation by `tau / h` moves `hA_0` by exactly `tau` and
  leaves the diameter unchanged.
- [ ] Check the degree `L(L - 1)` and the midpoint estimate
  `T <= ceil((D + h) / 2)`.
- [ ] Verify the elementary comparison bounds
  `m <= binomial(k + h - 1, h)` and `diam(A) >= diam(S) / h`.

## Quadratic double-sumset refinement

- [ ] Verify the shifted-Sidon formula `b_r = 2p^2 + 2pr + (r^2 mod p)`.
- [ ] Check pair-sum injectivity: reduce modulo `2p`, then modulo `p`, and
  identify the two unordered pairs as roots of the same quadratic over
  `F_p`.
- [ ] Check that `2p^2 <= b_r < 4p^2` excludes relations with unequal numbers
  of terms when the total number of terms is at most four.
- [ ] Verify the diameter estimate `diam(A) <= 8(4T + d)p^2 + T`, the
  tightened Bertrand consequence `p <= 2m - 1` when `m >= 2`, and the
  explicit lower bound `diam(A) >= 2Mm(m - 1)`.
- [ ] Verify the Sidon difference-counting barrier
  `diam(B) >= binomial(m, 2)`.

## Relation to the preprint

- [ ] Re-read Problems 9--11 in arXiv:2605.26425v2 and state precisely why
  `d = 2` implies each requested assertion.
- [ ] Check the Problem 7(2) example directly:
  `A = {-1, 1, 2}`, `[0, 4] subseteq 2A`, and `n_2(3) = 4`.
- [ ] Quote Theorem 4's displayed `Delta` exactly and distinguish a likely
  typographical issue from a proved flaw.

## Machine checks

- [ ] Run `lake build`.
- [ ] Run `python -m pytest`.
- [ ] Inspect one saved certificate with negative starts and one randomized
  certificate.
- [ ] Check that bounded computational scans are described as evidence, not
  as proofs of unrestricted claims.
- [ ] Confirm that every theorem claimed in the paper is either proved in the
  paper or named accurately in `research/formalization-status.md`.
- [ ] Keep the Lean boundary explicit: the power, moment, and shifted-Sidon
  closed interval constructions are formalized; midpoint centering and the
  shifted-Sidon quadratic upper and lower bounds are also formalized; exact
  minimization is not needed for the stated midpoint bound.

## Circulation pass

- [x] Replace the author placeholders in the email, author brief, and paper
  draft.
- [ ] Compare the TeX source, extracted PDF text, and rendered pages before
  acting on OCR-based typo reports; visually confirm `\ell` in the Sidon proof.
- [ ] Send the short note before public posting to reduce duplicated effort.
