# An explicit radius for the strict local maximality of A16

`pipeline/certify_radius.jl` (`make radius`) certifies a number `r > 0` such that
no small equilateral 16-gon within distance `r` of A16, modulo
orientation-preserving Euclidean motions, has a side at least as long unless it
*is* A16 up to such a motion. The article's Theorem 6.3 gives *some* neighbourhood;
this gives one of certified size. This page is the proof; the script computes the
constants with outward-rounded interval arithmetic.

## Setting

Let `x = (p, l)` be A16 at the certified root `z*`, with `n = 16`, and let
`E(A16)` be its 15 active diameters. For `h = (v, eta) ∈ (R^2)^16 × R`, `|h|` is
the Euclidean norm on `R^33`.

* `A` is the 31 × 33 Jacobian of `build_jacobian`: row `i ≤ 16` is
  `h ↦ <s_i, v_{i+1} − v_i> − eta` with `s_i = (p_{i+1} − p_i)/l`, and row `16+k` is
  `h ↦ <p_b − p_a, v_b − v_a>` for the `k`-th active pair `{a, b}`. Write
  `A_E`, `A_D` for the two blocks.
* `(alpha, lambda) ∈ R^16 × R^15` are the multipliers of stage 05: `A' (alpha, lambda) = (0, …, 0, 16)`,
  that is, `16 eta = alpha·(A_E h) + lambda·(A_D h)` for every `h`, with every
  `lambda_e > 0`.
* `V` is the 33 × 3 matrix of the infinitesimal rigid motions (two translations
  and the rotation `v_i = J p_i`, all with `eta = 0`); its column space is
  `R_eq(p)`.

## Theorem

Let `sigma > 0` with `sigma^2 ≤ lambda_min(A'A + V V')` and put

    r = sigma · l / (2 (1 + |alpha|_2 / lambda_min)).

Let `(q, m)` be a labelled configuration with `|q_{i+1} − q_i| = m` for every `i`,
`|q_i − q_j| ≤ 1` for all `i, j`, and `m ≥ l`. If

    min over orientation-preserving motions g of |(g·q − p, m − l)|  <  r,

then `m = l` and `q` is congruent to `p` by an orientation-preserving motion.

No convexity, cyclic order or inactive margin is assumed of `(q, m)`.

## Proof

**Alignment.** The minimum exists (the rotation group is compact and the
translation part is solved in closed form). Let `g` attain it and put
`h = (u, eta) = (g·q − p, m − l)`. The first-order conditions of the minimisation
are `sum_i u_i = 0` (translations) and `sum_i <u_i, J (p_i + u_i)> = 0`
(rotations), and `<u_i, J u_i> = 0`, so `sum_i <u_i, J p_i> = 0`. That is,
`V' h = 0`: `h ⊥ R_eq(p)`. Replacing `q` by `g·q` changes no distance, so we
may assume `g` is the identity.

**Exact expansion.** The squared constraints are quadratic, so for
`y = x + h`

    |q_{i+1} − q_i|^2 − m^2 = 2l (A_E h)_i + w_i,      w_i = |u_{i+1} − u_i|^2 − eta^2,
    |q_b − q_a|^2 − 1       = 2 (A_D h)_e + |u_b − u_a|^2,

using `|p_{i+1} − p_i| = l` and `|p_b − p_a| = 1` (Lemma 6.1, exact). The first
vanishes, and the second is `≤ 0` because `q` is small. Hence

    A_E h = −w / (2l),       (A_D h)_e ≤ −|u_b − u_a|^2 / 2 ≤ 0.

**Size of `w`.** `|w|_2 ≤ sum_i |u_{i+1} − u_i|^2 + sqrt(16) eta^2 ≤ 4 sum_i |u_i|^2 + 4 eta^2 = 4 |h|^2`,
since `|a − b|^2 ≤ 2|a|^2 + 2|b|^2` and every index occurs in two sides.

**The multipliers.** With `eta ≥ 0`,

    lambda·(A_D h) = 16 eta − alpha·(A_E h) = 16 eta + alpha·w/(2l) ≥ −|alpha|_2 |w|_2 / (2l).

Every term on the left is `≤ 0`, so
`lambda_min |A_D h|_1 ≤ sum_e lambda_e |(A_D h)_e| ≤ |alpha|_2 |w|_2 / (2l)`, and

    |A h|_2 ≤ |A_E h|_2 + |A_D h|_1 ≤ (|w|_2 / (2l)) (1 + |alpha|_2 / lambda_min)
            ≤ (2/l) (1 + |alpha|_2 / lambda_min) |h|^2.

**The lower bound.** Since `V' h = 0`,
`|A h|^2 = h'(A'A + V V')h ≥ sigma^2 |h|^2`.

**Conclusion.** `sigma |h| ≤ (2/l)(1 + |alpha|_2/lambda_min) |h|^2`, so `h = 0` or
`|h| ≥ r`. Under the hypothesis `|h| < r`, `h = 0`: `m = l` and `g·q = p`. ∎

## How the constants are certified

All at 256 bits, outward rounded, over the box `Z_cert` of stages 03–05, which
contains `z*` (box nesting gate of `certify_a16.jl`).

* `lambda_min(A'A + V V') ≥ mu`: the interval Cholesky factorisation of
  `B − mu I`, `B = A'A + V V'` computed in interval arithmetic, runs with every
  pivot strictly positive. Then every symmetric matrix enclosed by the interval
  matrix is positive definite (G. Alefeld, G. Mayer, *The Cholesky method for
  interval data*, Linear Algebra Appl. 194 (1993)), in particular `B(z*) − mu I`.
  `mu` is the largest of `0.9^k` times a floating estimate that passes.
* `|alpha|_2` from the upper ends of the certified enclosures of stage 05,
  `lambda_min` from their certified lower bound, `l` from its enclosure over
  `Z_cert`.
* `r` is computed as an interval and its lower endpoint is reported: the theorem
  holds for any smaller radius.

## Scope

This is a statement about labelled configurations near A16 in the Procrustes
sense. It does not bound how far a *different* local maximiser may be, and it
says nothing about global optimality.
