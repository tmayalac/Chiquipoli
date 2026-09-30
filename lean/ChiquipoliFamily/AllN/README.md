# Every `n = 16k`, with no per-case data

This directory proves, for **every** `n = 16k`, the statement of
`A<n>/Published.lean` (`Main.lean`, **`published_all_n`**). The case `n = 16` is
taken from `../Interval/T16`; `n ≥ 32` is analytic. The theorem names keep the
namespace `Chiquipoli.Family.Trig` (with `.P3` for the multipliers and `.P1`
for feasibility), so that the names recorded elsewhere are unchanged.

| file | content |
|---|---|
| `Root.lean` | the zero of `F_n`: unique in `(0, π/n)`, simple |
| `Strip.lean` | the triangulated strip, rigidity, Problem 2 |
| `Layout.lean` | the symbolic run of the published code, for every `n = 16k` |
| `Constructor.lean` | unit chords on `G_n`, equal sides; rigidity of the polygon |
| `RungVector.lean` | Lemma R: the rungs turn by exactly `z` |
| `Multipliers/` | Problem 3: the stress in closed form, equilibrium, positivity, Theorem 3.5 |
| `Feasibility/` | Problem 1: side angles, convexity, smallness |
| `Main.lean` | the complete statement |

Verify: `../../verify_general.sh` (`make lean-general`).

## The root, for every `n` (`Root.lean`)

`root_all` is proved for **every** `n ≥ 16`, with no per-case data and no
interval tables:

```
theorem root_all (n : ℕ) (hn : 16 ≤ n) :
    ∃ z, z ∈ Ioo (π/(n+2)) (π/n) ∧ Optigon.F n z = 0 ∧ Fd n z < 0 ∧
      ∀ z' ∈ Ioo 0 (π/n), Optigon.F n z' = 0 → z' = z
```

`F_n` has exactly one zero in `(0, π/n)`, which is simple (`F_n' < 0`). The
bracket `(2 asin(sin(π/n)/2), π/n)` that upstream uses lies inside `(0, π/n)`.
The proof has four steps:

* **Sign change.** `F_n(π/(n+2)) > 0` (`F_left_pos`). The closed form
  `F_n(π/n) = −4 sin t (1−cos t)² (cos 2t − sin t)/cos² 2t` gives
  `F_n(π/n) < 0` (`F_right_closed`).
* **Location.** Write `F = y² + cos²(at) − 4 sin²(t/2)`. A zero then forces
  `|y| ≤ 2 sin²(z/2)` and `z ≥ π/(n−2+π)` (`loc`).
* **Simplicity.** `F' = 2 y y' − a sin((n−2)t) − 2 sin t`. On
  `[π/(n+2), π/n]` we have `|y'| ≤ 16` (`xd_bound`, `yd_bound`) and
  `a sin((n−2)t) + 2 sin t ≥ 2.6` (`main_term`). So at a zero,
  `F' ≤ 64 sin²(z/2) − 2.6 < 0` (`Fd_neg_at_zero`).
* **Uniqueness.** A continuous function whose derivative is negative at each
  of its zeros has at most one zero on an interval (`at_most_one_zero`).

Steps 1–3 of `../../verify_general.sh` build the module, scan it for admitted goals,
and audit `root_all`.

## Rigidity and the constructor, for every `n = 16k`

Three more modules have no per-case data. Their combinatorics are proved by
`omega` for a symbolic `k`.

* `Strip.lean`. The sides and the pairs of `G_n` form a triangulated strip. It
  starts after the point `(h/2, h/2)` of the lattice path and leaves out only
  the two closing sides:
  * `strip_edge`, `strip_step` and `strip_cover` establish the strip;
  * `strip_rigid` and `gn_rigid` prove infinitesimal rigidity: each step adds a
    triangle with sides `1, 1, ℓ`, which is never flat;
  * `problem2` is Problem 2 (angular rigidity), with the constructor's direction
    `(ṗ, ℓ')` as a hypothesis. It gives `η = 0` whenever the closing side moves
    to first order, i.e. `F_n'(z) ≠ 0`.
* `Layout.lean`. `vertexS_eq` states that for `n = 16k` the symbolic run of
  upstream's code (`abS`) stores `spec k x` at index `x`. The proof is the loop
  invariant `Inv`: iteration `I` writes `q_I, r_I, u_I, t_I` and their mirror
  images at eight explicit indices, and no index is written twice.
* `Constructor.lean`. From the layout and the identities of `Shapes.lean`:
  * `chords_all`: every pair of `G_n` is at distance `1`;
  * `sides_all`: every non-closing side is `2 sin(z/2)`;
  * `closing_all`, `closing'_all`: each closing side has squared length
    `F_n + ℓ²`.

  `published_all` combines these with `root_all`: for every `n = 16k`, the
  unique zero of `F_n` in `(0, π/n)` is simple, and there the published polygon
  is equilateral, has unit distance on every pair of `G_n`, and is
  infinitesimally rigid.

## Problem 3 and strict local maximality, for every `n = 16k`

The modules below give the multipliers of the note on Problem 3 in closed form
and prove the whole chain in Lean, with no per-case data:

* `RungVector.lean`, `rung_vec`: Lemma R. Along the strip, rung `ρ_i` is
  `∓Φ_{8k−1−i}`, so consecutive rungs turn by exactly `z`.
* `Multipliers/Core.lean`, `Multipliers/Stress.lean`: the stress, i.e. side weights `sigS` and rung
  weights `lamR`, from the recursion `tau`. `rung_core` is the identity
  `λ_i u_i − S_{i−1} + S_i = ε_i κ (1, 0)` for one rung.
* `Multipliers/Vertices.lean`, `Multipliers/Symmetry.lean`, `Multipliers/Balance.lean`, `force_all`: equilibrium
  at every vertex.
  * Interior vertices: the identity above, summed over the vertex's run of rungs.
  * The gap vertices `A`, `C` and the vertex `h`: directly.
  * The second half: the symmetry `x ↦ −x`.
  * The vertex `0`: global equilibrium.
* `Multipliers/Theorem35.lean`, `local_max_of_positive`: Theorem 3.5 (`thm_3_5`), with the
  rigidity of the strip and the stationarity from `force_all`.
* `Multipliers/Gap.lean`, `yy_pos`: the gap is open, `a = y(z) > 0`, for `n ≥ 32`. The
  proof uses the mean value theorem, `|y'| ≤ 16` and the closed form of `y(π/n)`.
* `Multipliers/Positivity.lean`: the bounds on `τ` and `κ` (`tau_lower`, `tau_pos`) give
  `λ_j > 0` (`lamR_pos`) and negative side weights (`sigS_neg`). The switch
  `a → t` uses Jordan's inequality (`switch_ineq`).
* `Multipliers/StrictLocalMax.lean`, **`strict_local_max_all`**: for every `n = 16k`, the unique
  zero of `F_n` in `(0, π/n)` gives a polygon that no nearby equilateral small
  `n`-gon beats in side length, modulo Euclidean motions. The case `n = 16` is
  taken from the per-case certificate `T16`.

## Problem 1 and the complete statement, for every `n = 16k`

* `Feasibility/PolygonGeometry.lean`: general facts about polygons, independent of the constructor.
  * `convex_of_angles`: sides `ℓ e(α_x)` with `α` strictly increasing over a span
    `< 2π` give a convex polygon. `cross(q_i, q_{i+1}, q_j)` is `ℓ²` times a
    partial sum of `sin β_m` (`partial_sin_pos`).
  * `supp_of_cone`: a vertex supports its normal cone.
  * `small_of_antipodal`: support pairs at distance `≤ 1` for every direction
    imply smallness.
* `Feasibility/Sides.lean`, `Feasibility/Angles.lean`: every side is `ℓ e(sideAng x)` (`side_all`),
  with the angle in closed form:
  * `θ_j + z/2 ± π/2` along the strip;
  * `π/2 − β` and `3π/2 + β` on the closing sides, `β = arctan(a / sin φ)`.

  The angles increase with turns `≤ 1/2` (`sideAng_succ`, `sideAng_turn`) and
  span less than `2π`. Hence `convex_all`.
* `Feasibility/Smallness.lean`, `small_all`: for every direction, a pair of support vertices at
  distance `≤ 1`:
  * a rung, in the sector of that rung;
  * the middle rung `{8k, 0}`;
  * in the gap arc, `B–D`, `A–D` (width `a + cos φ ≤ 1`) or `A–C`;
  * mirror images and `ψ + π` for the rest.
* `Main.lean`, **`published_all_n`**: the statement of `A<n>/Published.lean`
  for **every `n = 16k`**:
  * `F_n` has a unique zero in `(0, π/n)`, and it is simple;
  * there, the published polygon is strictly convex, equilateral and small;
  * it is a strict local maximiser of the perimeter among equilateral small
    `n`-gons, modulo Euclidean motions.

  The case `n = 16` is taken from `T16`; `n ≥ 32` is proved analytically. The
  statement also covers `n` divisible by 16 that are not powers of 2.

