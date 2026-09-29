# The general Lean certificate of the family: one theorem for every `n = 16k`

`ChiquipoliFamily/Trig/` proves **once** the theorem

```
Chiquipoli.Family.Trig.published_of_checks
```

whose hypotheses are Boolean checks on finite data, and whose conclusion is the
statement of `A<n>/Published.lean`, about the published objects themselves:

> upstream's constructor equation `Optigon.F n` (OPTIGON `cstrt_audet_ngon`,
> transcribed in `ChiquipoliFamily/Optigon.lean`) has exactly one zero `z` in
> upstream's bracket `(2 asin(sin(π/n)/2), π/n)`, and the polygon upstream's
> code builds there is a strictly convex equilateral small `n`-gon and a
> **strict local maximiser of the perimeter, modulo orientation-preserving
> Euclidean motions** (and no nearby feasible polygon has a larger side).

Per `n`, only data changes: `lean/generators/family/gen_trig.py n` writes
`ChiquipoliFamily/T<n>/` (the data, seven files of `decide +kernel` checks, and
`Main.lean`, which applies the theorem) and `negative_controls_trig/T<n>/`.
**Nothing the generator writes is trusted**: every table, enclosure, graph,
shape witness, Henneberg order and stress enclosure is a claim the kernel
checks, and a wrong claim makes a check — and so the build — fail.

Currently generated: **A16, A32, A64, A128, A256**. (A16–A64 are thereby
covered twice in Lean: also by the per-case polynomial certificates of
`ChiquipoliFamily/A<n>/`, a different method.)

Verify: `./verify_trig.sh` (or `make lean-general`; one case:
`make lean-general-case N=256`). Per candidate, `make a<n>-complete` runs it.

## Why a second method

The per-case certificates (`A<n>/`) expand everything into polynomials in
`c = cos z`; the degrees grow with `n` and A64 already needs ~13 GB. Here
nothing is expanded:

* **Exact identities are proved once, symbolically.** `Term.lean` runs
  upstream's code on symbolic terms (`vertexS`), with `vertex_eval` proving that
  evaluating a symbolic vertex gives upstream's vertex. `Shapes.lean` and
  `FSide.lean` prove, for every `i`, the squared length of every kind of side
  and active diameter the code produces (`fan_qr`, `side_ur`, `cross_ut`,
  `side_qt`, …, and the two closing sides `closing`, `closing'`, whose squared
  length is `F_n(z) + (2 sin(z/2))²`, which uses `n/8` even). Per `n`, the
  kernel only compares each vertex's term with a witness shape (`W.fits`).
* **Inequalities from interval arithmetic** on fixed-point integers
  (`FI.lean`, `K = 384` binary digits): tables of `(cos kz, sin kz)` from a
  Taylor–doubling point enclosure (`Base.lean`, Mathlib's `cos_bound`,
  `sin_bound`) and a checked rotation recurrence, evaluated through the terms
  (`Interp.lean`). Convexity (`conv_sound`) and smallness (`far_sound`) follow.
* **The root**: sign change of `F_n` at the ends of a bracket of half-width
  `2^-180` (`root_exists`), and `F_n' < 0` on an interval containing upstream's
  whole bracket (`root_unique`, `FDeriv.lean`), located against Mathlib's
  twenty digits of `π` (`pi_div_mem`).
* **Rigidity** by a Henneberg order (`rigid_of_henneberg`), proved once;
  per `n` the kernel checks the order and the determinants' signs.
* **Multipliers** as a self-stress built by the reverse Henneberg recursion
  (`stressR`), which balances every vertex exactly (`bal_zero`, proved once);
  its interval enclosure is re-derived step by step by the kernel
  (`stress_encl`), which gives `λ > 0` and a negative side sum.
  `stationary_of_bal` and `mult_of_stationary'` feed `Feasible.thm_3_5`.

## The root, for every `n` (`RootAll.lean`)

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

Steps 1–3 of `verify_trig.sh` build the module, scan it for admitted goals,
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
* `ConstructorAll.lean`. From the layout and the identities of `Shapes.lean`:
  * `chords_all`: every pair of `G_n` is at distance `1`;
  * `sides_all`: every non-closing side is `2 sin(z/2)`;
  * `closing_all`, `closing'_all`: each closing side has squared length
    `F_n + ℓ²`.

  `published_all` combines these with `root_all`: for every `n = 16k`, the
  unique zero of `F_n` in `(0, π/n)` is simple, and there the published polygon
  is equilateral, has unit distance on every pair of `G_n`, and is
  infinitesimally rigid.

**Not yet proved for every `n`:**
* convexity;
* that no pair outside `G_n` reaches distance `1` (Problem 1);
* positivity of the multipliers (Problem 3).

Until those are proved, the local-maximality statement for all `n` is not
proved: `published_of_checks` covers `n = 16 … 256` only, through per-case
kernel checks.

## The checks, per `n`

| file | checks |
|---|---|
| `Checks1` | the bracket (integers, `π` bounds), `sin` comparisons at the bracket ends, the four tables, the sign change and `F' < 0` |
| `Checks2` | every symbolic vertex equals upstream's code run symbolically; the vertex enclosures |
| `Checks3` | strict convexity: all `n(n−2)` support determinants |
| `Checks4` | every non-active pair at distance `< 1`; every pair of `G_n` is in the edge list |
| `Checks5` | every side and active diameter matches a shape witness |
| `Checks6` | the bar list, the Henneberg order, the determinant signs |
| `Checks7` | the stress recursion in intervals, the pinned bar, coverage, `λ > 0`, the side sum `< 0` |

## Negative controls

Twelve per case (`negative_controls_trig/T<n>/`): each is a check on tampered
data — a vertex term replaced, a table entry replaced, an enclosure shrunk, two
vertices exchanged, no pair declared active, an edge dropped, a wrong or
mirrored shape witness, the root bracket reversed, a Henneberg step on an
unplaced vertex or with a degenerate pair, the pinned stress claimed to be
`0`. `verify_trig.sh` requires the kernel to **refute** each (not merely fail
to elaborate it), and its twin — the same check on the true data — to compile.
