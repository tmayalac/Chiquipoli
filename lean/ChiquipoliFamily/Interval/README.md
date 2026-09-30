# The interval method: one theorem for every `n = 16k`, data per case

`ChiquipoliFamily/Interval/` proves **once** the theorem

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
`ChiquipoliFamily/Interval/T<n>/` (the data, seven files of `decide +kernel` checks, and
`Main.lean`, which applies the theorem) and `negative_controls_interval/T<n>/`.
**Nothing the generator writes is trusted**: every table, enclosure, graph,
shape witness, Henneberg order and stress enclosure is a claim the kernel
checks, and a wrong claim makes a check — and so the build — fail.

Currently generated: **T16, T32, T64, T128, T256** (A16 … A256). (A16–A64 are thereby
covered twice in Lean: also by the per-case polynomial certificates of
`ChiquipoliFamily/Polynomial/A<n>/`, a different method.)

Verify: `./verify_general.sh` (or `make lean-general`; one case:
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

Twelve per case (`negative_controls_interval/T<n>/`): each is a check on tampered
data — a vertex term replaced, a table entry replaced, an enclosure shrunk, two
vertices exchanged, no pair declared active, an edge dropped, a wrong or
mirrored shape witness, the root bracket reversed, a Henneberg step on an
unplaced vertex or with a degenerate pair, the pinned stress claimed to be
`0`. `verify_general.sh` requires the kernel to **refute** each (not merely fail
to elaborate it), and its twin — the same check on the true data — to compile.

## The proof for every `n` with no data

The directory `../AllN/` proves the same statement for every `n = 16k`
analytically; see `../AllN/README.md`. It reuses the symbolic run (`Term.lean`),
the shape identities (`Shapes.lean`, `FSide.lean`), the derivative of `F`
(`FDeriv.lean`) and the Henneberg and stress lemmas of this directory.
