# ChiquipoliFamily — the Bingane–Audet family `A_n`, verified in Lean 4

This library proves, for members of the Bingane–Audet family `A_n`
(`n = 2^s ≥ 16`), the same statement that `ChiquipoliLean` proves for A16:

> there is a root of the constructor equation in the article's search interval,
> it is the only one there, and the polygon it builds is a strictly convex
> equilateral small `n`-gon that is a **strict local maximiser of the
> perimeter, modulo orientation-preserving Euclidean motions**.

It is built separately from `ChiquipoliLean` (`lake build ChiquipoliFamily`,
not a default target) and verified separately (`./verify_family.sh`, or
`make lean-family` from the repository root). Nothing in `ChiquipoliLean/`,
`verify.sh`, or the counts the article quotes depends on it.

Currently generated: **A16** (a second, independent proof of the A16 result,
by a different method), **A32** and **A64**.

## The headline theorems

| Lean name | Statement |
|---|---|
| `Chiquipoli.Family.A<n>.locally_maximal_unique` | the full statement above |
| `Chiquipoli.Family.A<n>.locally_maximal_at` | the same conclusion at *every* root `c ∈ (clo, chi)` |
| `Chiquipoli.Family.A<n>.locally_maximal` | existence form, without the search interval |

They apply the general `Chiquipoli.Feasible.thm_3_5` (Theorem 3.5, proved once
for every `n` in `ChiquipoliLean/Theory/`), whose hypotheses each case discharges:

| hypothesis of Theorem 3.5 | proved by | method |
|---|---|---|
| equilateral, active diameters `= 1` | `equilateral`, `active_eq` | exact identities in `Q[c]` (`ring`, `linear_combination` with `Fc`) |
| strictly convex, labelled cyclic order | `convexOrdered` | all `n(n−2)` support determinants, from vertex enclosures |
| small (every pair `≤ 1`) | `small` | every non-active pair `< 1`, from vertex enclosures |
| (i) multiplier identity, `λ > 0` | `stationary`, `side_sum`, `lam_pos` | **self-stress by the Henneberg recursion** (below); positivity by enclosure arithmetic |
| (ii) `I_eq ⊆ R_eq` | `Ieq_imp_R` | **Henneberg construction** (below) |

## The method, and why A16's does not scale

`ChiquipoliLean` certifies every sign condition with one Bernstein certificate
per polynomial, and the rank by dense elimination over `Q[c]/(Fc)`. Both were
measured at `n = 32` before this library was written:

* one support determinant of A32 is a degree-29 polynomial; its Bernstein
  certificate alone costs 38 s and 2.2 GB, and A32 has 960 of them. A single
  file of 300 of them exceeded 73 GB of memory and was stopped.
* the A16 rank certificate already costs 160 s and 13.6 GB at `n = 16`.

`Basic.lean` replaces both, with lemmas proved **once for every `n`**:

1. **Two layers for every sign condition.** Only the `2n` vertex coordinate
   polynomials (degree `≤ n/2 − 1`) are expanded: each is enclosed,
   `|XC_k(c) − x̂_k| ≤ ρ`, on a rational interval of width `≈ 10⁻⁹` around the
   root, by a centred Taylor expansion (`tbound`). Every support determinant
   (`det_lb`) and every inactive distance (`sqd_ub`) then follows from those
   enclosures by a lemma proved once; each instance is rational arithmetic for
   `norm_num`. `O(n)` polynomial certificates instead of `O(n²)`.

2. **Rigidity by a Henneberg construction.** `I_eq ⊆ R_eq` is infinitesimal
   rigidity of the bar framework (sides and active diameters). Pin one side by a
   rigid motion (`pin_bar`); then add the vertices one at a time, each joined to
   two already pinned vertices by bars with independent directions
   (`henneberg_step`). That is `n − 2` two-by-two determinants, each again from
   the enclosures. No elimination, no `Fc`.

3. **The multipliers are a self-stress, built by the same Henneberg order.**
   The multipliers of the squared formulation are a self-stress of the bar
   framework: weights on the bars that balance at every vertex. The two bars
   the Henneberg construction does not use — which turn out to be exactly the
   two sides that hold only at the root of `Fc` — carry rational stresses; in
   reverse Henneberg order, each vertex fixes its two Henneberg bars by
   Cramer's rule (`cramer_bal`, with the same nonzero determinant as the
   rigidity proof), the pinned side is fixed last (`pin_bal`), and vertices
   `0`, `1` balance by the global force and moment identities. The equilibrium
   holds on the whole interval — **no `Fc` is needed** — and positivity of the
   diameter stresses, and a negative sum of side stresses, follow by centred
   enclosure arithmetic (`add_close`, `mul_close`, `div_close`, `recenter`).
   `mult_of_stationary'` turns this into the multiplier identity of `dataOf`
   with `κ = −ℓ Σα > 0`.

   This replaced a first design that computed an exact multiplier witness in
   `Q[c]/(Fc)`: at `n = 64` that witness took 51 min to compute and one
   positivity certificate of degree 59 took 314 s and 9.7 GB in Lean.

Every margin is checked in exact rational arithmetic by the generator **before**
any Lean is written; Lean then re-checks everything in the kernel.

## Cost

| | A16 (this library) | A32 | A64 |
|---|---|---|---|
| generated files | 22 | 46 | 132 |
| generator run | 4 s | 5 s | 7 s |
| support determinants | 224 | 960 | 3968 |
| inactive pairs | 105 | 465 | 1953 |
| Henneberg steps | 14 | 30 | 62 |
| vertex enclosure radius `ρ` | `9·10⁻¹⁶` | `7·10⁻¹⁵` | `7·10⁻¹⁴` |
| smallest certified diameter stress | `0.0141` | `0.00161` | `0.000186` |

Build times and peak memory are recorded in the CHANGELOG entry for the run
that produced these files.

For comparison, the A16 layer of `ChiquipoliLean` needs 160 s and 13.6 GB for
its rank certificate alone.

Large certificates are split into chained files (`Conv1 → Conv2 → …`): Lean
keeps every proof of a file in memory while it elaborates that file, and the
chain also keeps `lake` from building several heavy files at once.

## Where the data comes from

`lean/generators/family/gen_family.jl <n>` writes `ChiquipoliFamily/A<n>/`. Its
inputs are the repository's own exact arithmetic: the generic OPTIGON
constructor `audet_generic` and `audet_Fc` in `cases/exact_coords.jl`
(cross-checked against the upstream constructor in `test/literature.jl`), and
the active graph and root of `cases/A<n>_bingane_audet/candidate.jl`. The
coordinates are reduced to `(sin z · XC(c), YC(c))` with `XC, YC ∈ Q[c]` by
exact division by `cos 2z`, which the generator asserts. `verify_family.sh`
re-runs the generator and requires every file to reproduce byte for byte.

## What is not (yet) in Lean here

* **The trigonometric constructor.** `ChiquipoliLean` transcribes the A16
  constructor by hand and proves it equal to its polynomial form (`red*`). Here
  the configuration is *defined* by its polynomial form, `P z`, and `Fc` by
  Proposition 1. That this is the Bingane–Audet `A_n` rests on the Julia tests
  (the generic constructor reproduces upstream OPTIGON to `10⁻⁷⁰`, and at
  `n = 16` reproduces `A16Certificate` exactly), not on Lean.
* **Global optimality.** As for A16, nothing here says anything about it.
