# Literature validation

This document explains what the general certifier (`src/SmallPolygons.jl`,
driver `pipeline/certify_literature.jl`) reproduces from the literature on
**maximal-perimeter convex equilateral small polygons**, and — just as
importantly — what it does **not**. It keeps four epistemic levels strictly
separate and never presents as demonstrated a result the literature does not
demonstrate.

Bibliographic basis: the references of the accompanying article (closed,
primary-source-verified). Run: `julia --project=. pipeline/certify_literature.jl`.

## The four epistemic levels (never conflated)

| Level | Meaning | Who establishes it |
|---|---|---|
| **THEOREM** | Global optimality **proven in the literature** | Vincze / Reinhardt / AHMP — **not** this framework |
| **PROVEN** (block) | Established here by **exact arithmetic** | this framework (e.g. A16 exact identities, in the dedicated certificate) |
| **CERTIFIED** (block) | Established here **rigorously by interval arithmetic** | this framework |
| **NUMERICAL** (block) | High-precision **floating diagnostic**, *not* a certificate | this framework |

The framework's job is the middle two: it **re-certifies the local first-order
structure** that a candidate has. It never re-proves (or claims) global
optimality — that is the literature's THEOREM for the solved cases, and is
**OPEN** for the powers of two `n = 2^s, s ≥ 4` (where `A16` lives).

## What the general certifier checks (per candidate, interval-rigorous)

For a candidate convex equilateral small `n`-gon it certifies, over the
certified point/box:

1. **existence** — for root-defined families, a true root of the constructor's
   defining equation exists in the box (interval IVT sign change). `:CERTIFIED`.
2. **equilaterality** — the side² enclosures are mutually consistent with one
   common value. Interval arithmetic can *refute* equality (disjoint
   enclosures) but not *prove* exact equality (Golden Rule); so this is
   `:CONSISTENT` for valid cases and `:FAIL` for negative controls. It was
   labelled `:CERTIFIED` until the 2026-09 external audit (D11) pointed out
   that the label reads as a certified equality; the equality itself is
   `:PROVEN` by the `exact_identities` block.
3. **active graph + inactive margin** — each declared active diameter encloses
   the diameter `1`; every other pair is strictly `< 1` (directed lower bound
   on the margin). `:CERTIFIED`.
4. **strict convexity + cyclic order** — all support determinants `> 0`
   (Lemma L2). `:CERTIFIED`.
5. **local constant rank `= 2n−2`** — a regular `(2n−2)×(2n−2)` minor of the
   constraint Jacobian (preconditioned interval regularity) plus the rigid-
   motion upper bound (Lemma L1: the two translations and the rotation are
   independent ⇒ `rank ≤ 2n−2`). Hence `dim I_eq = 3 = dim R_eq`, i.e.
   `I_eq = R_eq`. `:CERTIFIED`.
6. **multipliers** — LICQ status and strict positivity of every active-diameter
   multiplier, established by interval Krawczyk on the normalised stationarity
   system (`SmallPolygons.general_multipliers`), with the three gauge equations
   recovered exactly through the regular rigid-motion matrix `Q`. `:CERTIFIED`.
7. **exact_identities** — the side and active-diameter equalities proved by
   exact `Q(c,s)` algebra (`src/ExactIdentity.jl`), zero remainder, no interval
   containing zero. `:PROVEN`.

## Results (reproduced 2026-07; see `pipeline/certify_literature.jl` output)

| Case | n | Framework (local structure) | Literature result | LICQ |
|---|---|---|---|---|
| n4-regular-square (Vincze) | 4 | CERTIFIED/PROVEN/NA; equilaterality CONSISTENT | **THEOREM** (global optimum, unique) | holds (6=6) |
| n6-reinhardt-R₃,₆ (Reinhardt) | 6 | CERTIFIED/PROVEN/NA; equilaterality CONSISTENT | **THEOREM** (global optimum, unique) | fails by 2 |
| n8-ahmp2004-H₈ (AHMP 2004) | 8 | CERTIFIED/PROVEN; equilaterality CONSISTENT | **THEOREM** (global optimum, unique) | holds (14=14) |
| A16-bingane-audet | 16 | CERTIFIED/PROVEN; equilaterality CONSISTENT | **OPEN** (best known, not optimal) | fails by 1 |
| neg-broken-convexity | 16 | **REJECTED** (convexity FAIL) | negative control | — |
| neg-broken-equilateral | 16 | **REJECTED** (equilaterality FAIL) | negative control | — |
| neg-wrong-diameter | 16 | **REJECTED** (active-graph FAIL) | negative control | — |

A structural observation the benchmark surfaces honestly: **LICQ (constraint
independence) varies by case** — it holds for n=4 and n=8, and fails (by 2 for
n=6, by 1 for A16) where there are more active constraints than the rank
`2n−2`. This is a genuine structural difference, not an artifact.

### n=8 independent cross-check

Two independent primary characterizations of H₈ agree exactly: the squared side
length `u` produced by the OPTIGON `cstrt_vincze_ngon(8)` constructor is a root
of the Bingane–Audet degree-6 polynomial `2u⁶−18u⁵+57u⁴−78u³+46u²−12u+1` (in
`(sin²(π/8), 4sin²(π/16))`). Checked in the test suite.

## What this validation demonstrates

- The certifier is **generic in `n`** (n = 4, 6, 8, 16 with no `n`-specific
  code) and reproduces the **local first-order structure** of every literature
  candidate with reproducible data.
- It **distinguishes** proven theorems (n=4,6,8) from the open best-known
  construction (n=16) from numerical diagnostics, and labels each explicitly.
- It **rejects** invalid configurations (the three negative controls), so a
  positive verdict is not vacuous.

## What this validation does NOT demonstrate (scope limits)

- It does **not** prove global optimality of A16 or of any case. For n=4,6,8
  the global optimum is a **literature theorem**; the framework only
  re-certifies the *local* conditions those optima satisfy (a necessary-
  condition consistency check, not a re-proof).
- For `n = 8` the `existence` block certifies a root by a sign change and does
  not, by itself, certify uniqueness. The identification with the published
  AHMP optimum is closed separately and exactly: the AHMP degree-6 polynomial
  is squarefree and has exactly one real root in `[146/1000, 153/1000]`, an
  interval that strictly contains the one AHMP names, counted by a Sturm
  sequence in `Rational{BigInt}` with no floating point anywhere. See the
  `n=8 H8 cross-check` testset.
- The Julia framework does **not** prove Theorem 3.5 itself: it establishes that
  theorem's hypotheses for a given configuration. The implication is supplied by
  the Lean layer (`Feasible.thm_3_5`), not by this framework, and not by hand.
- The `equilaterality` and `active_graph+margin` blocks are interval
  **enclosures**, which per the Golden Rule are not proofs of exact equality.
  The exact equalities are supplied separately by the `exact_identities` block
  (`:PROVEN`, exact `Q(c,s)` algebra) — for every shipped family, not only A16.
  Read the two blocks together: the enclosure locates the value, the exact
  identity proves it.
- The `rank` and `multipliers` blocks describe the constraint set *at* the given
  configuration and are therefore reported `:NA`, not `:CERTIFIED`, whenever the
  `equilaterality` block has refuted feasibility.

## Reproducibility

`Project.toml`/`Manifest.toml` pin the environment. `certify_literature.jl`
prints a provenance header (UTC, Julia and IntervalArithmetic versions).
Adding a new case is pure data: drop an `cases/<case>/candidate.jl`
directory; no framework code changes.
