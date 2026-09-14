# Changelog

All notable changes to this project are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [1.0.0] — 2026-09-09

First public release: the supplementary material for *Stability of Equilateral
Small Polygons*.

### What it establishes

- **The certificate.** Eight gates on the Bingane–Audet hexadecagon `A16`,
  by outward-rounded interval arithmetic at 256-bit precision and by exact
  rational algebra in `Q[c]`: the constructor root exists and is unique in the
  search interval, the sixteen side and fifteen active-diameter equalities hold
  exactly, the configuration is strictly convex in the labelled cyclic order,
  every inactive diameter is strictly slack, the multipliers are certified
  strictly positive, and `rank D(e,d) = 30`, hence `I_eq = R_eq`.
- **The formal layer.** Lean 4, checked against a pinned Mathlib revision, with
  no interval arithmetic and no floating point. It re-derives the computational
  hypotheses by kernel-checked rational arithmetic, and proves the article's
  Theorem 3.5 itself — the local Euclidean slice, openness of convexity and the
  inactive margin, the first-order limits, invariance under Euclidean motions,
  and the blow-up. `Feasible.A16_locally_maximal` is the article's Theorem 6.3
  and `Feasible.square_strict_local_max` its Proposition 4.2, so the passage
  from the certified data to strict local maximality is machine-checked end to
  end.
- **The general framework.** The same code path certifies the first-order
  structure at the equilateral optima known for `n = 4, 6, 8`, and refuses
  three deliberately broken variants of `A16`.

### How it guards itself

- 628 test assertions; `Pkg.test()` runs them.
- 107 Lean theorems audited, depending on `propext`, `Classical.choice` and
  `Quot.sound` only, with 32 required by name so that coverage cannot drift.
- 26 negative controls, each a deliberately false variant that must fail to
  compile — what shows the true statements are not vacuous.
- 12 planted defects, each of which the checks must reject
  (`tools/mutation_check.sh`).
- Seven generated Lean files reproduce byte for byte from the Julia source.
- SHA256 of every load-bearing source file, with the count pinned: the
  provenance scan is directory-driven and non-recursive, so a file moved out of
  `src/`, `scripts/` or `test/` would otherwise drop out of the hash chain in
  silence.
- `scripts/check_paper.jl` reconciles the article — its tables, bounds, figure
  coordinates, structural counts, claims about Lean, and the commands it prints
  — against the regenerated certificate and the Lean sources.

### Known limits

Stated in full in `docs/scope-and-limitations.md`. In short: the theorem is
local and yields no lower bound on the radius of the neighbourhood; global
optimality is not addressed; and no proof assistant establishes that the
certified configuration is the published Bingane–Audet polygon — that is an
attribution, checked by running the upstream OPTIGON constructor and comparing
coordinates.
