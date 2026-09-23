# Limitations and exact scope of the general framework

Maximum scientific honesty. This document states, per certified property, what
the general certifier (`src/SmallPolygons.jl`) **proves**, what it **does not
prove**, which hypotheses it uses (including ones that were implicit and are now
explicit), and how the blocks depend on one another. Every claim below is
backed by a theorem, a reference, or a certificate; nothing is asserted beyond
what the computation establishes.

Companion documents: `docs/guide/literature-validation.md` (results), the closed
bibliography recorded in `docs/guide/literature-validation.md`, and the full
A16-only certificate `docs/guide/provenance-mapping.md`.

## 0. Status update — the full first-order certificate is now GENERAL

An earlier version of this document listed, as the single most important
limitation, that the general framework certified only the local first-order
*structure* (`I_eq = R_eq`) and not the full strict first-order certificate,
because positive multipliers were a NUMERICAL diagnostic and the exact
identities were A16-only. **Both blockers (referee R1 and R2) are now closed**
as general capabilities (see `docs/guide/general-framework.md`):

- **R1**: `SmallPolygons.general_multipliers` certifies, by interval Krawczyk,
  a KKT multiplier vector with all active-diameter multipliers `> 0`, for any
  candidate (variable LICQ defect). The `multipliers` block is `:CERTIFIED`.
- **R2**: `src/ExactIdentity.jl` proves the side/diameter equalities exactly in
  `Q(c,s)` for every family. The `exact_identities` block is `:PROVEN`.

So for `n = 4, 6, 8, 16` the framework now certifies the full hypotheses of the
paper's Corollary "first-order strict case". The residual limitations below are
the ones that remain genuinely open or by-design.

## 1. Logical dependency graph of the blocks

```
                 coords(candidate)   [enclosed over box / at the point]
                   │  │  │  │
      ┌────────────┘  │  │  └───────────────┐
      ▼               ▼  ▼                   ▼
 equilaterality   active_graph            convexity ──────┐   existence
 (enclosure;       + margin               (support dets>0,  │   (IVT sign
  refutable)       (encl. actives;        Lemma L2)         │    change;
      │             strict inactive<1)         │            │    root cases)
      │                    │                   │  (L1: distinct vertices)
      │                    │                   ▼            ▼
      │                    │             rank UPPER bound (≤2n-2, algebraic
      │                    │             theorem: exact annihilation + L1)
      │                    │                   │
      │                    │      rank LOWER bound (≥2n-2, interval regular minor)
      │                    │                   │
      │                    │                   ▼
      │                    │             rank = 2n-2  ⇒  I_eq = R_eq
      │                    │                   │
      └────────────────────┴───────────────────┤
                                                ▼
                        multipliers (CERTIFIED by interval Krawczyk; the LICQ
                        defect interpretation uses the certified rank)

  Strict first-order certificate  =  (I_eq = R_eq)  AND  (positive multipliers)
                                     └─ CERTIFIED ─┘      └───  CERTIFIED  ───┘
                                                          (general in n; see §0)
```

Key non-obvious edge (fixed this round): **rank's upper bound depends on the
convexity block.** `rank ≤ 2n-2` needs the three rigid motions to be linearly
independent (Lemma L1), which holds only because certified convexity forces the
vertices to be distinct. If convexity is not certified, the rank block cannot
certify the upper bound and reports `:FAIL` (observed on the broken-convexity
negative control).

## 2. Per-property audit

### existence (root-defined candidates: n8, A16)
- **Proves:** a true real root of the constructor's defining equation `F` lies
  in the box, by a certified sign change of `F` at the box endpoints
  (Intermediate Value Theorem; `F` continuous). `:CERTIFIED`.
- **Does NOT prove:** uniqueness of the root in the box or in the search
  interval. The general framework does **not** certify monotonicity of `F`.
  (A16's dedicated certificate does prove uniqueness, via `0 ∉ F'(search)`.)
- **Hypotheses:** `F` interval-evaluable and continuous; box brackets a sign
  change. **Implicit hypothesis, now stated:** that the box is centred on the
  intended root — the nominal value is taken from the constructor, not
  independently isolated here.
- **Depends on:** nothing (independent of the other blocks).

### equilaterality
- **Proves:** all side² lie in a common certified interval `[maxinf, minsup]`,
  i.e. the sides are equal **to within the certified spread** `minsup−maxinf`
  (≈ rounding width for the benchmark cases). It can also **rigorously refute**
  equality (disjoint side² enclosures ⇒ sides differ; used by the negative
  control). `:CONSISTENT` for the consistency/spread bound (it was `:CERTIFIED`
  until the 2026-09 external audit, D11); `:FAIL` on refutation.
- **Does NOT prove:** exact equality of the sides. Per the project's Golden
  Rule, overlapping interval enclosures are **not** a proof of exact equality.
  Exact equilaterality holds **by construction** (an algebraic identity of the
  literature constructor) and is proven exactly by the separate
  `exact_identities` block, for every shipped family (`src/ExactIdentity.jl`),
  not only for A16. In *this* block it is enclosed/consistency-checked, not
  proven; read the two blocks together.
- **Depends on:** coords only.

### active_graph + margin
- **Proves:** every declared active pair's distance² **encloses** the diameter
  `1`, and every undeclared pair's distance² has certified `sup < 1` (a
  directed lower bound on the inactive margin `1 − max|p_i−p_j|`). This both
  certifies the strict inactive margin and **validates the declared active
  graph in both directions** (a declared-active pair that were not at distance 1,
  or an undeclared pair that reached 1, would `:FAIL`).
- **Does NOT prove:** that the active distances are *exactly* 1 (same Golden-Rule
  caveat as equilaterality — active diameters equal 1 by construction, enclosed
  here). It also does not prove the polygon's diameter equals 1 as an
  independent fact; that rests on the active distances being 1 by construction
  together with the certified `<1` for all other pairs.
- **Depends on:** coords + the declared active graph (candidate data).

### convexity
- **Proves:** all support determinants `H_{i,j} = det(p_{i+1}−p_i, p_j−p_i) > 0`
  (certified interval lower bound), hence the polygon is strictly convex, simple,
  and in the declared labelled cyclic order (Lemma L2, a standard orientation
  criterion). `:CERTIFIED`. In particular the vertices are pairwise distinct.
- **Does NOT prove:** anything about optimality; convexity is a feasibility/
  regularity property.
- **Hypotheses:** Lemma L2 (cited standard result: all vertices strictly to the
  left of every directed edge ⟺ strictly convex simple polygon in that order).
- **Depends on:** coords only. **Feeds:** the rank upper bound (via L1).

### rank = 2n−2 (⇒ I_eq = R_eq)
- **Proves:** `rank D(e,d) = 2n−2` at the certified point/box, hence
  `dim I_eq = 3 = dim R_eq`, hence `I_eq = R_eq` (the equality tangent space is
  exactly the rigid-motion space). `:CERTIFIED`.
  - Lower bound `≥ 2n−2`: **interval-rigorous** (a regular `(2n−2)×(2n−2)` minor,
    preconditioned regularity `‖I−CM‖_∞ < 1`).
  - Upper bound `≤ 2n−2`: an **algebraic theorem**, not a numerical check — the
    three rigid motions annihilate every distance constraint exactly (translation:
    endpoint velocities cancel; rotation: `(p_i−p_j)·(v_i−v_j)=0`), and they are
    independent by Lemma L1 (distinct vertices, from certified convexity). The
    reported `max|Aρ|` (≈1e-77) is a **numerical sanity check only**, never the
    basis for the bound.
- **Does NOT prove:** the full strict first-order maximality (needs positive
  multipliers, see below). It gives the rank **at the configuration**, which is
  all Theorem 3.5 consumes; it says nothing about the rank at neighbouring
  configurations, and nothing needs it to — see §3.
- **Hypotheses:** certified convexity (for L1); the annihilation identity
  (unconditional). **Depends on:** convexity (upper bound) + coords (minor).

### multipliers (R1 — now CERTIFIED, general)
- **Proves:** existence of a KKT multiplier vector with the stationarity identity
  `D^T y = DL` and all active-diameter multipliers `λ_ij > 0`, by interval
  Krawczyk on a square normalized system, with the 3 omitted stationarity
  equations recovered via a certified-regular rigid-motion matrix `Q`
  (`SmallPolygons.general_multipliers`). `:CERTIFIED`.
- **Does NOT prove:** uniqueness of the multiplier. When LICQ fails (n6, A16) the
  multipliers are a `d`-parameter family (`d = #active − (n−2)`); positivity is a
  property of the certified representative, and exhibiting one positive
  representative is exactly what the first-order lemma needs (not a canonical
  multiplier).
- **Depends on:** coords (Jacobian), the certified rank (gauge/normalization
  counts), and certified convexity (distinct vertices ⇒ regular `Q`).

## 3. Box vs. neighbourhood (openness)

For root-defined candidates (n8, A16) the certification runs over a genuine
interval **box in the scalar parameter `z`**, i.e. a one-parameter family of
configurations. For fixed candidates (n4, n6) it runs at the **exact point**
(thin interval enclosure of the algebraic coordinates).

Earlier revisions of this file recorded, as a limitation, that the computation
does not establish constant rank on a full `R^{2n+1}` neighbourhood, and
attributed such a hypothesis to the paper. **That is no longer accurate and
should not be read as an open gap.** Theorem 3.5 as it now stands assumes
nothing about `D(e,d)` at neighbouring configurations — not that its rank is
locally constant, not that the constraint set is a smooth manifold nearby, and
no higher-order information; its Remark on hypotheses used says so explicitly.
What the theorem consumes is the pointwise identity `I_eq = R_eq` at the single
configuration `(p, ℓ)`, and pointwise `rank = 2n−2` is exactly what is
certified. No openness or continuity argument external to the computation is
load-bearing anywhere in the chain.

## 4. The LICQ pattern — reported as an experimental observation

The benchmark exhibits: LICQ **holds** for n=4 and n=8, and **fails** for n=6
(by 2) and A16 (by 1). We report this honestly and do **not** promote it to a
theorem.

- **What is certified per case:** the LICQ defect equals
  `#constraints − rank = (n + #active) − (2n−2) = #active − (n−2)`. This identity
  is elementary **given the certified rank `2n−2`**; it is verified for all four
  cases (n4: `2−2=0`; n6: `6−4=2`; n8: `6−6=0`; A16: `15−14=1`). So LICQ holds
  iff the polygon has exactly `#active = n−2` unit diameters.
- **Connection to the literature (not a derivation):** the number of unit
  diameters is the size of the *diameter graph*, whose maximum on `n` planar
  points is `n` (Hopf–Pannwitz, 1934), and Vincze's necessary condition
  (Vincze 1950, cited in Bingane–Audet 2022 §1) requires every vertex to have an
  opposite vertex at diameter distance. These constrain `#active` but we do not
  derive the LICQ pattern from them.
- **What we do NOT claim:** we make **no** general theorem that LICQ holds/fails
  for any family, and we are **not aware** of a published result stating LICQ
  (or KKT multiplier non-uniqueness) for the maximal-perimeter equilateral
  polygon problem. This is a computational observation on four instances, and is
  labelled as such. Extending it to a proof (e.g. characterising `#active` for
  the `A_n` family) is future work, not a present claim.

## 5. Soundness vs. completeness of the minor selection

`select_minor` picks the certified `(2n−2)`-minor by Float64 QR column
pivoting. This is a **heuristic for selection only**; the certificate itself is
the subsequent interval regularity test, so a positive verdict is always
sound. The heuristic could in principle fail to find a regular minor even when
one exists, yielding a spurious `:FAIL` (a **completeness**, not a soundness,
gap). No false `:CERTIFIED` can arise from it.

## 6. What depends on the literature vs. on our certificates

- **On the literature (theorems we do NOT re-prove):** that n=4, 6, 8 are
  *global* optima (Vincze / Reinhardt / AHMP 2004); that A16 is the best known
  construction and beats Mossinghoff (Bingane–Audet 2022); the constructor
  formulas themselves (OPTIGON, taken as definitions of the candidates).
- **On our certificates (established here):** the local first-order structure
  (existence [IVT], convexity, active graph + strict margin, rank `= 2n−2 ⇒
  I_eq = R_eq`) by interval arithmetic; for A16 additionally the exact side/
  diameter identities and interval-certified positive multipliers (dedicated
  module). Global optimality is **never** claimed for any case, and no
  second-order property is claimed (vacuous where `I_eq = R_eq`).

## 7. Reproducibility caveats

The `Manifest.toml` pins package versions and `pipeline/certify_literature.jl`
writes `results/validation_certificate.toml` (git commit, source SHA-256, UTC,
Julia and package versions, per-block epistemic states, timing) on every run.
Reconstruction requires the same Julia minor version; interval results are
independent of hardware given IEEE-1788 directed rounding, but timings are not.
