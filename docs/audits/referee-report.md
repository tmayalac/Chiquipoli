# Adversarial referee report (self-review, DCG standard)

Written in the voice of a hostile *Discrete & Computational Geometry* referee
whose goal is to **reject**. Each point: severity, impact, and how to resolve.
Nothing here is a defense.

> **STATUS: THIS IS A HISTORICAL SNAPSHOT, NOT A DESCRIPTION OF THE CURRENT
> CODE.** It records the objections raised at one point in the project's
> development and is kept as a record of what was found and what was done about
> it. Several findings have since been resolved, and reading them as live
> statements about the present artifact would be wrong. In particular **R1 and
> R2 below are CLOSED**: the multiplier block is now `:CERTIFIED` for every
> candidate by interval Krawczyk (`SmallPolygons.general_multipliers`), and the
> side and active-diameter equalities are now `:PROVEN` for every shipped
> family by exact `Q(c,s)` algebra (`src/ExactIdentity.jl`) — not for `A16`
> alone. See `docs/scope-and-limitations.md` §0. For the current state, read
> `README.md`, `docs/certificate-spec.md` and `docs/provenance-mapping.md`; for a
> current adversarial reading, regenerate one rather than trusting this file.
> **R5 is also CLOSED for A16**: `test/optigon_reference.jl` vendors the
> upstream general `n = 2^s` constructor line for line (with its URL, retrieval
> date, upstream SHA256 and licence recorded), and the test suite requires it to
> reproduce `A16Certificate.coordinates` — root, all sixteen vertices, the
> diameter graph, equilaterality and the perimeter. The certified object is
> therefore identified with the published one by computation, not by assertion.

Recommendation (honest): **major revision.** The mathematics that is claimed is
sound, but the framing over-promises relative to what the general framework
actually certifies, and the empirical scope is thin. None of the findings are
fatal; all are addressable.

---

## Severity: HIGH

### [CLOSED] R1. The "first-order certifier" is, for 3 of 4 cases, only a *structural* certifier
The paper's own theorem (Corollary "first-order strict case") requires
`I_eq = R_eq` **and** positive KKT multipliers. The general framework certifies
only the first; multipliers are a `:NUMERICAL` diagnostic. So for n=4, 6, 8 the
framework does **not** deliver a first-order certificate — it delivers the
geometric + rank structure (`I_eq = R_eq`). Calling the tool a "first-order
certifier" and printing "CERTIFIED" (even with an asterisk) invites a reader to
over-read the result.
- **Impact:** central to the paper's claim. A referee will demand that either
  (a) the general framework certify positive multipliers rigorously (interval
  Krawczyk on the normalized stationarity system, handling the variable LICQ
  defect), or (b) the contribution be re-scoped and re-titled as a *structural*
  (I_eq = R_eq) certifier, with the strict first-order certificate claimed only
  for A16.
- **Resolution:** implement general interval multipliers (the A16 machinery
  generalizes: normalize `defect` degrees of freedom, Krawczyk-enclose, certify
  `λ>0`), OR restrict the strict-certificate claim to A16 and rename elsewhere.
  Documented honestly in `docs/scope-and-limitations.md` §0, but documentation is not a
  substitute for correct titling.

## Severity: MEDIUM–HIGH

### [CLOSED] R2. The equality constraints are not proven — only enclosed
"equilaterality: CERTIFIED" and "declared actives enclose diameter 1" are
interval enclosures. By the project's own Golden Rule, an enclosure that
contains a value does not prove the value. Exact equilaterality and unit
diameters hold *by construction* of the OPTIGON formulas and are proven exactly
**only for A16**. A referee will say: you cannot label as CERTIFIED a property
you explicitly cannot prove without exact identities.
- **Impact:** undermines the "CERTIFIED" column of Table 2 for the equality
  properties; the honest content is "equal to within a certified spread ε" plus
  "exact by construction."
- **Resolution:** port the A16 exact-identity (Chebyshev reduction) machinery to
  the Reinhardt and Vincze/Audet families (all have closed-form coordinates), so
  the equalities become `:PROVEN`; or relabel these entries to make the
  enclosure-vs-equality distinction explicit in the table itself, not only in
  the caption.

### R3. Empirical scope is thin (four instances)
A paper proposing a *general, n-independent* framework that demonstrates it on
four hand-picked polygons is weak. Two of the four (n=4, n=8) have LICQ holding
and small active graphs; the generality argument (works for any `n`) is asserted
by construction, not demonstrated across a range.
- **Impact:** reviewers of a "framework" paper expect breadth.
- **Resolution:** add the deferred extended benchmarks (Mossinghoff `M_16`,
  `A_32`, more Reinhardt `R_{m,n}` for several `m,n`), and ideally a sub-optimal
  and an infeasible family, to show the certifier discriminates across a range,
  not just on curated optima.

## Severity: MEDIUM

### [CLOSED] R4. Existence is certified, uniqueness is not (general path)
For n=8 the framework certifies a root exists in the box (IVT) but not that it
is unique, nor that the box brackets *the* AHMP optimum rather than some other
nearby root. The nominal centre is taken from the constructor. A referee will
ask: how do you know the certified configuration is the published H8?
- **Impact:** the identification "certified object = literature optimum" is not
  fully closed for n=8 in the general path.
- **Resolution:** add the monotonicity certificate (`0 ∉ F'(search)`), as A16
  already has; and cite the degree-6-polynomial cross-check (already in the
  tests) as the identification argument.
- **[CLOSED, and by a stronger route than the one proposed above.]** A
  monotonicity certificate would isolate a root of the *constructor equation*;
  what a referee actually asks is whether the certified object is the published
  optimum. The suite now settles that by an exact **Sturm count** on the AHMP
  degree-6 polynomial: the sextic is squarefree, and it has **exactly one** real
  root in the rational interval `[146/1000, 153/1000]`, which strictly contains
  the interval `(sin²(π/8), 4sin²(π/16))` that AHMP names — the two containments
  being themselves certified with an enclosed `π`. Since the constructor's
  `u = side²` roots that sextic and lies in the interval, `u` is *the* AHMP root,
  and the configuration is H8. Everything in the count is `Rational{BigInt}`:
  no floating point and no interval arithmetic enters it, so it is a proof and
  not an enclosure. Non-vacuity is asserted too — the same chain counts four
  real roots over `[-10, 10]`.

### [CLOSED] R5. Candidates are defined by external (OPTIGON) code
The certified objects are whatever the reimplemented OPTIGON formulas produce.
If a formula were transcribed wrongly, the framework would faithfully certify
the wrong polygon. Only n=8 has an independent algebraic cross-check (the
degree-6 polynomial); n=4, n=6, A16 are cross-checked only by perimeter.
- **Impact:** the chain "literature optimum → our candidate" rests on
  transcription fidelity.
- **Resolution:** add an independent cross-check per case (e.g., match published
  coordinates or an invariant), not only the perimeter.

## Severity: LOW

### R6. The LICQ pattern is anecdotal
Four data points and an elementary formula (`defect = #active − (n−2)`). It is
honestly labelled as an observation, but it is not a result and slightly
inflates the "findings."
- **Resolution:** either characterize `#active` for the `A_n` family (turning it
  into a theorem) or present it purely as a remark. Do not table it as if it
  were a contribution.

### R7. Trust base (openness half now MOOT)
The certificate trusts `IntervalArithmetic.jl`'s IEEE-1788 rounding: standard in
validated numerics, but not formally verified here. It is mitigated, not
removed, by the directed-rounding self check in the provenance header and by the
`isguaranteed` gate now asserted at every step, neither of which proves MPFR
correct.
- **Resolution:** state the trust base explicitly (done in `docs/scope-and-limitations.md`);
  optionally cross-validate a case in a second interval library.
- **[The second half of this item is MOOT.]** It used to add that "constant rank
  in an `R^{2n+1}` neighbourhood" rests on an openness argument external to the
  code. Theorem 3.5 in its current form assumes nothing about `D(e,d)` at
  neighbouring configurations — not that its rank is locally constant, not that
  the constraint set is a smooth manifold nearby — so no neighbourhood rank
  statement is needed and no openness argument is load-bearing anywhere in the
  chain. Pointwise rank is both what is certified and what is consumed. See
  `docs/scope-and-limitations.md` §3.

### R8. `select_minor` completeness
A Float64 pivot heuristic chooses the certified minor; it could spuriously
`:FAIL` (never spuriously `:CERTIFIED`). Sound but not complete.
- **Resolution:** fall back to trying alternative minors on failure.

## Meta-limitation (out of the framework's scope, must be acknowledged)

The whole edifice re-certifies the *hypotheses* of the paper's theorems; it does
**not** verify the theorems themselves (§3–§5, §8 of the source paper). Their
correctness is a human-review matter, independent of any amount of interval
computation.

---

## What a fair referee would concede
The soundness of the CERTIFIED claims is not in question (the rank upper bound
was, this round, moved from a non-rigorous numerical check to an algebraic
theorem + dependency on certified convexity; the lower bound is interval-
rigorous). The honesty apparatus (epistemic labels, LIMITATIONS, the reproducible
certificate) is unusually strong. The blocking issues are **scope and framing**
(R1–R3), not incorrectness.
