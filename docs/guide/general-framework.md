# A certification theory for the local first-order certificate

**Revised after the adversarial audit `docs/audits/theory-audit.md`.** This document is
self-contained. It states precisely what is *proved here*, what is *inherited
from the literature*, what is *certified by machine computation*, and what
*conclusion* follows by applying a corollary of the source paper. A referee
should be able to tell these four apart at a glance; they are labelled
throughout as **[THEORY]**, **[LIT]**, **[CERT]**, **[CONCL]**.

Scope claim, stated once and honestly: the results below concern the **class
`C`** of §1 — polygons whose coordinates are algebraic functions of a *single*
angle. They are established for the four benchmark families (regular square,
Reinhardt `R_{3,6}`, Vincze/AHMP `H8`, Audet `A16`) and, at the level of the
engine, for any member of `C`. We do **not** claim more.

---

## 0. Nature of the results: sound, incomplete, certificate-producing

All computational claims here are produced by **result-verification methods** in
the sense of validated numerics (Moore–Kearfott–Cloud 2009; Neumaier 1990;
Rump, *Verification methods*, Acta Numerica 2010; Tucker, *Validated Numerics*
2011). Such a method (interval Newton/Krawczyk, preconditioned regularity, exact
rational reduction) tests a **sufficient condition**:

- when the condition holds, the method **emits a certificate that is an
  unconditional, rigorous proof** of the statement;
- when it does not hold, the method returns **"not certified", which is
  inconclusive** — it is *not* a disproof.

In the standard vocabulary this is a **sound but incomplete** verification
procedure (one-sided: no false positives, possible false negatives). We
therefore do **not** speak of a "conditional certificate": a produced
certificate is unconditional; what is conditional is only whether the procedure
*succeeds*. (This differs from a semi-decision procedure in the recursion-theory
sense — our procedures always terminate, returning `CERTIFIED` or `FAIL`.)

This applies equally to R1 (multipliers) and R2 (exact identities): each is a
**certificate-producing algorithm**; a `FAIL` means "no certificate found here",
never "the property is false".

---

## 1. The algebraic class `C` [THEORY, definition]

Fix `θ ∈ (0,π)`, and write `c = cos θ`, `s = sin θ` (so `s > 0` and
`s² = 1 − c²`). Let
```
    K = Frac( Q[c,s] / (s² − 1 + c²) ) = Q(c)[s]/(s² − 1 + c²),
```
a degree-2 field extension of `Q(c)` (since `s = √(1−c²) ∉ Q(c)`). Every element
of `K` has a unique normal form `P(c) + s·Q(c)` with `P,Q ∈ Q(c)`.

A candidate polygon is **in the class `C`** if all its vertex coordinates lie in
`K` for a single such `θ`, and `θ` is pinned by a polynomial `Fc ∈ Q[c]` with
`Fc(c) = 0`. Two sub-cases:

- **root-parametrized** (Audet/A16, Vincze/H8): `θ = z` is the root of the
  family's constructor equation;
- **fixed-angle** (regular, Reinhardt): `θ` is a fixed rational multiple of `π`,
  and `Fc` is the minimal polynomial of `cos θ`.

The frontier of `C` (families *outside* it) is characterized rigorously in §8.

---

## 2. Automatic derivation of the defining polynomial [THEORY]

For root-parametrized families, `Fc` need **not** be supplied from outside: it is
computed from the constructor itself. This is the point that removes any
appearance of circularity (discussed after the proof).

> **Proposition 1 (Automatic derivation of `Fc`).**
> Let a root-parametrized candidate have constructor equation which, reduced in
> `K`, reads `G(c) + s·H(c) = 0` with `G,H ∈ Q[c]` (denominators cleared). Let
> `θ*` be the constructor root, `c* = cos θ*`, `s* = sin θ*`. Define the
> **norm polynomial**
> ```
>     Fc(c) := N_{K/Q(c)}(G + sH) = G(c)² − (1 − c²) H(c)²  ∈ Q[c].
> ```
> Then `Fc(c*) = 0`. Moreover `Fc` is computable from the constructor alone, and
> if `H ≡ 0` (the constructor already reduces to a polynomial in `c`) then `G`
> itself has `c*` as a root and one may take `Fc = G`.

*Proof.* The constructor root satisfies `G(c*) + s* H(c*) = 0`, i.e.
`G(c*) = − s* H(c*)`. Squaring, `G(c*)² = s*² H(c*)² = (1 − c*²) H(c*)²`, since
`s*² = 1 − c*²`. Hence `Fc(c*) = G(c*)² − (1 − c*²) H(c*)² = 0`. The expression
`G² − (1−c²)H²` is exactly the field norm of `G + sH` from `K` to `Q(c)`
(the product of `G + sH` with its conjugate `G − sH`), and is formed by exact
rational operations on the reduced constructor. If `H ≡ 0` then `G(c*) = 0`
directly. ∎

**Why this removes circularity.** The exact-identity engine (§4) needs *some*
polynomial with `c*` as a root. Supplying it from an external characterization of
the *answer* — e.g. the side-length minimal polynomial of the optimal octagon —
would risk using the quantity to be proved in order to prove it. Proposition 1
instead derives `Fc` from the **constructor's own defining equation**, which is
the *definition of the candidate* and is logically prior to, and independent of,
any side/diameter identity we later verify. The parameter `θ*` is thereby pinned
by the constructor; the equalities are then verified as consequences at `θ*`.

**[CERT] Machine check (this project).** For **Vincze/H8**, reducing the OPTIGON
constructor gives `G = 8c³−4c²−4c+1`, `H = 8c²−8c ≠ 0`, and
```
    Fc = G² − (1−c²)H² = 128c⁶ − 192c⁵ − 48c⁴ + 176c³ − 56c² − 8c + 1,
```
which is **identically equal** to the Bingane–Audet §2 sextic in `u = 2−2c`
(`sympy`-verified). So the paper's sextic and the constructor-derived `Fc`
coincide: the sextic is a *cross-check*, not an input. For **A16**, the
constructor reduces to pure `c` (`H ≡ 0`), `Fc = G` of degree 12
(`sympy`-verified; matches `A16Certificate.Fc_poly`).

---

## 3. The conjugate/norm lemma [LIT — standard algebra]

> **Lemma 1 (zero test in a quadratic extension).**
> In the field `K` above, let `w = A + sB` with `A,B ∈ Q(c)`, and let `c*` be a
> value with `s*² = 1 − c*²`, `s* = sin θ*`. If the norm `N(w) = A² − (1−c²)B²`
> vanishes at `c*` and the conjugate `w̄ = A − sB` does **not** vanish at `c*`,
> then `w` vanishes at `c*`.

*Proof.* `N(w)(c*) = (A − s*B)(A + s*B)`; if this is `0` and `A − s*B ≠ 0`, then
`A + s*B = 0` because `ℝ` is an integral domain (no zero divisors). ∎

This is the elementary **norm form of a quadratic field extension** and the
definition of an integral domain; it is textbook (see any algebra reference on
`Q(√d)` and its norm `a² − d b²`). **We claim no originality for Lemma 1.** Its
only novelty here is the *use* to which it is put in §4.

---

## 4. The exact side/diameter reduction [THEORY]

> **Theorem 1 (Exact reduction of side and diameter equalities — sufficient
> conditions).**
> Let `p_i, p_j ∈ K` be candidate vertices in `C`, `τ ∈ Q[c]` a target, and `Fc`
> as in §1–§2 with `Fc(c*) = 0`. Write, in lowest terms,
> ```
>     |p_i − p_j|² − τ = (A(c) + s·B(c)) / D(c),   A,B,D ∈ Q[c],  gcd(D,Fc)=1.
> ```
> Then the equality `|p_i − p_j|² = τ` holds at `θ*` **if** any one of:
> (a) `A ≡ 0` and `B ≡ 0`  (an *unconditional* identity, true for every `θ`);
> (b) `Fc | A` and `Fc | B`;
> (c) `Fc | (A² − (1−c²)B²)` **and** `A − sB ≠ 0` at `θ*`.

*Proof.* `gcd(D,Fc)=1` ⇒ `D(c*) ≠ 0`, so the equality at `θ*` is equivalent to
`A(c*) + s* B(c*) = 0`. Case (a) is immediate. Case (b): `Fc | A` and `Fc(c*)=0`
give `A(c*)=0`; likewise `B(c*)=0`; the sum is `0`. Case (c): `Fc | (A²−(1−c²)B²)`
gives `A(c*)² − (1−c*²)B(c*)² = 0`, which by Lemma 1 with `A − sB ≠ 0` yields
`A(c*)+s*B(c*)=0`. ∎

**Remark (only sufficiency is claimed, and only sufficiency is used).** The
three cases are *sufficient* conditions, checkable by exact `Q[c]` arithmetic
(with the `A−sB ≠ 0` test of case (c) done by a certified interval
non-vanishing check, §4 machine note). They are **not** claimed necessary: the
equality at `θ*` is equivalent to the norm `A²−(1−c²)B²` *vanishing at `c*`*,
whereas (b)/(c) require `Fc` to *divide* that norm — strictly stronger unless
`Fc` is the minimal polynomial of `c*`, which the norm-derived `Fc` of
Proposition 1 need not be. This matches the sound-but-incomplete nature of the
method (§0): a `PROVED` verdict is an unconditional proof; a `FAIL` is
inconclusive. The certification uses only this sufficiency; **no result depends
on a converse.**

**Recognition of the A16 special case.** A16's coordinates have the form
`x = s·X(c)`, `y = Y(c)`, so every squared distance is `s²X'²+Y'² =
(1−c²)X'² + Y'² ∈ Q[c]`, i.e. `B ≡ 0` — Theorem 1 collapses to case (a)/(b),
which is exactly the earlier A16-only method. Vincze/H8's "seam" vertices
(`x = ±½`, `y` with a `c+s` denominator) produce genuine `B ≢ 0` distances that
require case (c). Thus A16 is a **special case** of Theorem 1, not a separate
technique.

**[CERT] Machine check (`src/ExactIdentity.jl`).** All side and active-diameter
equalities are `:PROVEN`/`:UNCONDITIONAL` for the four families:

| family | sides | active diameters | cases used |
|---|---|---|---|
| square (regular) | 6 unconditional (rational) | — | (a) |
| `R_{3,6}` (Reinhardt) | 6 via `Fc` | 2 uncond. + 4 via `Fc` | (a),(b),(c) |
| H8 (Vincze) | 4 uncond. + 4 seam via (c) | 6 unconditional | (a),(c) |
| A16 (Audet) | 14 uncond. + 2 via `Fc` | 15 unconditional | (a),(b) |

R2 is the certificate-producing procedure that applies Theorem 1. Case (c)'s
`A − sB ≠ 0 at θ*` is discharged by a certified interval non-vanishing check
performed over a box that is **certified to contain `θ*`**: for
root-parametrized families the box is the one for which the `existence` block
proves `θ* ∈ box` by the interval IVT (so `A − sB ≠ 0` over the box ⇒ at `θ*`);
for fixed-angle families the box is an interval-π enclosure of the known angle.
It is sound; on these four families it succeeds.

---

## 5. Positive KKT multipliers [THEORY of the procedure; CERT of the results]

R1 is a **sound, incomplete, certificate-producing procedure** for the
statement *"there exist KKT multipliers `y` with `D(e,d)^T y = DL` and all
active-diameter multipliers `λ_ij > 0`."* It is **not** a decision procedure:
existence of a positive representative is a property of the candidate (a genuine
first-order-strict KKT point has one; a non-optimum does not), and even when one
exists the procedure may fail to find it. When it **succeeds it emits an
unconditional certificate**.

**Procedure (`SmallPolygons.general_multipliers`).** Let `d = (n+|E_D|)−(2n−2)`
be the LICQ defect.
1. **Gauge.** Omit the three stationarity equations of coordinates
   `{x_0, y_0, x_j}` for a vertex `j` with `y_j ≠ 0`. **[hypothesis, now
   explicit] the constructors place `p_0 = (0,0)`**; then the rigid-motion
   `3×3` matrix on these coordinates is `[[1,0,1],[0,1,0],[0,0,−y_j]]` with
   determinant `−y_j ≠ 0`, so it is regular and (by the rigid-invariance
   argument) recovers the three omitted equations exactly.
2. **Normalization.** For `d>0`, fix the `d` multipliers of largest nominal
   magnitude to their nominal values. **This is a heuristic**: it is not
   guaranteed to yield a regular square system; the next step checks regularity
   and, if it fails, the procedure returns `FAIL` (soundness is never at risk).
3. Certify the square system regular; Krawczyk-enclose its unique solution;
   certify `min_ij inf(λ_ij) > 0`; certify the gauge matrix regular.

**[CERT] Results.** Certified `λ_min > 0` for all four families, across LICQ
defects `d`: square `d=0` (`λ_min=1.414`), `R_{3,6}` `d=2` (`0.5176`), H8 `d=0`
(`0.3380`), A16 `d=1` (`0.1019`). When `d>0` the multipliers are a `d`-parameter
family and positivity is a property of the certified representative; exhibiting
one positive representative is exactly what the corollary of §7 requires.

---

## 6. What is inherited vs. proved — the strict separation

**[LIT] Inherited from the literature (used, never re-proved).**
- The **first-order-strict corollary** of the source paper (Bingane–Audet; the
  stability paper, §4–§5): *if* a strictly convex equilateral small `n`-gon with
  a declared active graph satisfies (1) strict convexity + labelled cyclic
  order, (2) the exact side and active-diameter equalities, (3) a strict inactive
  margin, (4) `rank D(e,d) = 2n−2` hence `I_eq = R_eq`, and (5) a KKT multiplier
  vector with all active-diameter multipliers positive, *then* every non-rigid
  one-sided feasible first-order direction strictly decreases the perimeter. This
  is the **only essential mathematical dependency**.
- The **constructors** (definitions of the candidates), from OPTIGON / the paper.
- **Classical tools**: Chebyshev reduction; the quadratic-extension norm
  (Lemma 1); interval Newton/Krawczyk and preconditioned regularity (Rump;
  Rohn/Shary); KKT first-order theory.

**[THEORY] Developed here.** Proposition 1 (automatic `Fc`); Theorem 1 (uniform
exact reduction, with A16 as the `B ≡ 0` special case); the two
certificate-producing procedures R1, R2 as sound/incomplete verification
methods; and the recognition, made precise in §8, of the exact class `C` to
which all of this applies.

**[CERT] Certified by machine, per candidate.** Hypotheses (1)–(5) above, each by
a result-verification method (existence by interval IVT; convexity, margin, rank
by interval bounds; multipliers by R1; equalities by R2). Reproduced by
`pipeline/certify_literature.jl` and `test/runtests.jl`.

**[CONCL] Conclusion.** For each of the four families, (1)–(5) are `CERTIFIED`/
`PROVEN`; applying the inherited corollary [LIT] to these certified hypotheses
[CERT] yields [CONCL] that the family's configuration is a **strict first-order
KKT point** — no non-rigid feasible first-order ascent. We do **not** re-prove
the corollary, and we claim **no** global-optimality or second-order result.

---

## 7. Standing scope limits (unchanged; see `docs/guide/scope-and-limitations.md`)

- Global optimality is never claimed. For `n = 4, 6, 8` it is a **literature
  theorem** (Vincze / Reinhardt / AHMP), which the framework does **not**
  re-prove; for A16 (`n = 2^s, s ≥ 4`) it is **open**.
- For root-parametrized families the framework certifies **existence** of the
  constructor root (interval IVT); **uniqueness** in the search interval is
  certified only by the dedicated A16 certificate, not by the general path.
- The rank block certifies `rank = 2n−2` at the certified point (over a box in
  `z` for root-parametrized families; at the exact point for fixed-angle ones);
  "constant rank in an `ℝ^{2n+1}` neighbourhood", the form the corollary's
  hypothesis literally uses, follows by **openness** of the non-vanishing minor —
  an argument external to the computation (`docs/guide/scope-and-limitations.md §3`).

---

## 8. Frontier of the theory (rigorous)

Theorem 1 and Proposition 1 apply to a candidate **iff** its vertex coordinates
lie in `Q(cos θ, sin θ)` for a single real `θ` pinned by a polynomial `Fc ∈ Q[c]`
with `cos θ` a root — equivalently, the coordinate field has transcendence
degree ≤ 1 over `Q` and is generated by one circular pair `(cos θ, sin θ)`.
Families **outside** the theory:

1. **Two `Q`-independent angles**: coordinates in `Q(cos α, sin α, cos β, sin β)`
   with `α, β` independent mod `π` (transcendence degree 2). No single `c`
   reduces both. *We have not verified that Mossinghoff `M_n` or `A_32` are
   single-angle; the theory therefore does not (yet) claim them.*
2. **Higher algebraic dependence on `θ`** (nested radicals `√(g(cos θ))`, `g`
   non-square): a degree `> 2` extension of `Q(c)`, which the quadratic normal
   form `A + sB` does not capture.
3. **Non-algebraic / transcendental parametrizations** (e.g. a purely numerical
   optimum with no closed form): no `Fc` exists.

Every unqualified "general / every family" in earlier drafts must be read as
"every family in `C`", and is so read throughout this revision.

---

## 9. Honest novelty accounting

- **(A) Known / classical.** Chebyshev multiple-angle reduction; the
  quadratic-extension norm and integral-domain factorization (Lemma 1); interval
  Newton/Krawczyk, self-validating regularity tests; KKT first-order theory.
- **(B) Inherited from the source paper.** The constructors; the first-order
  strict corollary; the solved-`n` classification. Certified as hypotheses,
  never re-proved.
- **(C) Earlier rounds of this project.** The A16-specific exact-identity and
  interval-multiplier certificates; the general interval blocks of
  `SmallPolygons`.
- **(D) New in this theory.** (i) Theorem 1 — a *uniform* exact reduction over
  the class `C` that subsumes the A16 (`B ≡ 0`) case and handles `B ≢ 0`
  (Vincze) with the same criterion; (ii) Proposition 1 — the norm-derivation of
  `Fc` from the constructor, which makes the certificate self-contained and
  removes the apparent constructor↔polynomial circularity; (iii) the uniform R1
  multiplier procedure across variable LICQ defect.

**Assessment (no inflation).** (D) is a **systematization and a rigorous,
machine-checked certification method**, not new pure mathematics: the underlying
tools are standard. The contribution is a reusable, honestly-scoped,
self-contained certificate for the class `C`, together with Proposition 1 and
Theorem 1 that organize it. The mathematical depth is modest by design; the value
is verifiability and honest scope.
