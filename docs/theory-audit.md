# Adversarial audit of docs/general-framework.md

Maximum-severity review, in the voice of a hostile *Discrete & Computational
Geometry* referee and a senior geometric-optimization coauthor, whose goal is to
**break** the theory. Nothing is accepted because it "looks right". Findings are
backed by proof or machine check; several were verified in `sympy`/Julia
specifically for this audit. **No code was changed.**

> **STATUS: HISTORICAL SNAPSHOT.** This audit records findings at one point in
> the project's development; it states plainly that no code was changed when it
> was written. Several findings have since been acted on — M1 and M2 were
> addressed in `docs/general-framework.md` (see its scope note and its
> "Honest novelty accounting"), and M5 is moot under the paper's current
> Theorem 3.5. Read individual items with that in mind rather than as live
> statements about the present artifact.

Bottom line up front: **no FATAL defect.** The core reduction is sound and, in
fact, more self-contained than the document claims. But the document commits
**real over-generalization and novelty-inflation** that a referee would reject
on, and it leaves several hypotheses implicit. Classification in Phase 7.

---

## Phase 1 — Theorem-level dependency map

Load-bearing statements in the document, with their true logical status.

| # | Statement | Hypotheses actually used | Status |
|---|---|---|---|
| T1 | coords ∈ `Q(c,s)`, `s²=1−c²`, `c=cosθ`, `θ` a root of `Fc∈Q[c]` | (i) coords are trig-univariate algebraic in one angle θ; (ii) an `Fc` with `cosθ` as a root is available | **Asserted for "every family"; PROVED only for the 4 treated families.** Necessary for everything downstream. |
| T2 | `|p_i−p_j|²−τ = (A+sB)/D`, `D(cosθ)≠0` | T1 + denominators non-vanishing at the root (checked as `gcd(D,Fc)=1`) | Sound. The `gcd` test is *sufficient* for `D(cosθ)≠0` only if every root of `Fc` shared with `D` is excluded — correct, since `gcd=1` ⇒ no common root. |
| T3 | conjugate criterion (cases a–c) ⇒ equality at θ | T2 + `cosθ` a root of `Fc` + integral-domain factorization | Sound (proof in Phase 3). Uses the **hidden identity** `1−cos²θ = sin²θ` with the geometric sign of `sinθ` — see M2. |
| T4 | "R2 is general" (all families PROVEN) | T3 applied per family; `Fc` supplied per family | **Per-family computation, not a theorem.** The engine is general; the *success* is verified on 4 families. |
| T5 | R1: gauge `{x_0,y_0,x_j}` gives regular `Q` | `p_0=(0,0)`; `∃ j: y_j≠0`; convexity ⇒ distinct vertices | Sound but **`p_0=(0,0)` is an implicit hypothesis** (M3). |
| T6 | R1: normalization fixes `d` largest-|nominal| multipliers ⇒ regular square system | none guaranteed | **Heuristic, not a theorem** (M4): may fail to produce a regular system; soundness is preserved (a spurious FAIL, never a false CERTIFY). |
| T7 | R1 certifies `∃` positive KKT multipliers | T5, T6, Krawczyk contraction, `Q` regular | Sound *conditional on the candidate actually having a positive representative that the heuristic finds*. Existence of a positive representative is a property of the candidate, not established in general. |
| C1 | "the full first-order certificate is now general" | T4 + T7 + rank + convexity + margin + the paper's corollary | Holds **for the four families**, modulo the point-vs-neighbourhood rank caveat (M5). |

Reducible hypotheses: none of the used hypotheses is redundant. Strengthenable:
T1/T4 can be strengthened by *deriving* `Fc` from the constructor rather than
supplying it (see the Vincze finding, Phase 4), which also removes an apparent
paper-dependency.

---

## Phase 2 — Over-generalizations, with corrected scope

The document uses "every family / general / all families / generic / reusable"
in places where only four families are demonstrated. Mathematically correct
rewrites:

- ✗ "For every family, the vertex coordinates lie in `Q(c,s)`."
  ✓ "For **each of the four benchmark families treated here**, the coordinates
  lie in `Q(c,s)`; more generally, the method applies to any family whose
  coordinates are algebraic functions of a single angle (Phase 5)."
- ✗ "R2 is now general." ✓ "R2 is proved for the four families; the engine is
  family-agnostic within the class **C** of Phase 5."
- ✗ "R1 … generalized to any candidate and any LICQ defect."
  ✓ "R1 is a **general method** that *certifies* positive multipliers whenever a
  positive representative exists and the normalization heuristic yields a regular
  system; verified for `d∈{0,1,2}` on the four families."
- ✗ "the strict first-order certificate is no longer A16-exclusive."
  ✓ Keep, but scope to "for the benchmark families" and cite the neighbourhood
  caveat.

None of these is a soundness error; all are precision/over-claim errors that a
referee **will** flag.

---

## Phase 3 — The theorem, stated and proved, with clean separation

**Definitions.** Fix `θ∈(0,π)`, `c=cosθ`, `s=sinθ` (so `s>0`, `s²=1−c²`). Let
`𝒞` be the class of polygons whose vertex coordinates lie in `Q(c,s) =
Frac(Q[c,s]/(s²−1+c²))`, i.e. each coordinate is `(P(c)+sQ(c))/R(c)` with
`P,Q,R∈Q[c]`, `R(c)≠0`. Let `Fc∈Q[c]` satisfy `Fc(c)=0`.

> **Theorem (Exact side/diameter reduction — sufficient conditions).**
> Let `p_i, p_j ∈ 𝒞` and `τ∈Q[c]`. Write, in lowest terms,
> `|p_i−p_j|² − τ = (A(c)+sB(c))/D(c)` with `A,B,D∈Q[c]` and `gcd(D,Fc)=1`.
> Then `|p_i−p_j|²=τ` holds at `θ` **if** one of:
> (a) `A≡0` and `B≡0`;
> (b) `Fc∣A` and `Fc∣B`;
> (c) `Fc ∣ (A²−(1−c²)B²)` and `A(c)−sB(c) ≠ 0` (at `θ`).

*Proof.* `gcd(D,Fc)=1` ⇒ `D(c)≠0`, so the equality at `θ` is equivalent to
`A(c)+sB(c)=0`. (a) immediate. (b) `Fc∣A` ⇒ `A(c)=0` (as `Fc(c)=0`), likewise
`B(c)=0`; sum `=0`. (c) `Fc ∣ (A²−(1−c²)B²)` ⇒ `A(c)²−(1−c²)B(c)²=0`; since
`1−c²=s²`, `A(c)²−(sB(c))²=(A(c)−sB(c))(A(c)+sB(c))=0` in the integral domain
`ℝ`; with `A(c)−sB(c)≠0`, conclude `A(c)+sB(c)=0`. ∎

*(Only sufficiency holds in general: the converse needs `Fc` to be the minimal
polynomial of `c*`; the norm-derived `Fc` need not be. The certification uses
only sufficiency — see the revised Theorem 1 in `docs/general-framework.md`.)*

This is **our** contribution at the theorem level, and it is elementary (Phase
4). It says nothing about optimality. The optimality bridge is inherited:

> **Corollary (inherited).** *If*, for a strictly convex equilateral small
> `n`-gon with the declared active graph, the framework certifies
> (1) strict convexity and labelled cyclic order, (2) the `n` side and `|E_D|`
> active-diameter equalities (via the Theorem), (3) strict inactive margin,
> (4) `rank D(e,d)=2n−2` hence `I_eq=R_eq`, and (5) a KKT multiplier vector with
> all active-diameter multipliers positive, *then* — **by the first-order-strict
> corollary of the source paper (Bingane–Audet / the stability paper §4–§5), not
> re-proved here** — every non-rigid one-sided feasible first-order direction
> strictly decreases the perimeter.

**Separation, explicit:** our theory = the reduction Theorem + the certified
computations of (1)–(5); the implication (1)–(5) ⇒ first-order strict is the
paper's, cited, never re-derived.

---

## Phase 4 — The conjugate criterion is elementary and NOT original

The step `(A+sB)(A−sB)=0 ∧ (A−sB)≠0 ⇒ A+sB=0` is exactly the **norm argument of
a quadratic field extension**: in `K=F(√d)` with `F=Q(c)` (localised) and
`√d=s`, `√d∉F`, the field norm is `N(A+sB)=(A+sB)(A−sB)=A²−dB²∈F`, and an element
is zero iff its norm is zero *and* it is not a unit-times-conjugate issue —
concretely, since `ℝ` is an integral domain, a product is zero iff a factor is.
This is textbook (any algebra text on quadratic extensions / the norm map;
e.g. the norm form `a²−d b²` of `Q(√d)`), and "a product of reals is zero iff a
factor is zero" is the definition of an integral domain.

**Verdict:** the criterion is **elementary, known algebra**, presented correctly
but it must **not** be advertised as an original lemma. The document's framing of
it as "one of the central … contributions" is novelty-inflation (MAJOR).

**Byproduct discovered during this audit (and it strengthens the theory).** The
same norm `A²−(1−c²)B²` derives a *self-contained* `Fc`. Reducing the OPTIGON
Vincze constructor `F(t)=0` gives `A₀(c)+sB₀(c)=0` with
`A₀=8c³−4c²−4c+1`, `B₀=8c²−8c≠0`; its norm
`A₀²−(1−c²)B₀² = 128c⁶−192c⁵−48c⁴+176c³−56c²−8c+1` is **identically equal** (verified in `sympy`) to the
Bingane–Audet §2 sextic in `u=2−2c`. Consequences:
- The Vincze `Fc` is **derivable from the constructor itself**; the document's
  claim that it is "obtained from the §2 sextic" mis-attributes provenance and
  understates self-containment. `cosθ` being a root of `Fc` is then a
  *definitional* fact (the constructor root squared), **not** a dependency on
  AHMP. (Fix: derive `Fc` via the norm; note the coincidence with §2.)
- For **A16**, `Fc` is already the constructor equation reduced to `c` (its
  coordinates are `x=sX, y=Y`, so `F` reduces to pure `Q[c]`). For **fixed-angle**
  families, `Fc` is the minimal polynomial of the *known* `cosθ`. So for **all
  four** families "`cosθ` is a root of `Fc`" is definitional, not inherited. This
  removes the one place the theory looked paper-dependent for R2.

---

## Phase 5 — Rigorous frontier (with counterexamples)

The theory applies to a candidate **iff** its vertex coordinates lie in
`Q(cosθ, sinθ)` for a **single** real `θ`, with `θ` pinned by a polynomial
`Fc∈Q[c]` having `cosθ` as a root. Equivalently: the coordinate field has
transcendence degree ≤ 1 over `Q` and is generated by one circular pair
`(cosθ, sinθ)`.

Explicit exclusions (rigorous, not intuitive):
1. **Two independent angles.** A construction with coordinates in
   `Q(cosα, sinα, cosβ, sinβ)` where `α,β` are `Q`-linearly independent mod `π`
   (transcendence degree 2) is **outside**: no single `c` reduces both. (A
   hypothetical multi-parameter equilateral construction, or a product/perturbed
   family, would be of this kind.) **We have not verified that Mossinghoff `M_n`
   or `A_32` are single-angle**; the document must not implicitly include them.
2. **Nested radicals / higher algebraic dependence on θ.** Coordinates involving
   `√(g(cosθ))` for non-square `g` lie in a degree-`>2` extension of `Q(c)`; the
   `(A+sB)` normal form (a **quadratic** extension by `s`) does not capture them.
3. **Transcendental / non-algebraic parametrizations** (e.g. coordinates
   defined by a non-algebraic ODE flow, or by an optimizer with no closed form):
   no `Fc` exists. The regular/Reinhardt/Vincze/Audet constructors are all
   algebraic; a purely numerical optimum with no algebraic model is outside.

So the boundary is **exactly** "single-circular-parameter algebraic families
with a known defining polynomial." This should replace every unqualified
"general/every family" in the document.

---

## Phase 6 — Honest novelty accounting

- **(A) Known / classical.** Chebyshev reduction `cos kθ=T_k(c)`,
  `sin kθ=sU_{k-1}(c)`; the quadratic-extension norm and integral-domain
  factorization (Phase 4); interval arithmetic, interval Newton/Krawczyk,
  preconditioned matrix-regularity (Rump; Rohn/Shary); KKT/first-order theory.
- **(B) Inherited from the source paper (Bingane–Audet / the stability paper).**
  The constructors (`A_n`, and via OPTIGON the Reinhardt/Vincze/regular data);
  the first-order-strict *implication* (the Corollary); the classification of
  which `n` are solved. **We certify hypotheses; we do not re-prove these.**
- **(C) Framework, earlier rounds of this project.** The A16 exact-identity and
  interval-multiplier certificates; the general interval blocks (existence,
  convexity, margin, rank) of `SmallPolygons`.
- **(D) Genuinely new in *this* theory.** (i) The observation that A16's
  `x=sX,y=Y` structure is the `B≡0` special case, and the **systematic reduction
  Theorem** (Phase 3) covering the `B≢0` case uniformly across single-angle
  families; (ii) the **norm-derivation of `Fc` from the constructor** making the
  Vincze certificate self-contained; (iii) the **uniform interval-multiplier
  certificate across variable LICQ defect** `d=#active−(n−2)`.

**Honest assessment:** (D) is a **systematization + rigorous-certification**
contribution, not new pure mathematics. The mathematical depth is modest (the
tools are standard); the value is a reusable, machine-checked, honestly-scoped
certificate. The document should claim exactly this and no more.

---

## Phase 7 — Referee verdict (trying to reject)

**FATAL** — none found. The reduction Theorem is proved; the per-family checks
pass; no circularity (in particular the Vincze `Fc` is now shown self-contained,
so the feared "define the candidate by the answer" circularity does not occur);
no false claim of re-proving the paper.

**MAJOR**
- **[ADDRESSED] M1. Over-generalization of "general/every family."** *(`docs/general-framework.md` now states: "Every unqualified general / every family in earlier drafts must be read as every family in `C`, and is so read throughout this revision." The manuscript `a16.tex` never made the claim at all.)* The theory is
  established for four families and for the class `C` of Phase 5, not "every
  family." Rewrite per Phase 2. *(Impact: central to a "general theory" claim.)*
- **[ADDRESSED] M2. Novelty inflation of the conjugate criterion.** *(That section is now headed "[LIT — standard algebra]" and says "We claim no originality for Lemma 1. Its only novelty here is the use to which it is put." The criterion is moreover never reached for `A16`: all 31 of its identities take the unconditional or divisible branch.)* It is the quadratic-field
  norm argument (Phase 4); must be cited as standard, not sold as a central
  contribution. *(Impact: a referee will penalise an over-claimed contribution.)*
- **[ADDRESSED IN CODE] M4. R1 normalization is a heuristic, not an algorithm with a guarantee.** *(It is a conditional certificate by construction: `general_multipliers` certifies the normalised system regular before solving and returns `pass=false, reason="normalized system not regular"` otherwise, so no positivity is ever asserted on an uncertified system. The heuristic chooses which multipliers to pin; it never decides the verdict.)*
  "Fix the `d` largest-|nominal| multipliers" may not yield a regular system;
  and existence of a positive representative is a candidate property, not proved
  in general. State R1 as a *conditional* certificate. *(Soundness intact;
  completeness/scope overstated.)*
- **M6. `Fc` provenance / self-containment (from Phase 4).** The document mis-
  states where Vincze's `Fc` comes from and misses that it is derivable from the
  constructor. Correcting this both fixes attribution and *removes* an apparent
  paper-dependency — strengthens the paper, but currently reads as an inherited
  input.

**MINOR**
- **M3. Implicit `p_0=(0,0)`** in the R1 gauge determinant `det Q=±(y_0−y_j)`
  (with `y_0=0` it is `∓y_j`). State the spatial-gauge hypothesis.
- **M5. Point vs. neighbourhood rank.** ~~For fixed-angle families the rank is
  certified at the point; "constant rank in a neighbourhood" (what the paper's
  hypothesis literally needs) follows from openness of the non-vanishing minor —
  an argument external to the computation.~~ **[MOOT.** Theorem 3.5 in its
  current form assumes nothing about `D(e,d)` at neighbouring configurations, so
  no neighbourhood rank statement is needed and no external openness argument is
  load-bearing. Pointwise rank is both what is certified and what is consumed.
  See `docs/scope-and-limitations.md` §3.**]**
- **M7. Vincze constructor↔`Fc` consistency** is currently cross-checked
  numerically in the tests (residual ~1e-58); with M6's norm-derivation it can be
  made exact. Until then, state it as a numerically-verified identification.

**WORDING ONLY**
- The `exact_identities` block message and the theory doc both say "conditional-
  on-`Fc`"; clarify this means "holds at the root of `Fc`," not "conditional on
  an unproved hypothesis."
- Consistently distinguish `θ` (angle) from `z` (A16's constructor root) in the
  prose.

**Recommendation:** *accept the mathematics; require revision of scope and
novelty language (M1, M2, M4, M6) before any "general theory" claim stands.* The
surviving core — the reduction Theorem + certified hypotheses + cited corollary —
is correct and, with M6, self-contained.
