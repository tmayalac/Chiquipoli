# Code to Section 6: a referee-grade mapping

Source: the article accompanying this package, *"First Order Geometry of Equilateral
Small Polygons"*, **Section 6 "Certified verification of $A_{16}$"** (Lemma 6.1,
Proposition 6.2 items (1)–(6), Theorem 6.3), which instantiates the abstract
criterion **Theorem 3.5** ("Strict first order criterion"). The article cites
this package as **[AH26]**.

This document checks the code **against the literal text of the article**, makes
every hypothesis it uses explicit, and claims nothing stronger than what is
proved. It is written at referee level: every auxiliary lemma is stated and
either proved or cited, every dimension is declared, and every logical step is
made explicit. Each numeric value quoted below was compared against the output
of `scripts/run_all.jl`, recorded in `logs/final_run.txt`, and agrees with
Proposition 6.2 digit for digit.

Topological maximality does not rest on any second-order remark. It is the
**direct** conclusion of Theorem 3.5, proved via **Lemma 3.4 (Local Euclidean
slice)** together with a normalised-sequence argument.

Every dimensional claim below was verified numerically: $\operatorname{rank} D
= 30$, dependency space of dimension $1$, ambient dimension $33$, $\det Q =
y_1 - y_8 < 0$, and three rigid-motion vectors of rank 3.

---

## 0. Conventions and glossary

To remove every ambiguity between rows, columns, equations and variables, the
following terminology is fixed and used consistently throughout. It matches the
article: ambient space $(\mathbb R^2)^{16}\times\mathbb R$ of dimension 33,
$\operatorname{rank} D(e,d)=30$, $\dim\mathcal I_{\mathrm{eq}}=3$.

- **Ambient space (of variables).** $V = (\mathbb R^2)^{16}\times\mathbb R$, of
  dimension **33**, with coordinates $(x_0,y_0,\dots,x_{15},y_{15},\ell)$. The
  vertex is $p_i=(x_i,y_i)$; the 33rd variable is the common side length
  $\ell$.
- **Active constraints.** 16 side equalities $e_i(p,\ell)=|p_{i+1}-p_i|-\ell$
  for $i=0,\dots,15$, and 15 active-diameter equalities
  $d_{ij}(p)=|p_i-p_j|-1$ for $\{i,j\}\in E_D$. **31 constraints** in total.
  The active graph $E_D(A_{16})$ is the one declared in Section 5 of the
  article.
- **Constraint Jacobian $D=D(e,d)$.** The **31×33** matrix whose **rows** are
  the differentials of the 31 constraints and whose **columns** are the 33
  ambient variables. In the code this is `A = build_jacobian(z)`. It is the
  article's $D(e,d)$, which the article also writes $A=D(e,d)$.
- **Transposed Jacobian $D^{\mathsf T}$.** A **33×31** matrix. Its **columns**
  are the 31 constraint gradients, viewed as vectors of
  $V^\ast\cong\mathbb R^{33}$; its **rows** are indexed by the 33 ambient
  variables.
- **Stationarity system (first-order KKT).** $DL = D^{\mathsf T} y$, written
  $A^{\mathsf T}\mu = g$ with $g = DL$ in the article, where
  $y=\mu=(\alpha,\lambda)\in\mathbb R^{31}$ is the multiplier vector: 16 side
  multipliers $\alpha_i$ and 15 diameter multipliers $\lambda_{ij}$. This is
  the article's *multiplier identity*, hypothesis (i) of Theorem 3.5. It is a
  system of **33 scalar equations**, one per ambient variable, in **31
  unknowns**.
- **Multipliers.** The vector $y\in\mathbb R^{31}$. Do not confuse its length
  (31) with the number of stationarity equations (33) or with the ambient
  dimension (33).
- **$R_{\mathrm{eq}}$.** The subspace of $V$ spanned by the three infinitesimal
  Euclidean motions: two translations and one rotation. By Lemma L1 below,
  $\dim R_{\mathrm{eq}}=3$. It is the article's $R_{\mathrm{eq}}(p)$
  (Definition 2.7).
- **$\mathcal I_{\mathrm{eq}}$.** The active equality tangent space,
  $=\ker D\subseteq V$. It is the article's
  $\mathcal I_{\mathrm{eq}}(p,\ell)$ (Definition 2.6).

Numeric summary — every entry verified, none assumed:

| Quantity | Value |
|---|---|
| $\dim$ ambient $V$ | 33 |
| number of active constraints | 31 |
| number of multipliers $=\dim y$ | 31 |
| number of stationarity equations | 33 |
| $\operatorname{rank} D$ | 30 |
| $\dim$ of the dependency space among constraint gradients | 1 |
| $\dim\mathcal I_{\mathrm{eq}}=\dim\ker D=33-30$ | 3 |
| $\dim R_{\mathrm{eq}}$ (Lemma L1) | 3 |
| stationarity equations solved directly | 30 |
| stationarity equations omitted, recovered by argument | 3 |

---

## 1. Auxiliary lemmas

These two lemmas are stated and proved here because they are load-bearing
below. In the article they play the role of the structural hypotheses of
Theorem 3.5: independence of $R_{\mathrm{eq}}$, and the strict convexity that
pins the labelled cyclic order.

### Lemma L1 — independence of the rigid motions, hence $\dim R_{\mathrm{eq}}=3$

**Statement.** Let $(p,\ell)$ be a configuration with at least two distinct
vertices. The three infinitesimal fields

$$t_x:\ v_i=(1,0),\qquad t_y:\ v_i=(0,1),\qquad r:\ v_i=(-y_i,x_i),$$

for $i=0,\dots,15$, all with $\eta=0$ in the $\ell$ variable, are linearly
independent in $V$. Hence $\dim R_{\mathrm{eq}}=3$.

**Proof.** Suppose $a\,t_x+b\,t_y+c\,r=0$. At vertex $i$ this gives
$(a-c\,y_i,\ b+c\,x_i)=(0,0)$ for every $i$, that is, $y_i=a/c$ and $x_i=-b/c$
constant in $i$ whenever $c\neq0$ — which would force **all** vertices to
coincide. Since at least two vertices are distinct, $c=0$; then $a=b=0$. $\square$

**Use.** The hypothesis "at least two distinct vertices" is amply guaranteed by
the certified strict convexity (Lemma L2 with Proposition 6.2(3)): a strictly
convex polygon with 16 labelled vertices has all 16 distinct. L1 is the reason
$\dim R_{\mathrm{eq}}$ is exactly 3 and not less, and it is indispensable for
the bound $\operatorname{rank}D\le30$ (Proposition 6.2(6)) and for
$\mathcal I_{\mathrm{eq}}=R_{\mathrm{eq}}$ (Theorem 6.3). The article uses the
same independence in the proofs of Lemma 3.4 and Proposition 6.2(6).

### Lemma L2 — convexity by support determinants

**Statement (classical criterion).** Let $p_0,\dots,p_{15}$ be a sequence of
points in the given labelled cyclic order. If for every edge $(i,i+1)$, indices
modulo 16, and every vertex $j\notin\{i,i+1\}$ the support determinant

$$H_{i,j}=\det\big(p_{i+1}-p_i,\ p_j-p_i\big)
=(x_{i+1}-x_i)(y_j-y_i)-(y_{i+1}-y_i)(x_j-x_i)$$

is strictly positive, then the sequence is a simple, strictly convex polygon,
traversed counterclockwise, with exactly that cyclic order.

**Justification.** This is the standard "every other vertex strictly to the left
of each directed edge" criterion. $H_{i,j}>0$ for every $j$ says that all
vertices lie strictly in the left half-plane of the oriented line
$p_i\to p_{i+1}$; that this holds for all 16 edges implies the boundary is that
of a convex body and that no triple of consecutive vertices is collinear, which
is *strict* convexity. The article calls these the "support determinants" in
Proposition 6.2(3). This document uses the criterion as a cited lemma, not as an
informal claim.

**Use.** Proposition 6.2(3) certifies $H_{i,j}>0$ over the whole interval box
$Z_{\mathrm{cert}}$; by L2 this certifies strict convexity and cyclic order
simultaneously, and it feeds the "at least two distinct vertices" hypothesis of
L1.

---

## The abstract framework: what Theorem 3.5 consumes

The result finally invoked is **Theorem 3.5 (Strict first order criterion)**.
It has exactly two hypotheses:

- **(i)** there exist side multipliers and **strictly positive**
  active-diameter multipliers satisfying the multiplier identity
  $DL=D^{\mathsf T}y$;
- **(ii)** $\mathcal I_{\mathrm{eq}}(p,\ell)=R_{\mathrm{eq}}(p)$.

Its conclusion: $(p,\ell)$ is a **strict local maximiser** of perimeter modulo
orientation-preserving Euclidean motions — there is a neighbourhood $W$ of
$(p,\ell)$ such that every feasible $(q,m)\in W$ satisfies $m\le\ell$, with
equality only when $q$ is congruent to $p$. This conclusion is **topological**
and is proved in the article via **Lemma 3.4 (Local Euclidean slice)** together
with a normalised-sequence argument. No second-order theory intervenes.

**The central point of rigour (Remark 3.6).** Theorem 3.5 **does not require
constant rank** on a neighbourhood. It uses only the one-sided linearised cone,
the multiplier identity, and the **linear** identity
$\mathcal I_{\mathrm{eq}}=R_{\mathrm{eq}}$ *at the point*. This settles the old
"box in $z$ versus neighbourhood in $\mathbb R^{33}$" concern cleanly: the
certificate needs $\operatorname{rank}D=30$ at the certified point, from which
$\dim\mathcal I_{\mathrm{eq}}=3=\dim R_{\mathrm{eq}}$ and therefore
$\mathcal I_{\mathrm{eq}}=R_{\mathrm{eq}}$. No sweep of a full neighbourhood of
$\mathbb R^{33}$ is needed.

The code establishes hypotheses (i) and (ii) for $A_{16}$. The implication
— hypotheses $\Rightarrow$ maximality — is Theorem 3.5, and its correctness is
a mathematical result to be reviewed separately. It is outside the scope of
this mapping.

---

## Lemma 6.1 — exact side and active-diameter equalities

> **Lemma 6.1.** "Let $z$ be a root of $F$ … Then all sixteen side equalities
> and all fifteen declared active diameter equalities hold exactly. More
> precisely, twenty nine corresponding squared distance differences vanish
> identically as polynomials in $c$. The remaining two, associated with the
> sides $\{3,4\}$ and $\{12,13\}$, are nonzero constant multiples of $F_c(c)$."

- **Files:** `src/A16Certificate.jl` (`sqdist_poly`, `Fc_poly`,
  `exact_identity_certificate`) and `scripts/06_exact_identities.jl`.
- **Method — not interval arithmetic.** Via the Chebyshev identities
  $\sin(kz)=\sin(z)\,U_{k-1}(\cos z)$ and $\cos(kz)=T_k(\cos z)$, every
  coordinate of `coordinates(z)` has the form $(\sin z\cdot X(c),\ Y(c))$ with
  $c=\cos z$ and $X,Y\in\mathbb Q[c]$. Every squared distance, and $F$ itself,
  reduces to a polynomial in $\mathbb Q[c]$; $F_c(c)$ has degree 12. An
  equality $\mathrm{sqdist}(i,j)=\mathrm{target}$ is PROVED when the difference
  polynomial is **exactly divisible** by $F_c(c)$: zero remainder under
  rational long division in `Rational{BigInt}`, with no floating point.
- **Exact classification**, verified by computation and independently under
  `tools/`. Of the 31 equalities:
  - **29 are unconditional:** the difference polynomial is *identically* zero in
    $\mathbb Q[c]$. These are trigonometric identities true for **every** $z$,
    without using $F$ at all.
  - **2 are conditional on $F(z)=0$:** the sides $\{3,4\}$ and $\{12,13\}$, the
    same pair the article names. For $\{3,4\}$, with $p_3=(-x,y)$ and
    $p_4=(x+\sin 7z,\ y+\cos 7z)$, we have $p_4-p_3=(2x+\sin 7z,\ \cos 7z)$ and
    therefore
    $$|p_4-p_3|^2-\ell^2=(2x+\sin 7z)^2+\cos^2(7z)-4\sin^2(z/2)=F(z)$$
    **literally**, by the article's definition of $F$. The difference
    polynomial is exactly a constant multiple of $F_c(c)$, quotient verified.
    The case $\{12,13\}$ is its mirror image under $i\mapsto 16-i$.
- **"No interval containing zero."** For $A_{16}$ the proof of the 31 equalities
  is **pure exact rational algebra**; no interval sign check intervenes. This
  satisfies the article's claim literally.
- **Exact strength, stated precisely and without exaggeration.** For the **29
  unconditional** ones, the algebraic proof is *strictly stronger* than an
  interval enclosure: the identity holds for every $z$. For the **2
  conditional** ones, the proof is **logically equivalent** to
  $F(z^\ast)=0$ — neither stronger nor weaker than the root certificate of
  Proposition 6.2(1). It *is* that certificate, re-expressed.
- **Independent verification.** `tools/` reproduces this 29-versus-2
  classification in Python with SymPy, written from scratch without reading
  `src/`. It agrees on all 31 cases, including the degree-12 polynomial of the
  2 conditional ones.

---

## Proposition 6.2 — certified geometric and first-order data

The article states Proposition 6.2 over the box nesting

$$Z_{\mathrm{root}}\subset\operatorname{int}Z_{\mathrm{cert}},$$

with $Z_{\mathrm{root}}$ of radius $10^{-30}$ for existence and uniqueness, and
$Z_{\mathrm{cert}}$ of radius $10^{-28}$ for geometry, rank and multipliers. In
the code, `box_root` (radius `1e-30`) $\subset$ `box_geom` (radius `1e-28`),
checked in `run_all.jl` by comparing endpoints: `Z_root` must lie in the
interior of the box that each of stages 03, 04 and 05 actually evaluated (not,
as before the 2026-09 external audit, by comparing the two radii, D04). The
check is a gate of the verdict; a failure yields `NOT CERTIFIED` and a
certificate file with a `FAIL` entry rather than an aborted run (D02).

### Proposition 6.2(1) — existence and uniqueness

- **File:** `scripts/02_root_interval.jl`, `run_root_interval()`.
- **Theorem used:** one-dimensional interval Newton. There is an exact real root
  in $Z_{\mathrm{root}}$, and it is unique there, provided
  $0\notin F'(Z_{\mathrm{root}})$ and
  $N(Z_{\mathrm{root}})\subset\operatorname{int}Z_{\mathrm{root}}$.
- **Rigour of the point value $F(m)$.** $N=m-F(m)/F'(Z)$ requires $F(m)$ to be
  a rigorous enclosure. $F$ is evaluated over the thin interval
  `interval(m)`, of width about $10^{-77}$ at 256 bits. The domain check
  $Z\subset(\mathrm{lo},\mathrm{hi})$ is also rigorous, with $\pi$ enclosed.
- **What is proved exactly.** Existence of an **exact real root**
  $z^\ast\in Z_{\mathrm{root}}$ with $F(z^\ast)=0$ *exactly*, and its
  uniqueness. This is what legitimises the two conditional identities of
  Lemma 6.1 holding *exactly* at $z^\ast$.
- **Uniqueness — scope.** Newton gives uniqueness inside $Z_{\mathrm{root}}$.
  The code additionally certifies $0\notin F'(I_{\mathrm{search}})$ over the
  **whole** search interval
  $I_{\mathrm{search}}=\big(2\arcsin(\sin(\pi/16)/2),\ \pi/16\big)$, proving
  strict monotonicity; with existence, the root is unique in the entire search
  interval. Proposition 6.2(1) states exactly this.
- **Methodological note.** The code solves only the **scalar equation**
  $F(z)=0$; the 33 ambient variables are explicit trigonometric functions of
  $z$, so fixing $z^\ast$ fixes all 33 coordinates. This exploits the
  one-parameter structure of the constructor; it is not a shortcut.
  **Explicit hypothesis:** `coordinates(z)` reproduces the Bingane–Audet OPTIGON
  constructor `cstrt_audet_ngon` for $n=16$. This is checked directly by running
  the original constructor unmodified and comparing all 30 coordinates; see
  "Constructor fidelity" below.

### Proposition 6.2(2) — side length

- **File:** `scripts/run_all.jl`, `emit_a16_certificate`.
- $\ell=2\sin(z/2)$ is enclosed over the certified root box
  $Z_{\mathrm{root}}$ with outward rounding, so the reported interval is a
  rigorous enclosure of the value at the exact root, not a point evaluation.
  The certified enclosure has width below $10^{-29}$ for $\ell$ and below
  $10^{-28}$ for $16\ell$, and lies inside the interval the article states.

### Proposition 6.2(3) — strict convexity and cyclic order

- **File:** `scripts/03_geometry_interval.jl`, `support_determinants`.
- **Method:** $H_{i,j}>0$ is certified — positive interval infimum — for every
  edge $(i,i+1)$ and every $j\notin\{i,i+1\}$, over **all** of
  $Z_{\mathrm{cert}}$. That is $16\times14=224$ determinants. By **Lemma L2**
  this certifies strict convexity together with the cyclic order.
- **Agreement with the article.** The smallest certified support determinant is
  $$\min H_{i,j}=0.00748820493069892443\ldots$$
  matching the article's bound of $0.0074882049306989244$.
- **Consequence:** all 16 vertices are distinct, so the hypothesis of L1 holds.

### Proposition 6.2(4) — exact active graph and strict inactive margin

- **The 15 active diameter equalities** are covered by Lemma 6.1, exactly and
  unconditionally.
- **Strict inactive margin:** `scripts/03_geometry_interval.jl`. The interval
  **supremum** of $|p_i-p_j|^2$ is taken over every undeclared pair and all of
  $Z_{\mathrm{cert}}$, and required to be $<1$. Of the $\binom{16}{2}=120$
  vertex pairs, 15 are the declared ones and the remaining 105 are checked. The
  reported margin is a **directed lower bound**,
  $$\delta_{\mathrm{inact}}\ge0.008099710658135729579\ldots$$
  matching the article's $0.0080997106581357295$. The critical pair is
  $\{4,12\}$.

### Proposition 6.2(5) — multiplier identity and positivity

> "A validated solve of the normalized square stationarity system gives a unique
> enclosed multiplier vector and certifies $\lambda_{ij}>0$ for every active
> diameter edge … $\min\lambda_{ij}\ge0.0918667776833353997$ …
> $\sum_i\alpha_i=-16$."

#### C.0 Structure of the problem: LICQ fails, multipliers are not unique

This must be stated explicitly, and the article accommodates it: Definition 2.8
allows dependent rows, and Theorem 3.5 does not require LICQ.

- There are **31 active constraints** but $\operatorname{rank}D=30$. The 31
  constraint gradients are linearly **dependent**: the dependency space
  $\ker D^{\mathsf T}$ has **dimension $31-30=1$**.
- Consequently **LICQ fails** at $A_{16}$.
- The system $D^{\mathsf T}y=DL$ — 33 equations, 31 unknowns — has, when
  consistent, a solution set that is an **affine line** $y^\ast+\mathbb R\,w$ of
  dimension 1: **the KKT multipliers are not unique.** The article says so
  explicitly.
- **What Theorem 3.5 requires.** Only the **existence of one** representative
  $y$ with $\lambda_{ij}>0$ for every active diameter (hypothesis (i)). Neither
  uniqueness nor positivity of every representative is needed. Exhibiting
  **one** positive representative suffices.

#### C.1 How the identity and the positivity of a representative are certified

- **File:** `scripts/05_multipliers_interval.jl`, with `normalized_matrix`,
  `krawczyk_linear` and `omitted_residual_matrix`.
- **Choice of representative.** To make the representative unique, a
  normalisation equation fixing $\lambda_{(0,9)}=1/5$ is added — **the same one
  the article imposes**. This is **not** a spatial gauge; the spatial gauge
  $p_0=(0,0)$ is already built into `coordinates(z)`. It is a normalisation of
  the affine family of multipliers induced by the failure of LICQ.
- **Agreement with the article.** The certified representative satisfies
  $$\min_{\{i,j\}}\lambda_{ij}=0.09186677768333539974\ldots>0,$$
  agreeing **digit for digit** with the article's positivity bound, attributed
  there to the edge $\{6,13\}$. The 15 values of `Y[17:31]`, the Krawczyk
  enclosure produced by this code at radius $10^{-28}$, agree digit for digit
  with the 15 values printed in the article's Table 2, including that minimum.
- **System solved.** $M(z)\,y=b(z)$ is **31×31**: 30 of the 33 stationarity
  equations — the variables in `COLS_MINOR`, which omits $x_1,y_1,x_8$,
  **exactly the three the article omits** — plus the normalisation row. $M$ is
  certified **regular** over the whole box by the preconditioned criterion
  described under Proposition 6.2(6), and the linear Krawczyk step rigorously
  encloses that $y$.
- **Recovery of the three omitted equations.** The residual
  $\rho=D^{\mathsf T}y-DL$ vanishes on the 30 solved variables, so it can be
  supported only on $\{x_1,y_1,x_8\}$. Since $D^{\mathsf T}y$ annihilates
  $\ker D\supseteq R_{\mathrm{eq}}$, and $DL$ also annihilates
  $R_{\mathrm{eq}}$ — because $DL[v,\eta]=16\eta$ and a rigid motion does not
  change $\ell$ — the residual annihilates the three rigid motions. Restricted
  to its three support coordinates this is the homogeneous system
  $Q\,\rho_{\mathrm{sup}}=0$ with
  $$Q=\begin{pmatrix}1&0&1\\0&1&0\\-y_1&x_1&-y_8\end{pmatrix},
  \qquad \det Q=y_1-y_8.$$
  For $A_{16}$ the article proves $\det Q<0$ **exactly** (Subsection 6.4, since
  the supervisor's 2026-09-16 corrections): $p_0=(0,0)$ and $p_8=(0,1)$ by the
  constructor, so $\det Q=y_1-1\leq|p_1-p_0|-1=\ell-1<0$. Hence $Q$ is regular,
  $\rho=0$, and $D^{\mathsf T}y=DL$ holds on all 33 variables. The code reaches
  the same conclusion by a different route: `05_multipliers_interval.jl`
  certifies $Q$ regular over the box by the preconditioned test,
  $\|\mathrm{Id}-C_QQ\|_\infty\leq4.017187643256795\times10^{-28}<1$, and
  that test **is** a gate (`omitted_pass` enters `final_pass`). The two routes
  are independent proofs of the same statement. Earlier versions of this file
  cited the interval sign $y_8-y_1>0$ instead; that sign is still checked, by
  `scripts/check_paper.jl`, but it is no longer the argument the article uses.
- **Positivity $\lambda_{ij}>0$:** a strict interval lower bound. This is a
  valid proof of a strict inequality; the "zero trap" concerns *equalities*, and
  does not apply.

#### C.2 The balance $\sum\alpha_i=-16$ is a consequence, not a pillar

Column 33 of $D$, the $\ell$ variable, is $-1$ in the 16 side rows and $0$ in
the 15 diameter rows. The stationarity equation for $\ell$ is therefore
$-\sum_i\alpha_i=(DL)_\ell=16$, that is, $\sum_i\alpha_i=-16$. Since column 33
**is in `COLS_MINOR`**, this equation is **one of the 30 solved exactly** by the
linear Krawczyk step. The article agrees: the identity "follows algebraically
from its $\ell$ component; the direct interval sum is only a diagnostic." The
code reports it as `alpha_balance_diagnostic`, not as part of `final_pass`. It
is the analogue of the article's Remark 3.2, $\sum\alpha_i=-n$.

### Proposition 6.2(6) — rank 30

> "A thirty by thirty minor $M$ of the active equality Jacobian admits a
> preconditioner $C$ satisfying
> $\|\mathrm{Id}-CM\|_\infty\le1.419383643581978\times10^{-25}<1$ on
> $Z_{\mathrm{cert}}$."

- **File:** `scripts/04_rank_interval.jl`, with `regularity_test`.
- **Lower bound $\operatorname{rank}D\ge30$.** A **30×30** minor $M$ is
  extracted — rows `ROWS_MINOR`, 30 of the 31 constraints, omitting
  $d_{(0,9)}$; columns `COLS_MINOR`, omitting $x_1,y_1,x_8$ — and certified
  regular over the whole box by the sufficient preconditioned criterion: with
  $R\approx\operatorname{inv}(\operatorname{mid}M)$ and $E=\mathrm{Id}-R\,M$,
  $\|E\|_\infty<1$ implies $M$ nonsingular, since
  $\rho(E)\le\|E\|_\infty<1$. The certified value
  $\|\mathrm{Id}-CM\|_\infty\le1.419383643581977854\ldots\times10^{-25}$ matches
  the article's bound.
- **Upper bound $\operatorname{rank}D\le30$.** By **L1** the three rigid motions
  are independent and annihilate every constraint, so
  $R_{\mathrm{eq}}\subseteq\ker D$ with $\dim R_{\mathrm{eq}}=3$; by
  rank–nullity, $\operatorname{rank}D\le33-3=30$. This **depends essentially on
  L1**: without the independence one would obtain only $\le31$.
- **Conclusion:** $\operatorname{rank}D=30$, hence
  $\dim\ker D=\dim\mathcal I_{\mathrm{eq}}=3$.
- **"Box in $z$" versus "neighbourhood in $\mathbb R^{33}$".** The code
  certifies regularity **at the enclosed exact point** on the one-parameter
  curve $\{p(z)\}$. Proposition 6.2(6) concludes $\operatorname{rank}D(e,d)=30$
  **at the exact configuration**, and by **Remark 3.6** Theorem 3.5 needs
  nothing more: the pointwise identity already gives
  $\mathcal I_{\mathrm{eq}}=R_{\mathrm{eq}}$. No computational sweep of a
  neighbourhood of $\mathbb R^{33}$ is claimed.
- **Choice of minor:** the article only requires that **some** regular 30×30
  minor exist, so the concrete selection is a valid implementation decision.

---

## Theorem 6.3 — certified strict local maximality of $A_{16}$

> **Theorem 6.3.** "The Bingane–Audet hexadecagon $A_{16}$ is a strict local
> maximiser of perimeter modulo orientation preserving Euclidean motions among
> convex equilateral small hexadecagons."

The article's logical chain, reproduced by the code:

1. Proposition 6.2(6) gives $\operatorname{rank}D(e,d)=30$.
2. The ambient space $(\mathbb R^2)^{16}\times\mathbb R$ has dimension 33, so
   $\dim\mathcal I_{\mathrm{eq}}(A_{16})=33-30=3$.
3. $A_{16}$ is strictly convex (Proposition 6.2(3) with Lemma L2), so
   $\dim R_{\mathrm{eq}}(A_{16})=3$ by Lemma L1; and always
   $R_{\mathrm{eq}}\subseteq\mathcal I_{\mathrm{eq}}$. Therefore
   $\mathcal I_{\mathrm{eq}}(A_{16})=R_{\mathrm{eq}}(A_{16})$, which is
   hypothesis (ii).
4. Proposition 6.2(5) gives the multiplier identity with every
   $\lambda_{ij}>0$, which is hypothesis (i).
5. Theorem 3.5 gives strict, topological local maximality modulo Euclidean
   motions.

**No constrained Hessian is required.** Since
$\mathcal I_{\mathrm{eq}}=R_{\mathrm{eq}}$ — the active equality space has
dimension 3 and consists exactly of the infinitesimal Euclidean motions — the
strict first-order criterion applies directly. The code is consistent with
this: it computes no second-order data, because none is needed.

**This document verifies that the code establishes hypotheses (i) and (ii) of
Theorem 3.5, via Lemma 6.1 and Proposition 6.2. The implication — hypotheses
$\Rightarrow$ strict local maximality — is Theorem 3.5 and Theorem 6.3 of the
article, and lies outside what the code certifies.**

---

## Constructor fidelity

Everything above certifies properties of the object that `coordinates(z)`
produces. That this object is the polygon Bingane and Audet published is a
separate claim, and it is an attribution rather than a theorem.

It is checked directly. The original OPTIGON constructor
`cstrt_audet_ngon.jl` is executed unmodified and its 30 coordinates compared
against `coordinates(z)`. In double precision the worst discrepancy is one unit
in the last place. At 256 bits it falls to about $5.2\times10^{-39}$, and that
residual is the truncation of the 38-digit root literal the package stores, not
a difference of formulas. For scale, the certified root box has radius
$10^{-30}$, nine orders of magnitude larger.

The article's Section 5 transcription of the constructor — $x(t)$, $F(t)$ and
the root interval — agrees with the OPTIGON source character for character.

---

## Reproducibility

Remark 5.1 of the supplementary material states: "The verification uses outward rounded interval
arithmetic at 256 bits, together with exact rational polynomial arithmetic.
Exact equalities are never inferred merely because an interval evaluation
contains zero."

Correspondence with this repository, which **is** that supplementary package:

| Element | Location |
|---|---|
| complete scripts | `scripts/` (`run_all.jl`, `02`–`06_*.jl`), `src/A16Certificate.jl` |
| execution log | `logs/final_run.txt` — versions, precision, commit, SHA256, UTC |
| exact identity checks | `scripts/06_exact_identities.jl`, `src/A16Certificate.jl` |
| independent SymPy verification | `tools/independent_check.py` and its output |
| 256-bit outward rounded intervals | `IntervalArithmetic.jl` with `setprecision(BigFloat, 256)` |
| exact rational polynomial arithmetic | `Rational{BigInt}` in `src/A16Certificate.jl` |
| formal layer | `lean/`, kernel-checked; see `lean/README.md` for its scope |

---

## Mathematical scope of the certificate

What is **established**, given the correctness of Theorems 3.5 and 6.4 and the
fidelity of `coordinates(z)` to the Bingane–Audet constructor:

- **Existence and uniqueness** of the exact real root $z^\ast$ — 6.2(1).
- **31 exact active equalities** — Lemma 6.1: 29 universal, 2 equivalent to
  $F(z^\ast)=0$ — with no tolerance and no interval containing zero.
- **Strict convexity and cyclic order** — 6.2(3) with Lemma L2.
- **Inactive margin** $\delta_{\mathrm{inact}}>0$ — 6.2(4), directed bound.
- **Rank** $\operatorname{rank}D=30$ — 6.2(6) — hence
  $\dim\mathcal I_{\mathrm{eq}}=3$ and
  $\mathcal I_{\mathrm{eq}}=R_{\mathrm{eq}}$.
- **Multipliers:** existence of a KKT representative satisfying the stationarity
  identity with every $\lambda_{ij}>0$ — 6.2(5). The family is affine of
  dimension 1 because LICQ fails; one positive representative is certified.
- **Strict topological local maximality** of perimeter modulo Euclidean motions
  — Theorem 6.3 via Theorem 3.5. The code certifies the hypotheses; the
  implication is the article's theorem.

What is **not** claimed, matching Section 7 of the article:

- **Global optimality** among all convex equilateral small hexadecagons. The
  article is explicit: "the global problem … is not addressed here." It would
  require an enumeration of active classes plus exclusion.
- **Second-order properties.** Not needed here, because
  $\mathcal I_{\mathrm{eq}}=R_{\mathrm{eq}}$.
- **Constant rank on a full neighbourhood of $\mathbb R^{33}$**: neither
  computed nor claimed. Regularity is computed over the curve in $z$, including
  the exact point, and Proposition 6.2(6) concludes rank 30 **at the exact
  configuration**. Theorem 3.5 needs no more.

> **On the output of `run_all.jl`.** The final banner prints
> `TOPOLOGICAL LOCAL MAXIMALITY: NOT ESTABLISHED BY *THIS* RUN — PROVED IN
> LEAN`, followed by clarifying lines. This means: **the interval computation
> alone** does not prove topological maximality — it certifies the hypotheses of
> Theorem 3.5. The conclusion is proved separately and checked by the Lean
> kernel (`Chiquipoli.Feasible.A16_locally_maximal`, the article's
> **Theorem 6.3**). There is no contradiction;
> the banner describes the scope of the computation, not that of the theorem.

---

## Referee re-reading

Re-read adversarially, looking for hidden hypotheses, unjustified equivalences,
and claims stronger than what is proved.

- **Explicit hypotheses:** independence of the rigid motions (L1); the convexity
  criterion (L2); non-uniqueness of multipliers from the failure of LICQ (C.0,
  accommodated by Definition 2.8); fidelity of `coordinates(z)` to the
  constructor, now checked directly against OPTIGON.
- **Justified equivalences:** $H_{i,j}>0 \Leftrightarrow$ strict convexity (L2);
  $\det Q\neq0\Rightarrow\rho=0$ (exact algebra with L1); the 2 conditional
  identities $\Leftrightarrow F(z^\ast)=0$.
- **Calibrated claims:** 29 identities stronger than any interval enclosure, 2
  equivalent to $F(z^\ast)=0$; "unique root" bounded to the article's search
  interval by monotonicity; the neighbourhood question settled by Remark 3.6,
  since first order does not need constant rank; topological maximality
  attributed to Theorem 3.5 via Lemma 3.4, not to the computation.
- **Numerical agreement verified** against Proposition 6.2, digit for digit:
  smallest support determinant $0.0074882049\ldots$, margin
  $0.0080997106\ldots$, $\min\lambda$ $0.0918667776\ldots$, regularity bound
  $1.41938364\ldots\times10^{-25}$.
- **Remaining point of faith, declared:** the correctness of the article's
  theorems — Theorem 3.5 with Lemma 3.4, and Theorem 6.3 — is a separate
  mathematical review, and no machine performs it.

No additional mathematical errors and no undocumented logical gaps were found in
this re-reading.
