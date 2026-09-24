# ChiquipoliFamily — the Bingane–Audet family `A_n`, verified in Lean 4

This library proves, for members of the Bingane–Audet family `A_n`
(`n = 2^s ≥ 16`), the same statement that `ChiquipoliLean` proves for A16, and
proves it **about the published constructor itself**:

> the constructor equation of Bingane and Audet — as their published code
> OPTIGON writes it — has exactly one zero in their search bracket, and the
> polygon their code builds there is a strictly convex equilateral small
> `n`-gon that is a **strict local maximiser of the perimeter, modulo
> orientation-preserving Euclidean motions**.

It is built separately from `ChiquipoliLean` (`lake build ChiquipoliFamily`,
not a default target) and verified separately (`./verify_family.sh`, or
`make lean-family` from the repository root). Nothing in `ChiquipoliLean/`,
`verify.sh`, or the counts the article quotes depends on it.

Currently generated: **A16** (a second, independent proof of the A16 result,
by a different method), **A32** and **A64**.

## The headline theorems

| Lean name | Statement |
|---|---|
| `Chiquipoli.Family.A<n>.published_locally_maximal` | the full statement above, about `Optigon.F n` and the polygon `Q z` built by the transcribed upstream code |
| `Chiquipoli.Family.A<n>.locally_maximal_unique` | the same, about the certified polynomial form `P z` and `Fc` |
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

## How the certificate is tested against itself

A proof that has only ever succeeded says nothing about whether the checks
around it could fail. Three mechanisms, all generated and run the same way for
every case, address that.

**Negative controls with twins** (`lean/negative_controls_family/A<n>/`, checked
by `verify_family.sh`, step 4). Eleven per case, the same eleven for every `n`. Each
control is a **false** statement about `A_n`, attempted with the proof the
certificate itself uses. The generator checks that it is false before writing
it, exactly or with an explicit witness. Its twin, in `twin/`, is the same proof
of the true statement. The control must be rejected; the twin must compile.
Without the twin, a control could be "rejected" for an accidental reason, such
as a typo, a name that does not resolve, a timeout, or a tactic that would have
failed anyway. A timeout, a recursion limit or an unresolved name is therefore
not accepted as a rejection, and a twin that admits a goal is not accepted as
compiling.

| control | the false claim | why it matters |
|---|---|---|
| `fnc01_convexity_sign` | the support determinant (0,1,2) is negative | the enclosures cannot prove the wrong orientation |
| `fnc02_inactive_margin` | the tightest inactive pair is 10⁻⁶ closer than it is | the margin to 1 is real, not slack |
| `fnc03_side_needs_Fc` | side `n/4 − 1` holds for every `c` (by `ring`) | only a root of `Fc` makes it equal; twin: side 0 |
| `fnc04_stress_sign` | the smallest diameter stress is `≤ 0` | the sign of the multiplier comes from the certified enclosure |
| `fnc05_rigidity_needs_bars` | `I_eq ⊆ R_eq` from the sides alone | an `n`-gon with free diameters flexes (`n − 3` dimensions) |
| `fnc06_root_sign` | `Fc(clo)` has the other sign | the bracket brackets a root only with the true signs |
| `fnc07_bracket_nonempty` | `chi < clo` | if the interval were empty every "for c in [clo, chi]" fact would be vacuous |
| `fnc08_henneberg_degenerate` | a Henneberg vertex pinned twice to one vertex has a positive determinant | the determinant is identically 0 |
| `fnc09_enclosure_tight` | a vertex enclosure with half the radius the polynomial actually reaches | the radius is not a free parameter |
| `fnc10_uniqueness_is_local` | `Fc` has one root on `[0, 1]` | false: it changes sign at least 5, 11, 21 times there for n = 16, 32, 64; uniqueness holds only on the article's search bracket |
| `fnc11_published_bracket` | the published `F` has one zero on `(0, π/4)` | false: there `F` is a constant times `Fc(cos z)`, which has at least two zeros; the twin is upstream's own bracket |

The last row is a fact worth knowing on its own: the constructor equation has
many roots in `(0, 1)`, and the search interval `(2 arcsin(sin(π/n)/2), π/n)` is
what selects `A_n` among them.

**The stress test** (`tools/stress_family.sh`, `make stress-family`). The
certificate has two lines of defence. The generator checks every margin in
exact rational arithmetic before it writes Lean (each check is a named
`guard`), and Lean re-proves everything in the kernel. The stress test checks
that *each line alone* is enough. It plants one generator defect at a time
(`CHIQUI_MUTATE=<kind>`), always into a scratch directory, never into the
tracked tree:

| kind | defect | planted in |
|---|---|---|
| `encl` | a vertex centre off by `10⁴ρ` | `Encl1`, `encX1` |
| `conv` | a support line with reversed orientation | `Conv1`, `convD_0_2` |
| `far` | an active diameter listed as inactive | `Far1` |
| `side` | a side that needs `Fc` proved for every `c` | `Sides1` |
| `hen` | a Henneberg vertex pinned twice to one vertex | `Hen` |
| `stress` | Cramer's rule with one sign dropped | `StressDef`, `bal_k` |
| `root` | the signs of `Fc` at the bracket ends swapped | `Root` |
| `unique` | a derivative bound above `|Fc'(slo)|` | `Unique`, `dFc_lb` |

* *generator*: with the pre-checks on, the generator must stop with
  `pre-check failed` after planting the defect (24 of 24 for A16, A32, A64);
* *lean*: with `CHIQUI_MUTATE_UNGUARDED=1` the defect is written, and Lean must
  reject the planted file. Every error must lie inside the planted declaration,
  and every module the file imports must be byte-identical to the certified,
  built one (24 of 24). The Cramer defect, for instance, is refused by the
  generator's new equilibrium check at the centres, and by Lean at the balance
  of exactly the vertex whose formula was broken;
* *harness*: eleven sabotages of `verify_family.sh` itself, each run against
  the step responsible for it (`FAMILY_STEPS`). They are: an admitted goal in an
  unimported file, and one in a twin; an unresolvable and a missing audit name;
  a control deleted, and one made true; a twin made false; a control failing
  only by an unresolved name, and one failing only by a timeout; a hand edit of
  a certificate file, and one of a control. Then four slips in the
  transcription of the published constructor (`Optigon.lean`), each of which
  must break the identification proof in `A16/Published.lean` (15 of 15).

The unguarded switch refuses to run without a planted defect, and a mutated run
refuses to write anywhere but a scratch directory, so the switch cannot
produce an unchecked certificate.

## Where the data comes from

`lean/generators/family/gen_family.jl <n>` writes `ChiquipoliFamily/A<n>/`. Its
inputs are the repository's own exact arithmetic: the generic OPTIGON
constructor `audet_generic` and `audet_Fc` in `cases/exact_coords.jl`
(cross-checked against the upstream constructor in `test/literature.jl`), and
the active graph and root of `cases/A<n>_bingane_audet/candidate.jl`. The
coordinates are reduced to `(sin z · XC(c), YC(c))` with `XC, YC ∈ Q[c]` by
exact division by `cos 2z`, which the generator asserts. `verify_family.sh`
re-runs the generator and requires every file to reproduce byte for byte.

## The published polygon, in the kernel

The certificate is proved about a polygon in polynomial form, `P z`, and an
equation `Fc`. A reader needs to know that this polygon is the one Bingane and
Audet published. The link is proved in Lean, not only tested:

1. **`ChiquipoliFamily/Optigon.lean` transcribes the upstream constructor**
   (`cstrt_audet_ngon` from OPTIGON, the code that accompanies the paper, as
   vendored in `test/fixtures/optigon_reference.jl` with its SHA-256)
   statement for statement, for every `n`. The transcription keeps upstream's
   array assignments in their order, the quarter-turn shifts
   `sin(i(2z − π/2))`, the signs `(−1)^i` and the division by `cos 2z`. Each
   upstream statement it transcribes is quoted in the file.
2. **`A<n>/Published.lean` proves, for each case,** that each of the `n`
   vertices the transcribed code builds equals `P z k`, and that its equation
   `F` equals a constant times `Fc (cos z)` (`4096`, `2^28`, `2^60` for
   n = 16, 32, 64), wherever `cos 2z ≠ 0`. That condition holds on the whole
   search bracket, since `z < π/16`. The multiple angles go through
   `Chebyshev.lean` (`sin kz`, `cos kz` for `k ≤ 63`, shared by all cases).
3. **`published_locally_maximal`** then states the headline result about
   upstream's own objects: its `F` has exactly one zero in its bracket
   `(2 arcsin(sin(π/n)/2), π/n)`, and the polygon its code builds there, with
   side `2 sin(z/2)`, is a strict local maximiser.

What remains outside any proof assistant is whether `Optigon.lean` says what
the Julia source says; no kernel can read Julia. Three checks bound it:

* the test *Optigon.lean quotes the vendored upstream constructor verbatim*
  (`test/literature.jl`) requires every quoted upstream statement to occur in
  the vendored file, and the transcription to make exactly as many
  assignments as upstream (12 before the loop, 16 in it);
* four transcription slips — a sign `(−1)^i`, a symmetry `b[n−j] = b[j]`,
  the angle `(n/4 − 2)t` in `x(t)`, and the loop bound — are planted by
  `tools/stress_family.sh harness`. Each breaks the Lean identification, in
  `A16/Published.lean`;
* independently, the Julia generic constructor reproduces the vendored
  upstream code to `10⁻⁷⁰` at every vertex (`test/literature.jl`).

## What is not in Lean here

* **Global optimality.** As for A16, nothing here says anything about it.
* **Every `n = 2^s`.** Each case is proved separately. The pattern the three
  share is recorded in `docs/guide/general-framework.md`: `n − 1` active
  diameters, `deg Fc = n − 4`, and the `Fc`-sides being the two
  non-Henneberg bars.
