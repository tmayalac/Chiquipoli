# ChiquipoliLean — the A16 computational hypotheses, verified in Lean 4

This directory contains a [Lean 4](https://lean-lang.org) / Mathlib
formalization of the *exact algebraic* half of the A16 first-order certificate.
Where the Julia package certifies a statement by exact `Rational{BigInt}`
arithmetic or by rigorous interval arithmetic, Lean re-establishes it as a
kernel-checked theorem: the trust base drops from "Julia's rational arithmetic
and my code are correct" to "Lean's kernel is correct".

Everything here is machine-checked. Nothing is admitted (`sorry`-free), and
`scripts/verify.sh` proves that claim rather than asserting it.

---

## What is formally proved

| # | Statement | Lean name |
|---|-----------|-----------|
| 1 | Multiple-angle reduction `sin (k z) = sin z · U_{k-1}(cos z)`, `cos (k z) = T_k(cos z)`, for `k = 1..7` | `sin_1 … cos_7` |
| 2 | Each of the 16 vertices of the hand-transcribed trigonometric constructor equals its exact polynomial form | `red0 … red15` |
| 3 | The generated polynomial evaluates the constructor equation: `Fc (cos z) = F z` | `Fc_cos_eq_Ffun` |
| 4 | **Lemma 6.1** — all 16 side equalities and all 15 active-diameter equalities | `side_*`, `diam_*` |
| 5 | A root of the constructor equation exists, with `cos z` in a narrow certified bracket | `exists_constructor_root` |
| 6 | **Main theorem** — such a hexadecagon exists, is exactly equilateral, and has exactly unit active diagonals | `A16_exists` |
| 7 | The root is **unique across the paper's entire search interval**, and the same at the level of the angle `z` | `Fc_root_existsUnique_search`, `constructor_root_unique_in_search` |
| 8 | **The inactive margin** (Prop 6.2(4)) — each of the 89 non-active diagonals is strictly shorter than 1 | `inactive_*`, `lt_one_*` |
| 9 | **The diameter is exactly 1** — `∀ i j : Fin 16`, no pair exceeds 1, and `(0,7)` attains it | `diameter_eq_one` |
| 10 | **Strict convexity + labelled cyclic order** (Prop 6.2(3)) — every vertex lies strictly left of every edge, all 224 determinants | `cross_pos` |
| 11 | **Stationarity with strictly positive multipliers** (Prop 6.2(5)) — the weighted gradient sum vanishes at every vertex, `Σαᵢ = −1`, and all 15 diameter multipliers are positive | `multipliers_certified` |
| 12 | **`R_eq ⊆ I_eq`** — every rigid infinitesimal motion is annihilated by every constraint differential | `dsq_rigid` |
| 13 | **`I_eq ⊆ R_eq`** (Prop 6.2(6)) — a displacement killing every active differential *is* a rigid motion, and `dt = 0` | `kernel_is_rigid` |
| **14** | **The assembled certificate** — a single `z` at which all six gates hold *simultaneously* | **`A16_certificate`** |
| 15 | **Theorem 3.5, algebraic core** — Prop 3.1, Rem 3.2, Lem 3.3, and the contradiction step, for arbitrary `n` and arbitrary active diameter set | `no_ascent`, `multiplier_balance`, `active_equality`, `no_admissible_direction` |
| **16** | **That core, with both its hypotheses discharged at `A16`** — no multiplier or rank assumption remains | **`A16_no_admissible_direction`** |
| 17 | **Proposition 3.8 (first order instability)** — a positive first variation along a realising curve rules out local maximality | `increases_to_the_right`, `not_isLocalMax` |
| 18 | **Section 4, the square** — the multiplier identity with `λ = √2 > 0`, `I_eq ⊆ R_eq`, and no admissible direction | `square_multiplier_identity`, `square_Ieq_imp_R`, `square_no_admissible_direction` |
| 19 | **Section 4, the rhombus — proved outright, without Theorem 3.5** — the deformation stays equilateral and small, and the perimeter strictly increases | `rho_equilateral`, `rho_small`, `rho_diameter`, `rhombus_perimeter_increases` |
| 20 | **Proposition 6.2(2)** — the side length and perimeter, at the paper's nineteen digits | `cos_root_tight`, `side_length_bounds`, `perimeter_bounds` |
| 21 | **Proposition 6.2(6)** — `rank D(e,d) = 30`, by rank–nullity from the exact kernel | `rank_eq_thirty` |
| 22 | **Lemma 3.4, in full** — a map `g`, strictly differentiable at `p`, exists near `p`, solves the slice equation, and satisfies `g(p) = id` | `g`, `g_at_p`, `g_hasStrictFDerivAt`, `g_eventually_iff` |

| 23 | **The feasible set** — the nonlinear constraints `\|q_{i+1}-q_i\| = m` and `\|q_i-q_j\| ≤ 1`, in squared form, and the proof that the linearised cone is the same set either way | `IsFeasible`, `eC_eq_zero_iff`, `dC_nonpos_iff`, `Keq_iff` |
| 24 | **Openness** — strict convexity, the labelled cyclic order and the strict inactive margin are open conditions (Remark 2.7) | `isOpen_convexOrdered`, `eventually_dC_neg_of_tendsto` |
| 25 | **The first order limits** — the side equalities and active diameter inequalities pass to the blow-up limit; Taylor is exact because the constraints are quadratic | `eC_expand`, `eD_eq_zero_of_blowup`, `dD_nonpos_of_blowup` |
| 26 | **Euclidean invariance and the slice normalisation** — the constraints and the orientation do not see a motion; `g(q)·q` stays feasible, still converges, and lands in `R(p)^⊥` | `isFeasible_move`, `tendsto_normCfg`, `eventually_phiGeom_zero`, `slice_of_generators` |
| **27** | **Theorem 3.5 itself** — the blow-up argument, and the conclusion stated about the competitor rather than its normalised representative | **`thm_3_5`**, `thm_3_5_le`, `eventually_congruent_of_no_worse` |
| **28** | **Theorem 6.4** — the certified configuration is a strict local maximiser of the perimeter, modulo orientation-preserving Euclidean motions | **`A16_locally_maximal`**, `A16_bridge`, `A16_isFeasibleConvex` |

`A16_locally_maximal` is the statement to read first; `A16_certificate` is the
one to read second. Everything else is a lemma feeding them. Without the
assembly the development would prove a pile of *implications* plus an existence
statement, leaving "there is an object satisfying all of them" to the reader.

### Bernstein certificates: sign questions without interval arithmetic

Items 7–9 all reduce to one question repeated: *does a rational polynomial in
`c` keep one sign everywhere the root can live?* Each is answered by an exact
identity

```
(p(c) - m) * (b-a)^n  =  Σ_k A_k * (c-a)^k * (b-c)^(n-k),    A_k ≥ 0
```

which the kernel re-checks with `ring` plus nonnegativity of each factor. Exact
rationals throughout — no interval arithmetic, no floating point, no rounding
model in the trust base. The certificates are emitted by
`tools/bernstein.jl` from the same Julia arithmetic as everything else.

Two cross-checks fell out of this, each agreeing with a Julia result computed
by 256-bit interval arithmetic:

| quantity | Lean **declares** | Bernstein generation **computed** | Julia certifies |
|---|---|---|---|
| tightest inactive pair | — | `(4,12)` | critical pair `{4,12}` |
| inactive margin | `1 − d² ≥ 1/100` | `1 − d² = 0.016134` | `1 − d ≥ 0.0080997106581357295` |
| min support determinant | `D ≥ 3/100` | `D = 0.0383986` | `sin z*·D ≥ 0.0074882049306989244` |

**Read the first column, not the second.** The middle column is what the
generator computed while searching for a certificate; the theorems declare the
weaker uniform bounds in the first. They are weaker on purpose — a rounder
constant makes the Bernstein coefficients clear zero by a wider margin, and
nothing downstream needs more than strict positivity. But a referee comparing
numbers should know that `3/100` is what the kernel checks, and that it implies
only `sin z*·D ≥ 0.005850`, not the paper's `0.0074882`. Likewise `1/100`
implies only `1 − d ≥ 0.005013`, not `0.0080997`. The paper's sharper constants
are certified by the Julia interval run, not by Lean.

Note also that `Data`'s factored form differs by `sin z*`: Lean bounds the
determinant `D` in `(c,s)`-factored coordinates, and `cross = sin z* · D` with
`sin z* = 0.1950126738905248312`.

**How much these are worth, stated precisely.** They are *not* independent
derivations: both routes read the same coordinate polynomials out of
`src/A16Certificate.jl`. What differs is the arithmetic and the method — exact
rational Bernstein certificates versus outward-rounded 256-bit intervals — so
what they corroborate is the *numerics*, not the model. A mistake in the
constructor itself would propagate identically to both, and neither would
notice.

### Root uniqueness: the search interval, not `[-1,1]`

`Fc` does have nine sign changes on `[-1,1]`, and an early draft of this file
described excluding the other eight as the remaining gap. That was a
misreading of the boundary conditions. The paper's search range is

    z ∈ (2·asin(sin(π/16)/2), π/16) = (0.195401, 0.196350)

i.e. `c = cos z ∈ (0.9807853, 0.9809699)`, a window of width `1.8·10⁻⁴`.
Exactly **one** of the nine roots lies in it; the nearest other sits at
`c ≈ 0.9672`, far outside. Neither the paper nor the Julia certificate claims
uniqueness beyond that range.

So no subdivision is needed: `[slo, shi] = [0.98, 0.982]` covers the whole
search range and `Fc' ≥ 13` there by a *single* Bernstein certificate. The
width does matter, though — Bernstein bounds are not tight, and on the wider
`[0.97, 0.99]` the minimum coefficient goes negative and the certificate fails.
The interval is chosen just generous enough.

`constructor_root_unique_in_search` lifts this from the algebraic variable `c`
to the angle `z` itself, using injectivity of `cos` on `[0,1] ⊆ [0,π]` — which
is how the paper states it. That version is strictly stronger than needed: it
covers all `z ∈ [0,1]`, not merely the search window.

### `I_eq = R_eq` without `Matrix.det`

The rank gate is not the number "30"; it is that the only tangent vectors
annihilated by every active constraint differential are the rigid infinitesimal
motions. Stated that way, Lean never touches `Matrix.det` or the rank API —
dense linear algebra becomes a sparse chain of `linear_combination` steps.

`⊇` is a ring identity with no hypotheses at all. For `⊆`, the rigid part is
subtracted first: with `δ = w − rigid(a,b,e)` and `a,b,e` chosen to kill the
three free coordinates `x₀, y₀, y₁`, the triangular reduced system forces
`δ = 0` one pivot at a time, every right-hand side being already known to
vanish. Independence of the three rigid motions on those free coordinates rests
on `(p₁)¹ ≠ 0`, itself a Bernstein bound.

**Why the elimination is modulo `Fc`.** Measured on this exact system,
eliminating *without* reducing reaches **degree 1209 with 464-digit
coefficients** by step 30; reducing at every step holds it to **degree 11 and 9
digits**. The price is that each step is valid only mod `Fc`, so the reduction
quotient is carried explicitly:

```
rowNEW = rowOLD − f · rowPIVOT − (Σⱼ qⱼ Vⱼ) · Fc
```

which is exactly what `linear_combination` consumes — Julia divides, Lean adds
back. 97 such steps, none with more than 13 correction terms; all 30 pivots are
bounded away from zero on the bracket (worst `|pivot| ≥ 0.0575`).

The minor was re-chosen for Lean rather than inherited: Julia's pivot is
selected for interval-arithmetic stability, and dropping row 31 with columns
`x₀, y₀, y₁` instead gives a factor ~1.4 fewer nonzeros and roughly half the
coefficient size.

### The multipliers: Julia computes, Lean checks

Lean is never asked to *solve* the multiplier system — that would mean exact
linear algebra over a number field inside the kernel. `lean/tools/multipliers.jl`
computes the witness once, exactly, by Gaussian elimination over `ℚ[c]/(Fc)`;
Lean only verifies it. That asymmetry is what keeps the whole block cheap.

**Reparametrisation, stated plainly for reviewers.** The certified formulation
uses the *squared* side length `t = ℓ²` as the scalar variable:

    side i      :  |p_{i+1} − p_i|² − t = 0
    diameter ij :  |p_i − p_j|²     − 1 = 0
    objective   :  t

Maximising the perimeter `16√t` is the same as maximising `t`, and both
reparametrisations (`d ↦ d²`, `ℓ ↦ ℓ²`) rescale the multipliers by strictly
*positive* factors — so `λ > 0` here is exactly the paper's condition. The gain
is that every constraint gradient becomes `2(p_j − p_i)`, with no division by
`ℓ = √(2−2c)`, keeping the witness inside `ℚ(c,s)` instead of a degree-4
extension of `ℚ(c)`. This is a different formulation from the Julia gate, not a
literal transcription of it; the equivalence is the positive-rescaling argument
just given.

Because the active Jacobian has rank 30 rather than 31 (**LICQ fails**), the
multipliers form a 1-parameter affine family. The normalisation is pinned at
`λ_(0,9) = 1/375`, chosen inside the feasible window `(0.00074, 0.00459)`
computed in Julia — whose midpoint `0.0026679` coincides with the independent
least-squares solution.

#### These are **not** the paper's Table 2 multipliers

A referee comparing numbers will find no agreement, so it is said here plainly.
The paper (and the Julia certificate, which reproduces Table 2 exactly, min
`λ ≥ 0.0918667776833353997`) exhibits one point of that affine family; Lean
exhibits a **different** one. The ratio is not even constant:

| edge | paper Table 2 | Lean | ratio |
|---|---|---|---|
| `(0,7)` | 0.23567685 | 0.00266916 | 0.01133 |
| `(0,9)` | 0.20000000 | 0.00266667 | 0.01333 |
| `(6,13)` | 0.09186678 | 0.00124761 | 0.01358 |
| `(7,14)` | 0.11818995 | 0.00163168 | 0.01381 |

Two things cause this: the `t = ℓ²` reparametrisation rescales each constraint's
multiplier, and the normalisation is pinned at a different point of the family.

**Why this is nevertheless sound.** Theorem 3.5 does not require a *particular*
multiplier vector — it requires that **some** vector exist with every active
diameter multiplier strictly positive. The affine family is 1-dimensional and
both points lie in it with all `λ > 0`, so both witness the same hypothesis.
Lean certifies its own witness end to end; it does not, and does not claim to,
reproduce the paper's.

`stationarity_vertex` is stated over the actual vertices: `gradSum k z` is an
honest vector in the plane, and the theorem is that it is `(0,0)` for all
sixteen `k`. It is not a polynomial identity wearing a geometric name.

### Why "diameter exactly 1" is the load-bearing statement

Proving the fifteen active diagonals equal 1 does **not** make the object a
*small* polygon: some other diagonal could be longer. `sqd_le_one` closes that,
and it is stated for every pair `i j : Fin 16` rather than an enumerated list,
so a forgotten pair is impossible. Together with equilaterality, the Lean object
is now pinned down as *a strictly convex equilateral hexadecagon of diameter
exactly 1, in the labelled cyclic order* — which is how the fidelity gap to the
paper gets narrowed: not by checking coordinates by eye, but by proving
properties only the intended object has.

Note that `cross_pos` requires `0 < sin z`. That is not bookkeeping: the mirror
image of the configuration is an equally valid polygon with every determinant
flipped, so orientation has to be fixed. `exists_constructor_root_sin_pos`
supplies a root in the upper half plane, and negative control `nc7` checks that
dropping the hypothesis really does break the proof.

### The 29 / 2 split, confirmed by the kernel

The Julia certificate reports that of the 31 equalities, **29 are polynomial
identities in `z`** (true of the constructor for *every* parameter value) and
only **2** — the sides `(3,4)` and `(12,13)` — actually consume the constructor
equation `F z = 0`. Lean confirms this exactly, and sharply: for those two, the
defect is `Fc (cos z)` *on the nose*, i.e. the quotient of the exact polynomial
division is the constant `1`:

```
sqd (p3 z) (p4 z) - (2 - 2 cos z) = Fc (cos z)
```

so the Lean proof is literally `linear_combination hF`. The remaining 29 close
by `ring`.

### No zero-trap, structurally

The paper's "Golden Rule" forbids concluding `x = 0` from an interval that
happens to contain `0`. In this development the rule holds by construction:
there is no interval arithmetic and no floating point anywhere. The only
analytic ingredient is the intermediate value theorem in item 5, which is used
to prove a root *exists* — never to prove a quantity *vanishes*.

---

## What is **not** formalized here

This is the honest boundary. All six *computational* gates of the certificate
are now Lean theorems, with no residual "bracket only" caveat. What remains
outside is:

- ~~**The analytic half of Theorem 3.5, and with it Theorem 6.4.**~~
  **This is now formalized.** `Feasible.A16_locally_maximal` proves that the
  configuration built from the unique constructor root in the bracket is a
  strictly convex equilateral small hexadecagon and a strict local maximiser of
  the perimeter, modulo orientation-preserving Euclidean motions — Theorem 6.4
  of the paper, kernel-checked, `sorry`-free, with only the three standard
  axioms. `Feasible.thm_3_5` is the general statement.

  The chain runs: `Feasible.lean` defines the feasible set (the nonlinear
  constraints appeared nowhere before it); `FeasibleOpen.lean` proves openness
  of strict convexity, the labelled cyclic order and the inactive margin;
  `FeasibleTangent.lean` passes the constraints to the first-order limit;
  `FeasibleRigid.lean` proves invariance under Euclidean motions and builds the
  slice normalisation on top of `SliceIFT`; `FeasibleMain.lean` assembles the
  blow-up and discharges the slice hypothesis into congruence; `FeasibleA16.lean`
  instantiates at `A16`, bridging the two normalisations (`FirstOrderA16` works
  in the squared formulation `t = ℓ²`, so its `η` is `2ℓ` times this one — see
  `A16_bridge`, and negative control `nc25`, which confirms the chain-rule
  factor cannot be dropped).

  Nothing here uses KKT or any constrained-optimization library — the paper
  builds the argument directly. (For the record: Mathlib *does* have Lagrange
  multipliers, in `Mathlib/Analysis/Calculus/LagrangeMultipliers.lean`, and
  lists KKT as a `TODO`. Neither is needed.)

  Two consequences are worth stating plainly. `square_no_admissible_direction`
  is still only the contradiction step for the square — `Feasible.thm_3_5` would
  upgrade it, but that instantiation is not written. And the theorem remains
  **local and non-quantitative**: it excludes competitors in *some*
  neighbourhood, and since the proof is by contradiction from a convergent
  sequence it yields no lower bound on the radius.

- **The paper's sharpest constants in Proposition 6.2(3) and (4).** Both
  propositions are Lean theorems — strict convexity holds at all 224 support
  determinants, and all 89 non-active diagonals are strictly shorter than 1; the article and
  the Julia certificate say 105 inactive pairs, which is the same statement
  counted differently, since 120 = 105 + 15 active and the 105 include the 16
  sides, whose length is far below 1 and which `sqd_le_one` covers with every
  other pair —
  but at deliberately rounder constants (`D ≥ 3/100`, `1 − d² ≥ 1/100`) than the
  paper's `0.0074882049306989244` and `0.0080997106581357295`.

  This is not laziness, and it cannot be fixed by re-declaring the constant.
  Over the certified bracket `[clo, chi]` (width `10⁻⁶`) the quantity `1 − d²`
  for the critical pair `{4,12}` ranges over `[0.0161332810, 0.0161352093]`,
  while the paper's constant corresponds to `0.0161338160` — *inside* that
  range. So on that bracket the paper's bound is false at the upper end; it is a
  statement about the exact root, not about the bracket. Certifying it in Lean
  would need the `10⁻²²` bracket of `SideLength.lean` and a matching regeneration
  of all 299 Bernstein certificates. Proposition 6.2(2) is done at the paper's
  own sharpness precisely because that tight bracket exists for it.

- **Fidelity to the paper's prose.** No proof assistant can check that these
  definitions mean what the article says. That gap is narrowed here — not by
  eyeballing coordinates, but by pinning the object with properties only it has
  (equilateral, strictly convex, diameter exactly 1, in the labelled cyclic
  order) — but it is narrowed, not closed, and it never can be by machine.

Consequently: **Lean proves "the certified configuration is a strict local
maximum"** — `Feasible.A16_locally_maximal` — but it does *not* prove that this
configuration is the polygon Bingane and Audet published. That identification is
an attribution, checked by running the original OPTIGON constructor and
comparing coordinates (in Julia, see `docs/provenance-mapping.md`), and it is the
one link in the chain a proof assistant cannot close.

The other limits are unchanged and are mathematical, not architectural. The
theorem is **local**: it excludes competitors in *some* neighbourhood, and since
the proof is by contradiction from a convergent sequence it yields no lower
bound on the radius. Global optimality is untouched. This is stated plainly so
that no reader can take "verified in Lean" to mean more than it does.

---

## Architecture: why the polynomials are generated

`ChiquipoliLean/Generated.lean` is emitted by `tools/extract_polys.jl` from the
exact `Rational{BigInt}` arithmetic in `src/A16Certificate.jl`.
`ChiquipoliLean/Constructor.lean` is written **by hand**, transcribed from
`coordinates(z)` in the same Julia file — independently, in trigonometric form.

Lean then *proves the two agree* (`red0 … red15`). This is deliberate: a
transcription slip on either side, or a drift between them, becomes a compile
error rather than a silently wrong theorem. Check 5 of `verify.sh` additionally
re-runs the generator and requires byte-identical output, so the Lean layer
cannot fall out of sync with the certified Julia source.

---

## Reproducing

Requires [`elan`](https://github.com/leanprover/elan); the toolchain and
Mathlib revision are pinned by `lean-toolchain` and `lake-manifest.json`.

```bash
# elan installs to ~/.elan and does not always land on PATH for non-login shells
export PATH="$HOME/.elan/bin:$PATH"

cd lean
lake exe cache get     # prebuilt Mathlib oleans (~7 GB, first run only)
./scripts/verify.sh
```

The `.lake/` directory (toolchain + vendored Mathlib, ~7 GB) is gitignored;
`lake-manifest.json` pins the exact revision, so the build is reproducible
without committing any of it.

Expected output ends with `LEAN CERTIFICATE PASS`. The five checks are:

1. the development builds;
2. no source admits a goal (`sorry`), searched with Lean comments stripped;
3. every headline theorem depends only on `[propext, Classical.choice,
   Quot.sound]` — Lean's three standard axioms, and in particular **not**
   `sorryAx`;
4. all eighteen files in `negative_controls/` — deliberately false variants —
   **fail** to compile, and the count is pinned, so deleting one is a failure
   rather than a silently smaller check;
5. `Generated.lean` reproduces byte-for-byte from the Julia source.

### The negative controls

Check 4 is what makes checks 1–3 meaningful: a formalization can be perfectly
`sorry`-free and still prove nothing, if the statements are vacuous or the
constants are wrong.

| File | Asserts | Why it must fail |
|------|---------|------------------|
| `nc1_wrong_diameter.lean` | an active diagonal has squared length `2` | wrong constant |
| `nc2_wrong_side.lean` | side target is `2 - 3 cos z` | wrong constant |
| `nc3_inactive_diagonal.lean` | the *inactive* diagonal `(4,12)` equals `1` | not an active diameter |
| `nc4_conditional_without_root.lean` | side `(3,4)` holds **without** `F z = 0` | this is one of the two genuinely conditional identities |
| `nc5_margin_overclaim.lean` | the `(4,12)` margin is `1/10` | the true margin is `0.0161` |
| `nc6_margin_without_bracket.lean` | the inactive bound holds for **all** `c` | it holds only where the root lives |
| `nc7_convexity_without_orientation.lean` | convexity **without** `0 < sin z` | the mirror image flips every determinant |
| `nc8_multiplier_sign.lean` | a diameter multiplier is negative | they are certified strictly positive |
| `nc9_certificate_not_vacuous.lean` | `False`, from the certified bounds | if this compiled, *every* theorem here would be vacuous |
| `nc10_multipliers_only_nonneg.lean` | Lemma 3.3 with `λ ≥ 0` | a zero multiplier can mask a strictly negative term |
| `nc11_no_ascent_hypothesis.lean` | Theorem 3.5's core without `0 ≤ η` | the blow-up supplies that from `ℓ_k ≥ ℓ`; without it `η` need not vanish |
| `nc12_no_slice.lean` | that core without `v ⊥ R(p)` | false, not merely unproved: any rigid motion is a counterexample |
| `nc13_wrong_inclusion.lean` | that core with `R_eq ⊆ I_eq` in place of `I_eq ⊆ R_eq` | the free inclusion carries no information; the rank gate is the reverse one |
| `nc14_side_length_overclaim.lean` | `ℓ ≥ 0.1959554930055385229` | one unit too large in the 19th decimal; the tight bracket must not prove it |
| `nc15_wrong_rank.lean` | `rank D(e,d) = 31`, i.e. LICQ holds | the kernel is 3-dimensional, so the rank is 30 |
| `nc16_rhombus_wrong_sign.lean` | the rhombus perimeter increases for `δ < 0` too | the first variation is `16δ/√41`, negative there |
| `nc17_slice_without_distinct.lean` | Lemma 3.4's independence without two distinct vertices | with every vertex at the origin `T₃` vanishes and `R(p)` drops to dimension 2 |
| `nc18_gram_needs_distinct.lean` | the Gram map injective for *any* configuration, no distinctness hypothesis | the actual proof needs exactly that hypothesis to invoke `gram_nondegenerate` |

`nc4` is the sharpest of the constant-checking ones: if it compiled, the "29
unconditional vs 2 conditional" split — a headline finding of the certificate —
would be wrong. `nc9` is the sharpest overall: it asks for `False` from the
certified bounds, so if it ever compiled every theorem in the development would
be vacuously true.

**What a negative control does and does not show.** Each of these fails with
`unsolved goals` or `linarith failed` — i.e. *this proof script* does not close
*that* goal. That is weaker than "the statement is unprovable", which no such
test can establish. They are a guard against vacuity and against wrong
constants, not a completeness argument.

---

## Files

```
lean-toolchain              pinned Lean version
lakefile.toml               package + Mathlib dependency
lake-manifest.json          pinned Mathlib revision
ChiquipoliLean.lean         root import
ChiquipoliLean/
  Chebyshev.lean            multiple-angle reduction, k = 1..7
  Generated.lean            AUTO-GENERATED exact polynomial layer
  Constructor.lean          hand-written constructor + reduction lemmas
  Positivity.lean           Bernstein sign certificates on the bracket
  Identities.lean           the 31 equalities (Lemma 6.1)
  RootExists.lean           existence and uniqueness of the root (IVT)
  Diameter.lean             the diameter is exactly 1, over all pairs
  InactiveMargin.lean       the 89 non-active diagonals are shorter than 1
  Convexity.lean            224 support determinants, strict convexity
  Multipliers.lean          stationarity with positive multipliers
  Rank.lean                 I_eq = R_eq, both inclusions
  Certificate.lean          the assembled A16_certificate
  FirstOrder.lean           Theorem 3.5, algebraic core (general n)
  FirstOrderA16.lean        that core with both hypotheses discharged at A16
  Instability.lean          Proposition 3.8
  Examples.lean             Section 4: the square and the rhombus
  SideLength.lean           Proposition 6.2(2): side length and perimeter
  Rank30.lean               Proposition 6.2(6): rank D(e,d) = 30
  Slice.lean                Lemma 3.4: independence and Gram nondegeneracy
  SliceIFT.lean             Lemma 3.4: the implicit function theorem step
  Main.lean                 the headline theorem A16_exists
  Audit.lean                #print axioms report
negative_controls/          eighteen files that MUST fail to compile
scripts/verify.sh           the five-check verification
tools/extract_polys.jl      generator for Generated.lean
```
