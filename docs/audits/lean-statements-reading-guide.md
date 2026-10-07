# Reading the Lean statements: what a human has to check

A kernel-checked proof settles that a theorem follows from its definitions. It does **not** settle
that the theorem, as written, says what the article says. That last step is a reading task, it is
the main risk of any formalisation, and no script in this repository can do it. This guide is for the
person who does it: it lists the definitions to read, what they mean in plain terms, the theorem
that backs each claim of the article, and what the Lean statements deliberately do not say.

Everything below was read from the sources of the tag this file is committed with. The file paths
and line-level statements can be inspected with `lake env lean` (see the last section).

## 1. The five definitions to read

All five are in `lean/ChiquipoliLean/Theory/Feasible.lean` and `FeasibleMain.lean`.

| Lean | Reading |
|---|---|
| `Cfg n := Fin n → ℝ × ℝ` | A labelled configuration of `n` points of the plane. |
| `Amb n := Cfg n × ℝ` | A configuration together with a scalar `m`, the intended common side length. The topology is the product topology; any norm on this finite-dimensional space gives the same neighbourhoods. |
| `eC i (q, m) := ‖q(i+1) − q(i)‖² − m²` | Side `i` has length `m`, in squared form (indices are in `Fin n`, so side `n−1` closes the polygon). `‖·‖` is the **Euclidean** length `nsq`; Mathlib's `‖·‖` on `ℝ × ℝ` is the sup norm and is *not* used (see the docstring of `elen`). |
| `dC i j q := ‖q(j) − q(i)‖² − 1` | The pair `{i, j}` is at distance exactly 1 when this is `0`. |
| `Small q := ∀ i j, dC i j q ≤ 0` | Diameter at most 1, over **all** pairs, not only the active ones. |

From these:

* `Equilateral (q, m) := ∀ i, eC i (q, m) = 0`.
* `IsFeasible (q, m) := Small q ∧ Equilateral (q, m) ∧ 0 < m`.
  **No convexity is imposed.** This makes the theorems *stronger* than the article's (the neighbourhood
  contains non-convex competitors too); `IsFeasibleConvex` (= `ConvexOrdered ∧ IsFeasible`) is what the
  certified polygon itself is shown to satisfy. The docstring of `IsFeasible` explains why dropping
  convexity is harmless for the proof.
* `ConvexOrdered q := ∀ i j, j ≠ i → j ≠ i+1 → 0 < cross (q i) (q (i+1)) (q j)`: every vertex lies
  strictly to the left of every directed edge. This is strict convexity **with the labelled
  counter-clockwise order**.
* `Congruent q p := ∃ c, moveCfg c q = p`, where `c = (a, b, θ)` and `moveCfg c` applies
  `x ↦ R_θ x + (a, b)` to every vertex. So congruence means *orientation-preserving* motions only
  (translations and rotations), with the labelling kept. A reflection is not a motion here.

**Perimeter.** For an equilateral `n`-gon with side `m` the perimeter is `n·m`, so "larger perimeter"
and "larger `m`" are the same thing; the theorems speak about `m` (`y.2`).

## 2. What "strict local maximiser modulo motions" looks like in Lean

Every main theorem has this shape (here for a configuration `p` of side `l`):

```lean
∀ᶠ y in nhds ((p, l) : Amb n),
  IsFeasible y → l ≤ y.2 → Congruent y.1 p ∧ y.2 = l
```

In words: *there is a neighbourhood of `(p, l)` such that every equilateral small `n`-gon `y` in it,
whose side is at least `l`, is carried onto `p` by a rotation and a translation, and has side exactly
`l`.* That is a strict local maximum of the perimeter modulo orientation-preserving motions. The
companion `∀ᶠ y …, IsFeasible y → y.2 ≤ l` is the plain local maximum.

Two things to notice when reading it:

1. The competitor `y` keeps its labelling, and "near" is meant in the coordinates of the plane. A
   mirror image of `p` has the opposite orientation, so it is not near `p`; a relabelled copy of `p` is
   at a fixed positive distance from it (unless it equals `p`). So nothing is lost by fixing the
   labelling and by allowing only orientation-preserving motions.
2. `p` itself is shown to be strictly convex (`IsFeasibleConvex (p, l)`), so the theorem is not about a
   degenerate configuration.

## 3. Which theorem backs which claim

| Claim of the article | Lean theorem | File |
|---|---|---|
| Theorem 3.5, the first-order criterion (hypotheses: positive multipliers on the active diameters, `I_eq ⊆ R_eq`) | `Chiquipoli.Feasible.thm_3_5` (and `thm_3_5_le`) | `ChiquipoliLean/Theory/FeasibleMain.lean` |
| `A₁₆` is a strict local maximiser, with the unique root of its constructor equation in the search interval | `Chiquipoli.Feasible.A16_locally_maximal` | `ChiquipoliLean/Instances/A16LocalMax.lean` |
| `A₁₆`, `A₃₂`, `A₆₄`, stated about the **published** constructor (OPTIGON, transcribed in `ChiquipoliFamily/Optigon.lean`) | `Chiquipoli.Family.A<n>.published_locally_maximal` | `ChiquipoliFamily/Polynomial/A<n>/Published.lean` |
| `Z₃₂`, `Z₆₄`: at **every** root of the defining equation in a certified bracket, the polygon is a strict local maximiser; and a root exists there | `Chiquipoli.Family.Z<n>.locally_maximal_at`, `…locally_maximal` | `ChiquipoliFamily/Polynomial/Z<n>/Main.lean` |
| `Z₃₂`, `Z₆₄`: that root is the only one in the search interval `(0, π/n]` | `Chiquipoli.Family.Z<n>.locally_maximal_unique` | `ChiquipoliFamily/Polynomial/Z<n>/Unique.lean` |

For `Z₆₄` the uniqueness is stated **among the configurations that exist**: the hypothesis `0 ≤ rad
(cos z')` is part of the statement, because the polygon needs a real square root and, in Lean, `√` of a
negative number is `0`. The statement is not weaker in substance (where `rad < 0` there is no
polygon), but it is the one place where the reader should check that the hypothesis is the right
one. The polygon exists exactly where the radicand `rad` is nonnegative, the last 13 % of
`(0, π/64]`.

## 4. What the formal statements do not say

These are limits of the formalisation, not defects, and the article states them too.

* **Global optimality.** Nothing here says a global maximiser exists or what it is. In fact, for
  `n = 32, 64` the polygons `Z_n` have larger perimeter than `A_n`, so `A_32` and `A_64` are local
  but not global maximisers.
* **The radius of Theorem 6.4.** The explicit radius `r ≥ 6.63·10⁻⁴` for `A₁₆` is a certificate of the
  Julia pipeline (interval Cholesky); Lean proves only that some neighbourhood exists.
* **That `Z₃₂` and `Z₆₄` are the polygons of Bingane and Audet.** There is no published constructor to
  transcribe; the polygons are rebuilt from the statements of their Propositions 1 and 2. This is
  checked against the published `t` and perimeter to ten digits, not in Lean.
* **That `Fc` (`Z₃₂`) and `G` (`Z₆₄`) are the equations of those Propositions.** They are the exact
  reductions to `c = cos t`, asserted by exact division in the generators and in the Julia certificates.
  Lean's theorems are about `Fc` and `G` as defined.
* **Transcription fidelity of OPTIGON.** The Lean transcription of the constructor says what it says; that
  it agrees with the upstream Julia file is checked by running the upstream file unchanged (see the
  article's section on the construction of the polygons), not by the kernel.

## 5. How to check mechanically what you have read

From `lean/`:

```bash
# the axioms of a headline theorem (expected: propext, Classical.choice, Quot.sound)
printf 'import ChiquipoliFamily.Polynomial.Z64.Unique\n#print axioms Chiquipoli.Family.Z64.locally_maximal_unique\n#check @Chiquipoli.Family.Z64.locally_maximal_unique\n' > /tmp/t.lean
lake env lean /tmp/t.lean
```

`ChiquipoliFamily/Audit.lean` does this for every headline theorem, and `./verify_family.sh` fails if one
is missing, if any axiom other than the three standard ones appears, if a `sorry`, `admit` or
`native_decide` is present, or if a negative control is accepted. A **negative control** is a false statement
attempted with the certificate's own proof; each one must be rejected, and its **twin** (the same proof of
the true statement) must compile, so a control cannot fail for an accidental reason. They show the
definitions above are not vacuous: for example, uniqueness of the root claimed on all of `[0, 1]`
is rejected (`negative_controls_family/Z64/fnc10_uniqueness_is_local.lean`), because `G` has other
roots there.

What this repository can show is that the proofs check and that the checks can fail. Whether the
statements of section 1 and section 3 are the right ones is the reader's judgement, and this guide is
written to make that judgement short.
