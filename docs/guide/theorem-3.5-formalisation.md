# Formalizing Theorem 3.5 in Lean 4

Status: **COMPLETE** (2026-09-08). Steps A-E plus both remaining glue steps.
`Chiquipoli.Feasible.A16_locally_maximal` closes the chain from the certified
`A16` coordinates to strict local maximality, unconditionally and `sorry`-free. All five files compile, are `sorry`-free,
and depend only on `propext`, `Classical.choice`, `Quot.sound`. The estimates
below are left as written so the plan can be compared with the outcome; see
"What actually happened" at the end.

Theorem 3.5 is the one statement of the paper that the Lean layer consumes but
does not prove. This file says exactly what is missing, in the order it has to
be built, and where the risk is concentrated.

## What already exists

Two of the three ingredients are done and `sorry`-free.

* **The algebraic core.** `FirstOrder.no_admissible_direction` takes precisely
  the data the blow-up argument produces --- `(v, η) ∈ K_eq`, `η ≥ 0`, and
  `v ⊥ R(p)` --- and returns `v = 0 ∧ η = 0`, which is the contradiction with
  `‖(v, η)‖ = 1` that closes the paper's proof. Its hypotheses `hIR` and
  `hlam` are exactly hypotheses (i) and (ii) of the theorem.
* **The slice, Lemma 3.4.** `SliceIFT` applies Mathlib's implicit function
  theorem and delivers `g`, with `g p = (0,0,0)`, `g_tendsto : g q → id as
  q → p`, and `g_hasStrictFDerivAt`. This is the `g(q^k) → id` step.

What is missing is the analytic bridge between them.

## What is missing

**Nothing in the Lean layer currently defines the feasible set.** Every
existing file works either with the *linearised* data (`FirstOrder.Data` takes
the differentials `s` and `u` as given) or with numeric facts at the single
configuration `A16` (`Convexity`, `InactiveMargin`, `Multipliers`). The
nonlinear constraints `|q_{i+1} − q_i| = m` and `|q_i − q_j| ≤ 1` appear
nowhere. That is the first thing to build, and everything else depends on it.

### A. The feasible set (new file `Feasible.lean`)

Define, on `(Fin n → ℝ × ℝ) × ℝ`:

```
e  i   (q, m) = ‖q (i+1) − q i‖² − m²
d  i j (q)    = ‖q i − q j‖² − 1
```

**Use the squared forms.** They are polynomial, hence differentiable
everywhere, and Mathlib differentiates them without a nonvanishing side
condition. The unsquared forms need `q i ≠ q j` at every step. The rescaling
is harmless: `D e_i = 2ℓ(⟨s_i, v_{i+1} − v_i⟩ − η)` with `s_i` the unit side
vector, and the docstring of `FirstOrder.Data` already records that positive
rescaling of `s` and `u` changes nothing in the multiplier identity.

Then `Feasible (q, m) := StrictlyConvex q ∧ CyclicOrder q ∧ (∀ i, e i (q,m) = 0)
∧ (∀ i j, d i j q ≤ 0)`.

Note the quantifier: feasibility constrains **all** diameters, not only the
active ones. The inactive ones carry no first-order information because
`d i j p < 0` strictly, and `InactiveMargin` already certifies that margin for
`A16` --- but the *openness* argument that turns a strict inequality at `p` into
a neighbourhood is step B, and is generic, not `A16`-specific.

Estimated 200-400 lines. Low risk, mostly definitional.

### B. Openness of strict convexity and labelled cyclic order

Each is a finite conjunction of strict inequalities in continuous (in fact
polynomial) functions of `q`: support determinants for convexity, the same for
cyclic order, and `d i j q < 0` for the inactive diameters. So each set is a
finite intersection of preimages of `(0, ∞)` under continuous maps, hence open.

`Continuous.isOpen_preimage` plus `isOpen_Ioi`, intersected over a `Fintype`.

This is the step the outside review called trivial, and it is close to it. It
is the only step where that description is accurate.

Estimated 100-200 lines. Low risk.

### C. The tangent cone is contained in the linearised cone

This is the theorem, and essentially all of the risk lives here.

**Statement.** Let `(q^k, m_k) → (p, ℓ)` be feasible, `t_k = ‖(q^k − p, m_k − ℓ)‖ > 0`,
and `(v^k, η_k) = (q^k − p, m_k − ℓ)/t_k → (v, η)`. Then `(v, η) ∈ K_eq(p, ℓ)`.

**Proof obligation per constraint.** For the sides, `e_i` is `HasFDerivAt` at
`(p, ℓ)` with derivative `De_i`, so

```
0 = e_i(q^k, m_k) − e_i(p, ℓ) = De_i[(q^k − p, m_k − ℓ)] + o(t_k).
```

Divide by `t_k`, use linearity, and pass to the limit through continuity of
`De_i`: `De_i[(v, η)] = 0`. The active diameters are the same computation with
`= 0` weakened to `≤ 0` and `le_of_tendsto` at the end. The inactive ones
contribute nothing, by B.

**Why this is the hard part.** The little-o bookkeeping is the fiddly bit: the
`o(‖x‖)` in `HasFDerivAt` has to be converted into a statement about the
sequence `t_k`, which means composing `Asymptotics.IsLittleO` with the sequence
and dividing. Mathlib does this kind of manipulation, but it is not a one-liner
and it has to be done once carefully and then reused `n + |active|` times.

Optionally restate the conclusion as `tangentConeAt ℝ Feasible (p, ℓ) ⊆ K_eq`,
using `mem_tangentConeAt_of_seq`
(`Mathlib/Analysis/Calculus/TangentCone/Defs.lean`). That is the standard
nonlinear-programming phrasing and makes the result quotable on its own, but it
is not needed for the proof --- our normalisation already produces the unit
vector that compactness wants. Do the direct version first.

Estimated 400-700 lines. **This is where the project either works or stalls.**

### D. Normalisation by the slice

Two facts, both new:

1. `e` and `d` are invariant under orientation-preserving Euclidean motions.
   Elementary but not free: it is a computation with `cos`/`sin` on each of
   `n` coordinates.
2. Replacing `q^k` by `g(q^k)·q^k` keeps feasibility (by 1), keeps convergence
   to `p` (by `g_tendsto`), keeps noncongruence to `p` (by definition of
   congruence), and lands the difference in `R(p)^⊥` --- which is exactly
   `Φ = 0`, the equation `SliceIFT` solves. So the third part should follow by
   unfolding, not by new analysis.

The one thing to watch: after normalising, `t_k > 0` must still hold. It does,
because a normalised competitor equal to `p` would be congruent to `p`, which
was excluded --- but this needs to be said in Lean rather than assumed.

Estimated 200-400 lines. Medium risk, concentrated in (1).

### E. Assembly

`isCompact_sphere` gives compactness of the unit sphere in the finite-
dimensional space `(Fin n → ℝ × ℝ) × ℝ`; `IsCompact.tendsto_subseq`
(`Mathlib/Topology/Sequences.lean`) extracts the convergent subsequence.
`η ≥ 0` comes from `m_k ≥ ℓ` by `le_of_tendsto`. Feed C, D, and that into
`no_admissible_direction`, get `v = 0 ∧ η = 0`, contradict `‖(v, η)‖ = 1`.

Estimated 150-300 lines. Low risk *given* A-D.

## Honest assessment

The claim that this needs "a moderate effort in topology" is wrong in one
direction and right in another. It is wrong that the work is topological ---
compactness and openness are the two easiest steps here, and B is genuinely
near-trivial. It is right that the work is bounded and that Mathlib has the
machinery. What it underestimates is step A, which does not exist at all today,
and step C, which is a real analysis proof and not an application of an existing
lemma.

A realistic total is 1000-2000 lines of Lean. The failure mode is not "Mathlib
lacks a theorem"; it is step C taking several times its estimate, which is the
normal outcome for the first serious analysis proof in a codebase that has so
far been algebraic and numeric.

## What actually happened

| Step | File | Estimated | Actual | Note |
|---|---|---|---|---|
| A | `Feasible.lean` | 200-400 | ~230 | as planned |
| B | `FeasibleOpen.lean` | 100-200 | ~100 | compiled almost first try |
| C | `FeasibleTangent.lean` | **400-700, high risk** | ~230 | **the risk did not materialise** |
| D | `FeasibleRigid.lean` | 200-400, medium risk | ~220 | as planned |
| E | `FeasibleMain.lean` | 150-300 | ~215 | as planned |

**The plan was wrong about step C, in our favour.** It budgeted the high risk on
the assumption that the first-order limits needed the `o(‖u‖)` of `HasFDerivAt`
converted into a statement about the sequence `t_k`. They do not. The squared
constraints chosen in step A are quadratic polynomials, so their Taylor
expansion terminates exactly — `eC_expand` and `dC_expand` are ring identities
with no remainder. Dividing by `t_k` and using homogeneity leaves
`eD[z_k] + t_k · eQ[z_k]`, and the second term vanishes because `t_k → 0`. No
little-o, no derivative, no continuous linear map: `ring` and the continuity of
two polynomials. The design decision in step A paid for step C.

Two things were found along the way and are worth recording.

* `nsq a = ‖a‖ ^ 2` is **false**. Mathlib gives `ℝ × ℝ` the sup norm, so
  `‖(3,4)‖ = 4`. The Euclidean length is defined explicitly as `elen`. The
  ambient norm used for the blow-up normalisation may be any norm — all are
  equivalent in finite dimension — but the constraint must be Euclidean.
* Convexity enters the paper's proof at exactly one point, to know that a nearby
  competitor inherits `p`'s labelled cyclic order. Here the constraints are
  label-indexed from the start, so that is free, and the blow-up needs nothing
  else from convexity. `IsFeasible` therefore drops it and the conclusion is
  *stronger* than the paper's; `IsFeasibleConvex` and `IsFeasibleConvex_imp`
  recover the printed statement.

Vacuity is guarded by six new negative controls (`nc19`-`nc24`), each removing
one load-bearing hypothesis and confirming the theorem no longer follows: the
sign of the diameter limit, activity at the base point, the rotation generator
of the slice, strict positivity of the multipliers, the direction of the side
length inequality, and activity in the blow-up. 24/24 rejected.

## The two glue steps, done

**1. Congruence.** `eventually_congruent_of_no_worse` discharges the slice
hypothesis rather than carrying it. A competitor is replaced by its normalised
representative `g(q)·q`: `isFeasible_move` says that costs no feasibility,
`tendsto_normCfg` that it still converges, and `eventually_phiGeom_zero` that it
satisfies the slice equation, which `slice_of_generators` turns into
orthogonality to all of `R(p)`. The conclusion is then stated about the original
competitor: side length exactly `ℓ`, and congruent to `p` by an
orientation-preserving Euclidean motion.

**2. `A16`.** `Instances/A16LocalMax.lean`. The join was not free, because the two halves
live in different normalisations: `FirstOrderA16` works in the *squared*
formulation (`t = ℓ²`, `κ = 1`, gradients `2(p_j − p_i)`), `Feasible` with `ℓ`
itself. So

    (A16Data z).sideD v (2ℓη) i = eD p ℓ v η i,   (A16Data z).diamD v e = dD p v (a e) (b e)

— the sides by the chain rule `d(ℓ²) = 2ℓ dℓ`, the diameters exactly. That is
`A16_bridge`, and it is why `no_blowup_sequence_gen`, `eventually_no_better` and
`eventually_congruent_of_no_worse` all carry a positive scale factor `sc` rather
than assuming `dataOf`. Negative control `nc25` confirms the factor cannot be
dropped: it is a unit error that would change nothing syntactically and rescale
every side multiplier against the diameter multipliers.

The final statement is unconditional. `exists_A16_root_in_Ioo_pi` pins the
constructor root to `(0, π)` — it is produced as `arccos c ∈ [0, π]`, and
`sin z > 0` rules out both endpoints — which is what makes `ℓ = 2 sin(z/2)`
positive.

```
theorem A16_locally_maximal :
    ∃ z l, 0 < l ∧ IsFeasibleConvex (A16p z, l) ∧
      ∀ᶠ y in 𝓝 ((A16p z, l) : Amb 16),
        IsFeasible y → l ≤ y.2 → Congruent y.1 (A16p z) ∧ y.2 = l
```

`nc26` confirms the conclusion cannot be strengthened past congruence:
translating or rotating `A16` gives another feasible configuration with the same
side length, arbitrarily close to it.

## What is still outside the Lean layer

Global optimality. Theorem 3.5 and this formalisation are local: they exclude
competitors in *some* neighbourhood, and the proof is by contradiction from a
convergent sequence, so it yields no lower bound on the radius. The paper says
this explicitly (Remark after Theorem 3.5).

For `A16` the radius is supplied by a separate theorem, Theorem 6.4, which is
now formalised by its own route (`Theory/Radius.lean`, `Theory/Coercive.lean`,
`Generated/Radius.lean`, `Instances/A16Radius.lean`; headline
`Chiquipoli.Feasible.A16_radius`). That route uses that the constraints are
quadratic, so it needs no quantitative slice, openness or first-order limits;
it does not make Theorem 3.5 itself quantitative, and it gives no radius for any
other polygon.

## Scope note

Formalising Theorem 3.5 did not fix a defect: the paper's proof was correct
mathematics before and is correct mathematics now. What it changed is that the
chain from `A16`'s certified constants to strict local maximality is
machine-checked end to end, and that the article can say so. The same route also
closes the square of Section 4 (`Feasible.square_strict_local_max`, the paper's
Proposition 4.2), which had stopped at the contradiction step.
