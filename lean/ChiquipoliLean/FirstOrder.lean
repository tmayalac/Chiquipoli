/-
**The first-order criterion (Theorem 3.5), algebraic core — kernel-checked.**

Everything else in this development certifies the *hypotheses* that Theorem 3.5
consumes. This file formalises part of the theorem itself.

WHAT IS PROVED HERE, AND WHAT IS NOT.

The paper's proof of Theorem 3.5 is a blow-up argument by contradiction with two
separable halves:

  ANALYTIC.  From a hypothetical sequence of feasible competitors
             `(q^k, ℓ_k) → (p, ℓ)` with `ℓ_k ≥ ℓ`, none congruent to `p`,
             produce a limiting unit vector `(v, η)` which (a) lies in the
             first-order feasible cone `K_eq`, (b) has `η ≥ 0`, and (c) is
             orthogonal to the rigid motions `R(p)`. This needs the local
             Euclidean slice (implicit function theorem), openness of strict
             convexity and labelled cyclic order, compactness of the unit
             sphere, and differentiability of the norm away from the origin.

  ALGEBRAIC. Show no such `(v, η)` exists — it must be zero, contradicting
             `‖(v, η)‖ = 1`.

The second half is what this file proves, in full and `sorry`-free. It is
finite-dimensional linear algebra and inequality reasoning: no limits, no
interval arithmetic, no floating point. The first half is formalised elsewhere
in this development, not here: the local Euclidean slice in
`ChiquipoliLean/Slice.lean` and `ChiquipoliLean/SliceIFT.lean`, the openness and
blow-up steps in `ChiquipoliLean/FeasibleOpen.lean` and
`ChiquipoliLean/FeasibleMain.lean`, and the two halves are joined in `thm_3_5`.
See `lean/README.md`, items 22–27, for the accounting.

WHY THIS IS THE USEFUL SPLIT. Both certified hypotheses are consumed entirely
inside the algebraic half — hypothesis (i) (the multiplier identity with
strictly positive active-diameter multipliers) in `no_ascent` and
`active_equality`, hypothesis (ii) (`I_eq = R_eq`) in `no_admissible_direction`.
The analytic half never touches them. So the step that turns *this package's*
certified output into the theorem's conclusion is exactly the step verified
here; what remains is standard analytic scaffolding, independent of `A16`.
`ChiquipoliLean/FirstOrderA16.lean` discharges both hypotheses at the certified
configuration, so at `A16` nothing here is assumed.

THE OBJECTIVE COEFFICIENT `κ`. The paper maximises the perimeter `L = nℓ`,
giving `DL[v,η] = nη`, so `κ = n`. This development's multiplier witness is
computed in the *squared* formulation, where the scalar variable is `t = ℓ²`
and the objective is `t` itself, giving `κ = 1` and `Σ αᵢ = −1` (`alpha_sum`).
Both reparametrisations rescale the multipliers by strictly positive factors, so
`λ > 0` means the same thing in each. Carrying `κ` as a parameter — with only
`0 < κ` ever used — covers both without privileging either; `no_ascent_paper`
and `multiplier_balance_paper` below recover the paper's normalisation.

The statements are kept at the paper's generality — arbitrary `n`, arbitrary
finite set of active diameter edges. Nothing in the argument needs `n = 16`.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace Chiquipoli.FirstOrder

open Finset

/-- The Euclidean inner product on `ℝ²`. -/
def ip (a b : ℝ × ℝ) : ℝ := a.1 * b.1 + a.2 * b.2

/-- `J(x,y) = (−y,x)`: the generator of infinitesimal rotation, as in the
paper's definition of `R(p)`. -/
def J (q : ℝ × ℝ) : ℝ × ℝ := (-q.2, q.1)

@[simp] lemma ip_zero_right (a : ℝ × ℝ) : ip a 0 = 0 := by simp [ip]

lemma ip_self_nonneg (a : ℝ × ℝ) : 0 ≤ ip a a := by
  simp only [ip]; nlinarith [sq_nonneg a.1, sq_nonneg a.2]

lemma eq_zero_of_ip_self_eq_zero {a : ℝ × ℝ} (h : ip a a = 0) : a = 0 := by
  simp only [ip] at h
  have h1 : a.1 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2]
  have h2 : a.2 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2]
  exact Prod.ext h1 h2

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The inner product on displacement fields, `⟪v,w⟫ = Σᵢ ⟪vᵢ, wᵢ⟫`. This is the
one implicit in the paper's slice condition `q − p ∈ R(p)^⊥`. -/
def cip (v w : Fin n → ℝ × ℝ) : ℝ := ∑ i, ip (v i) (w i)

lemma eq_zero_of_cip_self {v : Fin n → ℝ × ℝ} (h : cip v v = 0) : v = 0 := by
  have hnn : ∀ i ∈ (univ : Finset (Fin n)), 0 ≤ ip (v i) (v i) :=
    fun i _ => ip_self_nonneg _
  have h' := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  funext i
  exact eq_zero_of_ip_self_eq_zero (h' i (mem_univ i))

/-- First-order data at a strictly convex equilateral small `n`-gon: the side
vectors `sᵢ`, the active diameter edges with their vectors `u_ij` and endpoints,
and the configuration `p` (which enters only through the rigid motions `R(p)`).

This is *data*, not a claim. That `s i` points along side `i` and `u e` along an
active diameter is what the rest of the package certifies for `A16`; the results
below hold for any data meeting the stated hypotheses. The vectors need not be
normalised — rescaling side `i` by `cᵢ > 0` rescales `αᵢ` by `1/cᵢ`, and the
same for the diameters, so neither the multiplier identity nor strict positivity
is affected. -/
structure Data (n : ℕ) (ι : Type*) where
  /-- Vector along side `i`, from `pᵢ` towards `pᵢ₊₁`. -/
  s : Fin n → ℝ × ℝ
  /-- Vector along the active diameter indexed by `e`. -/
  u : ι → ℝ × ℝ
  /-- First endpoint of active diameter `e`. -/
  a : ι → Fin n
  /-- Second endpoint of active diameter `e`. -/
  b : ι → Fin n
  /-- The configuration itself. -/
  p : Fin n → ℝ × ℝ

variable [NeZero n] (D : Data n ι)

/-- `De_i(p,ℓ)[v,η] = ⟪sᵢ, vᵢ₊₁ − vᵢ⟫ − η`, the paper's side differential. -/
def Data.sideD (v : Fin n → ℝ × ℝ) (η : ℝ) (i : Fin n) : ℝ :=
  ip (D.s i) (v (i + 1) - v i) - η

/-- `Dd_ij(p)[v] = ⟪u_ij, v_j − v_i⟫`, the paper's diameter differential. -/
def Data.diamD (v : Fin n → ℝ × ℝ) (e : ι) : ℝ :=
  ip (D.u e) (v (D.b e) - v (D.a e))

/-- The first-order feasible cone `K_eq(p,ℓ)`: sides stay equal to first order,
active diameters may break inward. -/
def Data.Keq (v : Fin n → ℝ × ℝ) (η : ℝ) : Prop :=
  (∀ i, D.sideD v η i = 0) ∧ (∀ e, D.diamD v e ≤ 0)

/-- The active equality space `I_eq(p,ℓ)`: every active constraint differential
vanishes. -/
def Data.Ieq (v : Fin n → ℝ × ℝ) (η : ℝ) : Prop :=
  (∀ i, D.sideD v η i = 0) ∧ (∀ e, D.diamD v e = 0)

/-- Infinitesimal rigid motions `R(p)`: a translation plus a rotation rate. -/
def Data.R (v : Fin n → ℝ × ℝ) : Prop :=
  ∃ (t : ℝ × ℝ) (ω : ℝ), ∀ i, v i = t + ω • J (D.p i)

/-- The multiplier identity, as an identity of linear functionals: it must hold
for *every* `(v, η)`, which is what the paper states. `κ` is the objective
coefficient (`κ = n` for the perimeter `L = nℓ`). -/
def Data.MultiplierIdentity (κ : ℝ) (α : Fin n → ℝ) (lam : ι → ℝ) : Prop :=
  ∀ (v : Fin n → ℝ × ℝ) (η : ℝ),
    κ * η = (∑ i, α i * D.sideD v η i) + (∑ e, lam e * D.diamD v e)

section
variable {D} {κ : ℝ} {α : Fin n → ℝ} {lam : ι → ℝ}

/-- **Proposition 3.1 (first-order no-ascent criterion).** With the multiplier
identity and nonnegative active-diameter multipliers, the objective cannot
increase to first order along any direction in the feasible cone. -/
theorem no_ascent (hm : D.MultiplierIdentity κ α lam) (hlam : ∀ e, 0 ≤ lam e)
    {v : Fin n → ℝ × ℝ} {η : ℝ} (hK : D.Keq v η) :
    κ * η ≤ 0 := by
  rw [hm v η]
  have hside : (∑ i, α i * D.sideD v η i) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hK.1 i]; ring
  rw [hside, zero_add]
  refine Finset.sum_nonpos fun e _ => ?_
  have h1 := hlam e
  have h2 := hK.2 e
  nlinarith

/-- **Remark 3.2 (multiplier balance).** Comparing the `η` coefficients in the
multiplier identity forces `Σ αᵢ = −κ`. The package uses this as an exact
consistency check on the computed multipliers. -/
theorem multiplier_balance (hm : D.MultiplierIdentity κ α lam) :
    (∑ i, α i) = -κ := by
  have h := hm 0 1
  simp only [Data.sideD, Data.diamD, Pi.zero_apply, sub_self, ip_zero_right,
    zero_sub, mul_zero, mul_neg, mul_one] at h
  rw [Finset.sum_neg_distrib, Finset.sum_const_zero, add_zero] at h
  linarith

/-- **Lemma 3.3 (positive multipliers force active equality).** If the first
variation vanishes on a feasible direction and every active-diameter multiplier
is strictly positive, every active diameter differential vanishes: a zero sum of
nonpositive terms with strictly positive weights.

Strict positivity is exactly what is needed — with `λ ≥ 0` a vanishing sum can
hide a strictly negative term against a zero multiplier, and the conclusion
fails. That is the content of negative control `nc11`. -/
theorem active_equality (hm : D.MultiplierIdentity κ α lam) (hlam : ∀ e, 0 < lam e)
    {v : Fin n → ℝ × ℝ} {η : ℝ} (hK : D.Keq v η) (hz : κ * η = 0) :
    ∀ e, D.diamD v e = 0 := by
  have hside : (∑ i, α i * D.sideD v η i) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hK.1 i]; ring
  have hsum : (∑ e, lam e * D.diamD v e) = 0 := by
    have h := hm v η; rw [hz, hside, zero_add] at h; linarith
  have hnp : ∀ e ∈ (univ : Finset ι), lam e * D.diamD v e ≤ 0 := by
    intro e _
    have h1 := (hlam e).le
    have h2 := hK.2 e
    nlinarith
  have hz' := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hsum
  intro e
  rcases mul_eq_zero.mp (hz' e (mem_univ e)) with h | h
  · exact absurd h (ne_of_gt (hlam e))
  · exact h

/-- **Theorem 3.5, algebraic core: there is no nonzero admissible blow-up
direction.**

The hypotheses are exactly the two the certificate establishes — the multiplier
identity with strictly positive active-diameter multipliers, and
`I_eq ⊆ R_eq` — together with the two facts the analytic half of the paper's
proof supplies about the limiting direction: `η ≥ 0`, because the competitors
have perimeter at least `L(p,ℓ)`, and `v ⊥ R(p)`, because the local Euclidean
slice normalises each competitor into `R(p)^⊥`.

The conclusion `v = 0 ∧ η = 0` contradicts `‖(v,η)‖ = 1`, which is how the paper
closes the argument.

Only the `⊆` half of hypothesis (ii) is used; `R_eq ⊆ I_eq` holds for any
configuration and is proved separately as `dsq_rigid`. -/
theorem no_admissible_direction (hκ : 0 < κ)
    (hm : D.MultiplierIdentity κ α lam) (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Fin n → ℝ × ℝ, D.Ieq w 0 → D.R w)
    {v : Fin n → ℝ × ℝ} {η : ℝ}
    (hK : D.Keq v η) (hη : 0 ≤ η) (hslice : ∀ r, D.R r → cip v r = 0) :
    v = 0 ∧ η = 0 := by
  -- Step 1: the first variation is ≤ 0, while `η ≥ 0` and `κ > 0` force it ≥ 0.
  have hle := no_ascent hm (fun e => (hlam e).le) hK
  have hη0 : η = 0 := by nlinarith
  -- Step 2: it therefore vanishes, so every active diameter differential
  -- vanishes and the direction lies in `I_eq`.
  have hz : κ * η = 0 := by rw [hη0, mul_zero]
  have hI : D.Ieq v 0 := by
    refine ⟨fun i => ?_, active_equality hm hlam hK hz⟩
    have h := hK.1 i; rwa [hη0] at h
  -- Step 3: hypothesis (ii) puts it in `R(p)`; the slice puts it in `R(p)^⊥`;
  -- a vector orthogonal to itself is zero.
  exact ⟨eq_zero_of_cip_self (hslice v (hIR v hI)), hη0⟩

/-- The paper's normalisation of `no_ascent`: objective `L = nℓ`, so `κ = n` and
the conclusion is `DL[v,η] = nη ≤ 0`. -/
theorem no_ascent_paper (hm : D.MultiplierIdentity (n : ℝ) α lam)
    (hlam : ∀ e, 0 ≤ lam e) {v : Fin n → ℝ × ℝ} {η : ℝ} (hK : D.Keq v η) :
    (n : ℝ) * η ≤ 0 := no_ascent hm hlam hK

/-- The paper's normalisation of `multiplier_balance`: `Σ αᵢ = −n`. -/
theorem multiplier_balance_paper (hm : D.MultiplierIdentity (n : ℝ) α lam) :
    (∑ i, α i) = -(n : ℝ) := multiplier_balance hm

/-- The paper's normalisation of the core theorem: `κ = n`, positive because
`n ≠ 0`. -/
theorem no_admissible_direction_paper
    (hm : D.MultiplierIdentity (n : ℝ) α lam) (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Fin n → ℝ × ℝ, D.Ieq w 0 → D.R w)
    {v : Fin n → ℝ × ℝ} {η : ℝ}
    (hK : D.Keq v η) (hη : 0 ≤ η) (hslice : ∀ r, D.R r → cip v r = 0) :
    v = 0 ∧ η = 0 := by
  refine no_admissible_direction ?_ hm hlam hIR hK hη hslice
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

end

end Chiquipoli.FirstOrder
