/-
**The feasible set, as a subset of `(ℝ²)ⁿ × ℝ` — step A of Theorem 3.5.**

Every other file in this development works either with the *linearised* data
(`FirstOrder.Data` takes the differentials `s` and `u` as given) or with numeric
facts at the single configuration `A16`. The nonlinear constraints

  `|q_{i+1} − q_i| = m`   and   `|q_i − q_j| ≤ 1`

appear nowhere. This file introduces them. It is the object the blow-up half of
Theorem 3.5 argues about, and steps B–E all quantify over it.

SQUARED CONSTRAINTS, AND WHY.

We use `‖q_{i+1} − q_i‖² − m²` rather than `‖q_{i+1} − q_i‖ − m`, and
`‖q_i − q_j‖² − 1` rather than `‖q_i − q_j‖ − 1`. The squared forms are
polynomial in the coordinates, hence `C^∞` everywhere with no side condition;
the unsquared forms are non-differentiable where the argument vanishes and would
carry a `q i ≠ q j` hypothesis through every step. On the feasible set the two
formulations cut out the same set, because `m > 0` and `‖·‖ ≥ 0`
(`eC_eq_zero_iff`, `dC_nonpos_iff`).

The price is a positive rescaling of the differentials, and it is not a price:

  `D(eC i)[v,η] = 2ℓ·(⟪sᵢ, v_{i+1} − v_i⟫ − η) = 2ℓ · Data.sideD v η i`
  `D(dC i j)[v]  = 2·⟪u_ij, v_j − v_i⟫          = 2 · Data.diamD v e`

with `sᵢ = (p_{i+1} − p_i)/ℓ` and `u_ij = p_j − p_i`, exactly the paper's
vectors. The docstring of `FirstOrder.Data` already records that positive
rescaling of `s` and `u` leaves the multiplier identity and strict positivity
untouched, so the linearised cone `K_eq` is literally the same set either way
(`sideD_eq`, `diamD_eq`, and `Keq_iff` below).
-/
import ChiquipoliLean.Theory.FirstOrder
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder

variable {n : ℕ} [NeZero n]

/-! ## The ambient space -/

/-- A configuration: `n` labelled points of the plane. -/
abbrev Cfg (n : ℕ) := Fin n → ℝ × ℝ

/-- The ambient space of the problem: a configuration together with the scalar
side length. This is the `(q, m)` of the paper. -/
abbrev Amb (n : ℕ) := Cfg n × ℝ

/-- Squared Euclidean length, `‖a‖²`, written through `ip` so that it shares the
algebra already proved in `FirstOrder`. -/
def nsq (a : ℝ × ℝ) : ℝ := ip a a

lemma nsq_nonneg (a : ℝ × ℝ) : 0 ≤ nsq a := ip_self_nonneg a

lemma nsq_eq_zero_iff {a : ℝ × ℝ} : nsq a = 0 ↔ a = 0 :=
  ⟨eq_zero_of_ip_self_eq_zero, fun h => by simp [nsq, ip, h]⟩

/-- The Euclidean length on `ℝ²`, `|a| = √(a₁² + a₂²)`.

This is *not* `‖a‖`. Mathlib equips `ℝ × ℝ` with the sup norm, so `‖a‖` is
`max |a₁| |a₂|` and `nsq a = ‖a‖ ^ 2` is false. The paper's `|·|` is Euclidean
throughout, so it is defined here rather than borrowed. Nothing downstream is
affected: the ambient norm used for the blow-up normalisation may be any norm on
`(ℝ²)ⁿ × ℝ`, all of which are equivalent in finite dimension. -/
noncomputable def elen (a : ℝ × ℝ) : ℝ := Real.sqrt (nsq a)

lemma elen_nonneg (a : ℝ × ℝ) : 0 ≤ elen a := Real.sqrt_nonneg _

@[simp] lemma elen_sq (a : ℝ × ℝ) : elen a ^ 2 = nsq a :=
  Real.sq_sqrt (nsq_nonneg a)

/-! ## The constraint functions -/

/-- The side constraint at side `i`, in squared form:
`eC i (q, m) = ‖q_{i+1} − q_i‖² − m²`. -/
def eC (i : Fin n) (x : Amb n) : ℝ := nsq (x.1 (i + 1) - x.1 i) - x.2 ^ 2

/-- The diameter constraint on the pair `(i, j)`, in squared form:
`dC i j q = ‖q_j − q_i‖² − 1`. -/
def dC (i j : Fin n) (q : Cfg n) : ℝ := nsq (q j - q i) - 1

/-- Twice the signed area of the triangle `a b c`: positive exactly when `c` lies
strictly to the left of the directed edge `a → b`. Written through the existing
`ip` and `J`, so it needs no new algebra. -/
def cross (a b c : ℝ × ℝ) : ℝ := ip (J (b - a)) (c - a)

lemma cross_eq (a b c : ℝ × ℝ) :
    cross a b c = (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) := by
  simp [cross, ip, J, Prod.fst_sub, Prod.snd_sub]; ring

/-! ## Feasibility -/

/-- Strict convexity together with the labelled cyclic order, in the form the
certificate checks: every vertex lies strictly to the left of every directed
edge. This implies pairwise distinctness, no three collinear, and that every
vertex is extreme — Definition 2.1 of the paper — and it is manifestly an open
condition, which is what step B needs. -/
def ConvexOrdered (q : Cfg n) : Prop :=
  ∀ i j : Fin n, j ≠ i → j ≠ i + 1 → 0 < cross (q i) (q (i + 1)) (q j)

/-- Diameter at most `1`: the "small" condition of Definition 2.1. Note the
quantifier is over *all* pairs, not only the active ones. -/
def Small (q : Cfg n) : Prop := ∀ i j : Fin n, dC i j q ≤ 0

/-- All sides equal to `m`. -/
def Equilateral (x : Amb n) : Prop := ∀ i : Fin n, eC i x = 0

/-- The feasible set the blow-up argument actually uses: an equilateral small
`n`-gon, with no convexity imposed.

WHY CONVEXITY IS NOT HERE. The paper's Theorem 3.5 is stated for convex
competitors, but, as its Remark 3.6 records, the proof uses of the competitors
only the side and active diameter constraints. Here those constraints are
indexed by labels from the start (`eC i`, `dC i j`), so "side `i`" and "the
active diameter `{i,j}`" name the same constraints for a competitor as for `p`
without any appeal to its cyclic order. The blow-up then needs nothing else from convexity:
hypotheses (i) and (ii) of the theorem are conditions at `p`, and the slice of
Lemma 3.4 needs only `p i ≠ p j` for a single pair, again at `p`.

Dropping it therefore *strengthens* the conclusion — the neighbourhood excludes
nonconvex competitors too — and `IsFeasibleConvex_imp` below recovers the
paper's statement as a special case. `isOpen_convexOrdered` is kept because it
is what connects the two phrasings, and because it is what tells you that a
convex competitor near `p` really does carry `p`'s labelling. -/
def IsFeasible (x : Amb n) : Prop :=
  Small x.1 ∧ Equilateral x ∧ 0 < x.2

/-- Strictly convex competitors with `p`'s labelled cyclic order. Near a
strictly convex `p` these are the competitors of the paper's feasible class (the
closure of strictly convex positively labelled tuples). -/
def IsFeasibleConvex (x : Amb n) : Prop :=
  ConvexOrdered x.1 ∧ IsFeasible x

lemma IsFeasibleConvex_imp {x : Amb n} (h : IsFeasibleConvex x) : IsFeasible x := h.2

/-! ## The squared constraints cut out the intended set -/

/-- On configurations with `m > 0`, the squared side constraint says exactly what
the paper's unsquared one says. -/
lemma eC_eq_zero_iff {i : Fin n} {x : Amb n} (hm : 0 < x.2) :
    eC i x = 0 ↔ elen (x.1 (i + 1) - x.1 i) = x.2 := by
  rw [eC, sub_eq_zero]
  constructor
  · intro h
    have := elen_sq (x.1 (i + 1) - x.1 i)
    nlinarith [elen_nonneg (x.1 (i + 1) - x.1 i)]
  · intro h
    have := elen_sq (x.1 (i + 1) - x.1 i)
    rw [h] at this; linarith

omit [NeZero n] in
/-- Likewise for the diameter constraint; here no positivity hypothesis is
needed, since the target `1` is positive outright. -/
lemma dC_nonpos_iff {i j : Fin n} {q : Cfg n} :
    dC i j q ≤ 0 ↔ elen (q j - q i) ≤ 1 := by
  rw [dC, sub_nonpos]
  constructor
  · intro h
    nlinarith [elen_sq (q j - q i), elen_nonneg (q j - q i)]
  · intro h
    nlinarith [elen_sq (q j - q i), elen_nonneg (q j - q i)]

/-! ## Smoothness

The point of the squared formulation: both constraint families are polynomial in
the coordinates, so they are `C^∞` on the whole ambient space with no side
condition. Step B uses the continuity; step C uses the derivative. -/

lemma contDiff_eC (i : Fin n) : ContDiff ℝ ⊤ (eC i) := by
  unfold eC nsq ip
  simp only [Prod.fst_sub, Prod.snd_sub]
  fun_prop

omit [NeZero n] in
lemma contDiff_dC (i j : Fin n) : ContDiff ℝ ⊤ (dC i j) := by
  unfold dC nsq ip
  simp only [Prod.fst_sub, Prod.snd_sub]
  fun_prop

lemma continuous_eC (i : Fin n) : Continuous (eC i) := (contDiff_eC i).continuous

omit [NeZero n] in
lemma continuous_dC (i j : Fin n) : Continuous (dC i j) := (contDiff_dC i j).continuous

lemma continuous_cross (i j : Fin n) :
    Continuous fun q : Cfg n => cross (q i) (q (i + 1)) (q j) := by
  simp only [cross_eq]
  fun_prop

/-! ## The differentials, and the bridge to `FirstOrder.Data`

The linearisations of the squared constraints. Each is a positive multiple of
the corresponding differential of `FirstOrder.Data`, which is the whole content
of the "squared formulation is harmless" claim in the header. -/

/-- `D(eC i)[v, η] = 2⟪p_{i+1} − p_i, v_{i+1} − v_i⟫ − 2ℓη`. -/
def eD (p : Cfg n) (l : ℝ) (v : Cfg n) (eta : ℝ) (i : Fin n) : ℝ :=
  2 * ip (p (i + 1) - p i) (v (i + 1) - v i) - 2 * l * eta

omit [NeZero n] in
/-- `D(dC i j)[v] = 2⟪p_j − p_i, v_j − v_i⟫`. -/
def dD (p : Cfg n) (v : Cfg n) (i j : Fin n) : ℝ :=
  2 * ip (p j - p i) (v j - v i)

omit [NeZero n] in
lemma ip_smul_left (c : ℝ) (x y : ℝ × ℝ) : ip (c • x) y = c * ip x y := by
  simp [ip, Prod.smul_fst, Prod.smul_snd]; ring

variable {iota : Type*} [Fintype iota]

/-- The first-order data attached to a configuration: the paper's `sᵢ` and
`u_ij`, read off from `p` and `ℓ` rather than supplied abstractly. -/
noncomputable def dataOf (p : Cfg n) (l : ℝ) (a b : iota → Fin n) : Data n iota where
  s := fun i => l⁻¹ • (p (i + 1) - p i)
  u := fun e => p (b e) - p (a e)
  a := a
  b := b
  p := p

omit [Fintype iota] in
/-- The side differential of the squared constraint is `2ℓ` times the paper's. -/
lemma sideD_eq {p : Cfg n} {l : ℝ} (hl : l ≠ 0) (a b : iota → Fin n)
    (v : Cfg n) (eta : ℝ) (i : Fin n) :
    eD p l v eta i = 2 * l * (dataOf p l a b).sideD v eta i := by
  simp only [eD, Data.sideD, dataOf, ip_smul_left]
  field_simp

omit [Fintype iota] in
/-- The diameter differential of the squared constraint is `2` times the
paper's. -/
lemma diamD_eq (p : Cfg n) (l : ℝ) (a b : iota → Fin n) (v : Cfg n) (e : iota) :
    dD p v (a e) (b e) = 2 * (dataOf p l a b).diamD v e := by
  simp only [dD, Data.diamD, dataOf]

omit [Fintype iota] in
/-- **The linearised cone is the same set in either formulation.** This is what
licenses running the blow-up with the squared constraints and then handing the
limit direction to `FirstOrder.no_admissible_direction`, which is stated for the
paper's unsquared differentials. -/
theorem Keq_iff {p : Cfg n} {l : ℝ} (hl : 0 < l) (a b : iota → Fin n)
    (v : Cfg n) (eta : ℝ) :
    ((∀ i, eD p l v eta i = 0) ∧ (∀ e : iota, dD p v (a e) (b e) ≤ 0))
      ↔ (dataOf p l a b).Keq v eta := by
  constructor
  · rintro ⟨hs, hd⟩
    refine ⟨fun i => ?_, fun e => ?_⟩
    · have := hs i
      rw [sideD_eq hl.ne' a b] at this
      have h2 : (2 : ℝ) * l ≠ 0 := by positivity
      exact (mul_eq_zero.mp this).resolve_left h2
    · have := hd e
      rw [diamD_eq p l a b] at this
      linarith
  · rintro ⟨hs, hd⟩
    refine ⟨fun i => ?_, fun e => ?_⟩
    · rw [sideD_eq hl.ne' a b, hs i, mul_zero]
    · rw [diamD_eq p l a b]
      have := hd e
      linarith

end Chiquipoli.Feasible
