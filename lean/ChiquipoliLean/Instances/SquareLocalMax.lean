/-
**The square, closed: Proposition 4.2 as a Lean theorem.**

`Instances/SquareAndRhombus.lean` proves `square_no_admissible_direction`, which is Theorem 3.5's
contradiction step at the square. Until Theorem 3.5 itself was formalised that
was as far as it could go, and the paper's Proposition 4.2 — that the square is
a strict local maximiser — stayed outside the kernel.

It no longer needs to. `Feasible.eventually_congruent_of_no_worse` takes exactly
the data `Instances/SquareAndRhombus.lean` already supplies, so this file is the instantiation and
nothing more.

NORMALISATION. Unlike `A16`, the square carries no reparametrisation:
`squareData` is in the paper's own normalisation, with unit side vectors, unit
diameter vectors and `κ = 4`. So the scale factor is `1`, and `square_bridge`
is the statement that the differentials of the squared constraints are the
positive multiples `2ℓ` and `2` of the paper's — the same two factors as
everywhere else, and here they cancel against nothing.
-/
import ChiquipoliLean.Theory.FeasibleMain
import ChiquipoliLean.Instances.SquareAndRhombus

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder Filter Topology

/-! ## The square's side length -/

/-- The common side length of the unit-diameter square, `ℓ = 1/√2`. It coincides
with `sqH`, which `Instances/SquareAndRhombus.lean` introduces as the common coordinate of the two
diameter unit vectors; the two are the same number for the square, and are kept
apart here because they play different roles. -/
noncomputable def sqL : ℝ := 1 / Real.sqrt 2

lemma sqL_eq_sqH : sqL = sqH := rfl

lemma sqL_pos : 0 < sqL := by
  unfold sqL; positivity

lemma sqL_sq : sqL ^ 2 = 1 / 2 := by
  unfold sqL
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma sqA_sq : sqA ^ 2 = 1 / 8 := by
  unfold sqA
  rw [div_pow, one_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-! ## The bridge

The square is already in the paper's normalisation, so the scale factor is `1`.
-/

/-- `2a = ℓ`: the only arithmetic fact the square needs. Every coordinate
difference below is `±2a` in one component and `0` or `∓2a` in the other. -/
lemma two_sqA : 2 * sqA = sqL := by
  have h : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt2_pos
  unfold sqA sqL
  field_simp

/-- Each side vector of `squareData` really is the unit vector along that side:
`p_{i+1} − p_i = ℓ · s_i`. -/
lemma square_side_vec (i : Fin 4) :
    squareData.p (i + 1) - squareData.p i = sqL • squareData.s i := by
  have h2 := two_sqA
  fin_cases i
  · show ((-sqA : ℝ), (sqA : ℝ)) - (sqA, sqA) = sqL • ((-1 : ℝ), (0 : ℝ))
    simp only [Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> linarith
  · show ((-sqA : ℝ), (-sqA : ℝ)) - (-sqA, sqA) = sqL • ((0 : ℝ), (-1 : ℝ))
    simp only [Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> linarith
  · show ((sqA : ℝ), (-sqA : ℝ)) - (-sqA, -sqA) = sqL • ((1 : ℝ), (0 : ℝ))
    simp only [Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> linarith
  · show ((sqA : ℝ), (sqA : ℝ)) - (sqA, -sqA) = sqL • ((0 : ℝ), (1 : ℝ))
    simp only [Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> linarith

/-- Each diameter vector really is the difference of its endpoints; these are
unit vectors, so no scale factor appears. -/
lemma square_diam_vec (e : Fin 2) :
    squareData.p (squareData.b e) - squareData.p (squareData.a e) = squareData.u e := by
  have h2 := two_sqA
  have hH : sqL = sqH := sqL_eq_sqH
  fin_cases e
  · show ((-sqA : ℝ), (-sqA : ℝ)) - (sqA, sqA) = ((-sqH : ℝ), (-sqH : ℝ))
    simp only [Prod.mk_sub_mk, Prod.mk.injEq]
    constructor <;> (rw [← hH]; linarith)
  · show ((sqA : ℝ), (-sqA : ℝ)) - (-sqA, sqA) = ((sqH : ℝ), (-sqH : ℝ))
    simp only [Prod.mk_sub_mk, Prod.mk.injEq]
    constructor <;> (rw [← hH]; linarith)

theorem square_bridge (v : Cfg 4) (eta : ℝ)
    (hs : ∀ i, eD squareData.p sqL v eta i = 0)
    (hd : ∀ e, dD squareData.p v (squareData.a e) (squareData.b e) ≤ 0) :
    squareData.Keq v (1 * eta) := by
  rw [one_mul]
  refine ⟨fun i => ?_, fun e => ?_⟩
  · have h := hs i
    simp only [eD, square_side_vec, ip_smul_left] at h
    simp only [Data.sideD]
    nlinarith [h, sqL_pos]
  · have h := hd e
    simp only [dD, square_diam_vec] at h
    simp only [Data.diamD]
    linarith


/-! ## The square is feasible -/

lemma square_s_unit (i : Fin 4) : nsq (squareData.s i) = 1 := by
  fin_cases i <;> simp [nsq, ip, squareData]

lemma square_u_unit (e : Fin 2) : nsq (squareData.u e) = 1 := by
  have h : sqH ^ 2 = 1 / 2 := by rw [← sqL_eq_sqH]; exact sqL_sq
  fin_cases e <;> (simp [nsq, ip, squareData]; nlinarith [h])

/-- Every side has length `ℓ`. -/
theorem square_equilateral : Equilateral (squareData.p, sqL) := by
  intro i
  simp only [eC, square_side_vec, nsq_smul, square_s_unit, mul_one]
  rw [sqL_sq]; ring

/-- The two diagonals are active. -/
theorem square_active (e : Fin 2) :
    dC (squareData.a e) (squareData.b e) squareData.p = 0 := by
  simp only [dC, square_diam_vec, square_u_unit, sub_self]

/-- No pair of vertices is more than `1` apart. -/
theorem square_small : Small squareData.p := by
  intro i j
  have h := sqA_sq
  fin_cases i <;> fin_cases j <;> simp [dC, nsq, ip, squareData] <;> nlinarith [h]

/-- Strictly convex, in the labelled cyclic order. -/
theorem square_convexOrdered : ConvexOrdered squareData.p := by
  intro i j hji hjn
  have h := sqA_sq
  fin_cases i <;> fin_cases j <;> simp_all [cross_eq, squareData] <;> nlinarith [h]

theorem square_isFeasibleConvex : IsFeasibleConvex (squareData.p, sqL) :=
  ⟨square_convexOrdered, square_small, square_equilateral, sqL_pos⟩

/-- Two vertices are distinct — the nondegeneracy the slice consumes. -/
theorem square_vertices_distinct : squareData.p 0 ≠ squareData.p 2 := by
  intro hcon
  have h := sqA_pos
  have : (squareData.p 0).1 = (squareData.p 2).1 := by rw [hcon]
  simp only [squareData, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at this
  linarith

/-! ## Proposition 4.2, closed -/

/-- **The square is a strict local maximiser of the perimeter**, modulo
orientation-preserving Euclidean motions. This is Proposition 4.2 of the paper.

Every hypothesis comes from `Instances/SquareAndRhombus.lean`: the multiplier identity with
`κ = 4`, strict positivity of `λ₀₂ = λ₁₃ = √2`, and `I_eq ⊆ R_eq`. -/
theorem square_strict_local_max :
    IsFeasibleConvex (squareData.p, sqL) ∧
    ∀ᶠ y in 𝓝 ((squareData.p, sqL) : Amb 4),
      IsFeasible y → sqL ≤ y.2 → Congruent y.1 squareData.p ∧ y.2 = sqL := by
  refine ⟨square_isFeasibleConvex, ?_⟩
  refine eventually_congruent_of_no_worse (ii := 0) (jj := 2) sqL_pos
    square_vertices_distinct (D := squareData) rfl
    (a := squareData.a) (b := squareData.b) (sc := 1) one_pos
    square_bridge (by norm_num : (0:ℝ) < 4)
    square_multiplier_identity square_lam_pos square_Ieq_imp_R
    square_equilateral square_active

end Chiquipoli.Feasible
