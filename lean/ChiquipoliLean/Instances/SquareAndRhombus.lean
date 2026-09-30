/-
**Section 4's worked examples, kernel-checked.**

Two propositions the paper states about explicit small quadrilaterals:

  * the **square** is a strict local maximiser (Lemma "Square multiplier and
    rank data" + Proposition "Strict local maximality of the square");
  * the **rhombus** with vertices `(0,0), (1/2,-2/5), (1,0), (1/2,2/5)` is not
    (Proposition "Rhombus instability").

Both are instantiations of Section 3's machinery at explicit coordinates, so
both are formalised here in the paper's own normalisation — unit side and
diameter vectors, objective `L = 4ℓ`, hence `κ = 4` and `Σ αᵢ = −4`. Unlike the
`A16` layer there is no reparametrisation to explain: `√2` is carried directly.

`square_no_admissible_direction` below is Theorem 3.5's contradiction step at
the square, which used to be as far as it could go. It no longer is:
`Instances/SquareLocalMax.lean` feeds exactly this data to the formalised Theorem 3.5 and
obtains `square_strict_local_max`, the paper's Proposition 4.2. The rhombus was
always proved completely — its realising curve is explicit, so
`Instability.lean` applies with nothing left over.
-/
import ChiquipoliLean.Theory.FirstOrder
import ChiquipoliLean.Theory.Instability
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Chiquipoli.FirstOrder

open Finset

/-! ## The square -/

/-- Half-diagonal of the unit-diameter square: `a = 1/(2√2)`, so that the
diagonals `p₀p₂` and `p₁p₃` have length exactly `1`. -/
noncomputable def sqA : ℝ := 1 / (2 * Real.sqrt 2)

/-- `1/√2`, the common coordinate of the two diameter unit vectors. -/
noncomputable def sqH : ℝ := 1 / Real.sqrt 2

lemma sqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

lemma sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

lemma sqA_pos : 0 < sqA := by
  unfold sqA; positivity

/-- The paper's square: vertices `(±a, ±a)` in positive cyclic order, unit side
vectors, unit diameter vectors along the two diagonals, active edges `{0,2}` and
`{1,3}`. -/
noncomputable def squareData : Data 4 (Fin 2) where
  s := ![(-1, 0), (0, -1), (1, 0), (0, 1)]
  u := ![(-sqH, -sqH), (sqH, -sqH)]
  a := ![0, 1]
  b := ![2, 3]
  p := ![(sqA, sqA), (-sqA, sqA), (-sqA, -sqA), (sqA, -sqA)]


/-- Side multipliers of the square: `αᵢ = −1`, consistent with `Σ αᵢ = −4 = −κ`. -/
def squareAlpha : Fin 4 → ℝ := ![-1, -1, -1, -1]

/-- Active-diameter multipliers of the square: `λ₀₂ = λ₁₃ = √2 > 0`. -/
noncomputable def squareLam : Fin 2 → ℝ := ![Real.sqrt 2, Real.sqrt 2]

@[simp] lemma squareLam_0 : squareLam 0 = Real.sqrt 2 := rfl
@[simp] lemma squareLam_1 : squareLam 1 = Real.sqrt 2 := rfl

/-! Unfolding at literal indices, as in `Instances/A16FirstOrder.lean`. -/

@[simp] lemma sq_s_0 : squareData.s 0 = (-1, 0) := rfl
@[simp] lemma sq_s_1 : squareData.s 1 = (0, -1) := rfl
@[simp] lemma sq_s_2 : squareData.s 2 = (1, 0) := rfl
@[simp] lemma sq_s_3 : squareData.s 3 = (0, 1) := rfl
@[simp] lemma sq_u_0 : squareData.u 0 = (-sqH, -sqH) := rfl
@[simp] lemma sq_u_1 : squareData.u 1 = (sqH, -sqH) := rfl
@[simp] lemma sq_a_0 : squareData.a 0 = 0 := rfl
@[simp] lemma sq_a_1 : squareData.a 1 = 1 := rfl
@[simp] lemma sq_b_0 : squareData.b 0 = 2 := rfl
@[simp] lemma sq_b_1 : squareData.b 1 = 3 := rfl
@[simp] lemma sq_p_0 : squareData.p 0 = (sqA, sqA) := rfl
@[simp] lemma sq_p_1 : squareData.p 1 = (-sqA, sqA) := rfl
@[simp] lemma sq_p_2 : squareData.p 2 = (-sqA, -sqA) := rfl
@[simp] lemma sq_p_3 : squareData.p 3 = (sqA, -sqA) := rfl
@[simp] lemma sq_al_0 : squareAlpha 0 = -1 := rfl
@[simp] lemma sq_al_1 : squareAlpha 1 = -1 := rfl
@[simp] lemma sq_al_2 : squareAlpha 2 = -1 := rfl
@[simp] lemma sq_al_3 : squareAlpha 3 = -1 := rfl
@[simp] lemma fin4_succ_0 : ((0 : Fin 4) + 1) = 1 := rfl
@[simp] lemma fin4_succ_1 : ((1 : Fin 4) + 1) = 2 := rfl
@[simp] lemma fin4_succ_2 : ((2 : Fin 4) + 1) = 3 := rfl
@[simp] lemma fin4_succ_3 : ((3 : Fin 4) + 1) = 0 := rfl

lemma sqH_pos : 0 < sqH := by unfold sqH; positivity

/-- The only non-ring fact the square needs: `√2 · (1/√2) = 1`. -/
lemma sqrt2_mul_sqH : Real.sqrt 2 * sqH = 1 := by
  unfold sqH; field_simp

/-- **Both diameter multipliers are strictly positive.** -/
theorem square_lam_pos : ∀ e, 0 < squareLam e := by
  intro e; fin_cases e <;> simpa using sqrt2_pos

/-- **The square's multiplier identity** (paper: Lemma "Square multiplier and
rank data"), in the paper's normalisation `κ = n = 4`. -/
theorem square_multiplier_identity :
    squareData.MultiplierIdentity 4 squareAlpha squareLam := by
  intro v η
  simp only [Data.MultiplierIdentity, Data.sideD, Data.diamD, ip,
    Fin.sum_univ_four, Fin.sum_univ_two, Prod.fst_sub, Prod.snd_sub,
    sq_s_0, sq_s_1, sq_s_2, sq_s_3, sq_u_0, sq_u_1, sq_a_0, sq_a_1,
    sq_b_0, sq_b_1, sq_al_0, sq_al_1, sq_al_2, sq_al_3, squareLam_0,
    squareLam_1, fin4_succ_0, fin4_succ_1, fin4_succ_2, fin4_succ_3]
  linear_combination
    (((v 2).1 - (v 0).1) + ((v 2).2 - (v 0).2)
      - ((v 3).1 - (v 1).1) + ((v 3).2 - (v 1).2)) * sqrt2_mul_sqH

/-- **`I_eq ⊆ R_eq` at the square** (paper: the dimension count `9 − 6 = 3`).
Formalised directly as the inclusion, exactly as for `A16`: no `Matrix.rank`. -/
theorem square_Ieq_imp_R (w : Fin 4 → ℝ × ℝ) (h : squareData.Ieq w 0) :
    squareData.R w := by
  obtain ⟨hs, hd⟩ := h
  have h0 := hs 0; have h1 := hs 1; have h2 := hs 2; have h3 := hs 3
  have d0 := hd 0; have d1 := hd 1
  simp only [Data.sideD, Data.diamD, ip, Prod.fst_sub, Prod.snd_sub, sub_zero,
    sq_s_0, sq_s_1, sq_s_2, sq_s_3, sq_u_0, sq_u_1, sq_a_0, sq_a_1, sq_b_0,
    sq_b_1, fin4_succ_0, fin4_succ_1, fin4_succ_2, fin4_succ_3] at h0 h1 h2 h3 d0 d1
  have hsq : sqH ≠ 0 := ne_of_gt sqH_pos
  have ha : sqA ≠ 0 := ne_of_gt sqA_pos
  -- both diameter equations reduce to the same linear relation
  have e4 : ((w 2).1 - (w 0).1) + ((w 2).2 - (w 0).2) = 0 := by
    have hz : sqH * (((w 2).1 - (w 0).1) + ((w 2).2 - (w 0).2)) = 0 := by linarith
    rcases mul_eq_zero.mp hz with hx | hx
    · exact absurd hx hsq
    · exact hx
  obtain ⟨t1, ht1⟩ : ∃ x : ℝ, x = (w 0).1 + ((w 0).2 - (w 1).2) / 2 := ⟨_, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ x : ℝ, x = ((w 0).2 + (w 1).2) / 2 := ⟨_, rfl⟩
  obtain ⟨om, hom⟩ : ∃ x : ℝ, x = ((w 0).2 - (w 1).2) / (2 * sqA) := ⟨_, rfl⟩
  refine ⟨(t1, t2), om, fun i => ?_⟩
  fin_cases i
  · show w 0 = (t1, t2) + om • J ( sqA,  sqA)
    simp only [J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.ext_iff,
      ht1, ht2, hom]
    constructor <;> field_simp <;> linarith
  · show w 1 = (t1, t2) + om • J (-sqA,  sqA)
    simp only [J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.ext_iff,
      ht1, ht2, hom]
    constructor <;> field_simp <;> linarith
  · show w 2 = (t1, t2) + om • J (-sqA, -sqA)
    simp only [J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.ext_iff,
      ht1, ht2, hom]
    constructor <;> field_simp <;> linarith
  · show w 3 = (t1, t2) + om • J ( sqA, -sqA)
    simp only [J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.ext_iff,
      ht1, ht2, hom]
    constructor <;> field_simp <;> linarith

/-- **Theorem 3.5's contradiction step at the square.** There is no nonzero
admissible blow-up direction. Both hypotheses of the theorem are discharged
here: the multiplier identity with `λ = √2 > 0`, and `I_eq ⊆ R_eq`.

This is a step, not the conclusion. The paper's Proposition 4.2 --- that the
square is a strict local maximiser --- is `Feasible.square_strict_local_max`,
which feeds this same data to the formalised Theorem 3.5. -/
theorem square_no_admissible_direction
    (v : Fin 4 → ℝ × ℝ) (η : ℝ) (hK : squareData.Keq v η) (hη : 0 ≤ η)
    (hslice : ∀ r, squareData.R r → cip v r = 0) :
    v = 0 ∧ η = 0 :=
  no_admissible_direction (by norm_num) square_multiplier_identity
    square_lam_pos square_Ieq_imp_R hK hη hslice


/-! ## The nonoptimal rhombus

`p₀ = (0,0)`, `p₁ = (1/2, −2/5)`, `p₂ = (1,0)`, `p₃ = (1/2, 2/5)`
(labelled counterclockwise), with
`ℓ = √41/10` and the single active diameter `{0,2}`.

This one is proved **outright** without needing Theorem 3.5: the realising curve
is explicit, so nothing analytic is left assumed. -/

/-- Squared Euclidean distance. -/
def sqdist (a b : ℝ × ℝ) : ℝ := (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2

/-- The paper's deformation: `p₁` and `p₃` move apart vertically at rate `δ`,
`p₀` and `p₂` stay put. The half-height at time `t` is `2/5 + tδ`. -/
noncomputable def rhoP (δ t : ℝ) : Fin 4 → ℝ × ℝ :=
  ![(0, 0), (1/2, -(2/5 + t*δ)), (1, 0), (1/2, 2/5 + t*δ)]

/-- The perimeter along that curve, `L(t) = 4ℓ(t)`. -/
noncomputable def rhoL (δ t : ℝ) : ℝ := 4 * Real.sqrt (1/4 + (2/5 + t*δ)^2)

@[simp] lemma rhoP_0 (δ t : ℝ) : rhoP δ t 0 = (0, 0) := rfl
@[simp] lemma rhoP_1 (δ t : ℝ) : rhoP δ t 1 = (1/2, -(2/5 + t*δ)) := rfl
@[simp] lemma rhoP_2 (δ t : ℝ) : rhoP δ t 2 = (1, 0) := rfl
@[simp] lemma rhoP_3 (δ t : ℝ) : rhoP δ t 3 = (1/2, 2/5 + t*δ) := rfl

/-- The four vertices, enumerated without touching `Fin` index arithmetic. -/
lemma rhoP_cases (δ t : ℝ) (i : Fin 4) :
    rhoP δ t i = (0, 0) ∨ rhoP δ t i = (1/2, -(2/5 + t*δ)) ∨
    rhoP δ t i = (1, 0) ∨ rhoP δ t i = (1/2, 2/5 + t*δ) := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- **The deformation stays equilateral**: every side has the same squared
length at every time. This is what makes the curve *feasible*, and it is why the
instability conclusion is about the constrained problem rather than about a bare
function. -/
theorem rho_equilateral (δ t : ℝ) (i : Fin 4) :
    sqdist (rhoP δ t i) (rhoP δ t (i + 1)) = 1/4 + (2/5 + t*δ)^2 := by
  fin_cases i
  · show sqdist (rhoP δ t 0) (rhoP δ t 1) = _
    simp only [rhoP_0, rhoP_1, sqdist]; ring
  · show sqdist (rhoP δ t 1) (rhoP δ t 2) = _
    simp only [rhoP_1, rhoP_2, sqdist]; ring
  · show sqdist (rhoP δ t 2) (rhoP δ t 3) = _
    simp only [rhoP_2, rhoP_3, sqdist]; ring
  · show sqdist (rhoP δ t 3) (rhoP δ t 0) = _
    simp only [rhoP_3, rhoP_0, sqdist]; ring

/-- **The deformation stays a small polygon** while the half-height is between
`0` and `1/2`: no pair of vertices is farther apart than `1`. At `t = 0` the
half-height is `2/5`, so this holds on a neighbourhood of `0`. -/
theorem rho_small (δ t : ℝ) (h0 : 0 ≤ 2/5 + t*δ) (h1 : 2/5 + t*δ ≤ 1/2)
    (i j : Fin 4) : sqdist (rhoP δ t i) (rhoP δ t j) ≤ 1 := by
  rcases rhoP_cases δ t i with h|h|h|h <;> rcases rhoP_cases δ t j with k|k|k|k <;>
    rw [h, k] <;> simp only [sqdist] <;> nlinarith [sq_nonneg (2/5 + t*δ)]

/-- The active diameter `{0,2}` is at distance exactly `1` at every time: the
deformation preserves it, which is why `{0,2}` stays the active graph. -/
theorem rho_diameter (δ t : ℝ) : sqdist (rhoP δ t 0) (rhoP δ t 2) = 1 := by
  simp only [rhoP_0, rhoP_2, sqdist]; norm_num

lemma sqrt41_pos : (0:ℝ) < Real.sqrt 41 := Real.sqrt_pos.mpr (by norm_num)

lemma sqrt41_hundredth : Real.sqrt (41/100) = Real.sqrt 41 / 10 := by
  rw [show (41:ℝ)/100 = 41 * (1/10)^2 by norm_num,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 41),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/10)]
  ring

/-- **The first variation of the perimeter along the curve is `16δ/√41`.**
The paper computes `DL[v,η] = 4η` with `η = 2δ/(5ℓ)` and `ℓ = √41/10`; that is
the same number. -/
theorem rho_hasDerivAt (δ : ℝ) :
    HasDerivAt (rhoL δ) (16 * δ / Real.sqrt 41) 0 := by
  have hin : HasDerivAt (fun t : ℝ => 2/5 + t*δ) δ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const δ).const_add (2/5 : ℝ)
  have hg : HasDerivAt (fun t : ℝ => 1/4 + (2/5 + t*δ)^2) (4*δ/5) 0 :=
    ((hin.pow 2).const_add (1/4 : ℝ)).congr_deriv
      (by first | (norm_num; ring) | norm_num | ring)
  have hne : (fun t : ℝ => 1/4 + (2/5 + t*δ)^2) 0 ≠ 0 := by norm_num
  have h41 : Real.sqrt 41 ≠ 0 := ne_of_gt sqrt41_pos
  exact ((hg.sqrt hne).const_mul (4:ℝ)).congr_deriv
    (by norm_num [sqrt41_hundredth]
        first | (field_simp; ring) | field_simp | ring)

/-- **Proposition (rhombus instability), in full.** With `δ > 0` the perimeter
along the feasible deformation is strictly larger at every sufficiently small
positive time, so the rhombus is not a local maximiser. Nothing here is assumed:
`rho_equilateral`, `rho_small` and `rho_diameter` establish that the curve stays
feasible, and `rho_hasDerivAt` that the perimeter strictly increases. -/
theorem rhombus_perimeter_increases (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), rhoL δ 0 < rhoL δ t :=
  increases_to_the_right (rho_hasDerivAt δ) (by positivity)

/-- The same, in Mathlib's vocabulary. -/
theorem rhombus_not_isLocalMax (δ : ℝ) (hδ : 0 < δ) : ¬ IsLocalMax (rhoL δ) 0 :=
  not_isLocalMax (rho_hasDerivAt δ) (by positivity)

end Chiquipoli.FirstOrder
