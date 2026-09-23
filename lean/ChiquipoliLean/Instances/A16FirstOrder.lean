/-
**Theorem 3.5's algebraic core, instantiated at the certified `A16`.**

`ChiquipoliLean/Theory/FirstOrder.lean` proves the algebraic half of Theorem 3.5 from
two hypotheses. This file discharges both of them at `A16`, from theorems
already in this development, so that nothing is assumed:

  * hypothesis (i), the multiplier identity with strictly positive
    active-diameter multipliers, comes from `gradx_*` / `grady_*` (the weighted
    gradient sum vanishes at every vertex), `alpha_sum` (`Σ αᵢ = −1`), and
    `mL*_pos` (each of the fifteen diameter multipliers clears `1/1000` on the
    certified bracket);

  * hypothesis (ii), `I_eq ⊆ R_eq`, comes from `kernel_is_rigid`.

The conclusion, `A16_no_admissible_direction`, is the contradiction step of the
paper's proof: at the certified configuration there is no nonzero admissible
blow-up direction. What is assumed of the direction here — `η ≥ 0` and
`v ⊥ R(p)` — is supplied by the analytic half of the paper's argument, which is
formalised in `Feasible*.lean`; `Feasible.A16_locally_maximal` joins the two and
closes the chain. See `lean/README.md`.

FORMULATION. The package's multiplier witness lives in the squared formulation:
the scalar variable is `t = ℓ²`, the objective is `t`, and every constraint
gradient is `2(p_j − p_i)` with no division by `ℓ`. So the side and diameter
vectors below are `2(p_{i+1} − p_i)` and `2(p_j − p_i)` rather than unit
vectors, and the objective coefficient is `κ = 1`. `Data` does not require
normalised vectors, and rescaling a constraint by a positive factor rescales its
multiplier by the reciprocal, so strict positivity — the only thing the theorem
uses — is unaffected. `Σ αᵢ = −1` rather than `−16` is the same statement read
in this normalisation.
-/
import ChiquipoliLean.Theory.FirstOrder
import ChiquipoliLean.Generated.Rank

namespace Chiquipoli.FirstOrder

open Finset

/-- `2(b − a)`: the gradient of `|b − a|²` in the squared formulation, up to the
displacement it is paired with. -/
def twice (a b : ℝ × ℝ) : ℝ × ℝ := (2 * (b.1 - a.1), 2 * (b.2 - a.2))

/-- The bridge to the development's existing differential: pairing `twice a b`
with a relative displacement is exactly `dsq`. -/
lemma ip_twice (a b u u' : ℝ × ℝ) : ip (twice a b) (u' - u) = dsq a b u u' := by
  simp only [ip, twice, dsq, Prod.fst_sub, Prod.snd_sub]; ring

/-- The sixteen vertices as a single indexed family. -/
noncomputable def A16p (z : ℝ) : Fin 16 → ℝ × ℝ :=
  ![p0 z, p1 z, p2 z, p3 z, p4 z, p5 z, p6 z, p7 z,
    p8 z, p9 z, p10 z, p11 z, p12 z, p13 z, p14 z, p15 z]

/-- Side vectors, in the squared normalisation. -/
noncomputable def A16s (z : ℝ) : Fin 16 → ℝ × ℝ :=
  ![twice (p0 z) (p1 z), twice (p1 z) (p2 z), twice (p2 z) (p3 z),
    twice (p3 z) (p4 z), twice (p4 z) (p5 z), twice (p5 z) (p6 z),
    twice (p6 z) (p7 z), twice (p7 z) (p8 z), twice (p8 z) (p9 z),
    twice (p9 z) (p10 z), twice (p10 z) (p11 z), twice (p11 z) (p12 z),
    twice (p12 z) (p13 z), twice (p13 z) (p14 z), twice (p14 z) (p15 z),
    twice (p15 z) (p0 z)]

/-- The fifteen active diameters, in the order fixed by `ACTIVE_EDGES`:
`(0,7) (0,8) (0,9) (1,9) (2,9) (2,10) (3,10) (3,11) (3,12) (4,13) (5,13)
(6,13) (6,14) (7,14) (7,15)`. -/
noncomputable def A16u (z : ℝ) : Fin 15 → ℝ × ℝ :=
  ![twice (p0 z) (p7 z), twice (p0 z) (p8 z), twice (p0 z) (p9 z),
    twice (p1 z) (p9 z), twice (p2 z) (p9 z), twice (p2 z) (p10 z),
    twice (p3 z) (p10 z), twice (p3 z) (p11 z), twice (p3 z) (p12 z),
    twice (p4 z) (p13 z), twice (p5 z) (p13 z), twice (p6 z) (p13 z),
    twice (p6 z) (p14 z), twice (p7 z) (p14 z), twice (p7 z) (p15 z)]

/-- First endpoints of the active diameters. -/
def A16a : Fin 15 → Fin 16 := ![0, 0, 0, 1, 2, 2, 3, 3, 3, 4, 5, 6, 6, 7, 7]

/-- Second endpoints of the active diameters. -/
def A16b : Fin 15 → Fin 16 := ![7, 8, 9, 9, 9, 10, 10, 11, 12, 13, 13, 13, 14, 14, 15]

/-- The first-order data at the `A16` configuration. -/
noncomputable def A16Data (z : ℝ) : Data 16 (Fin 15) :=
  { s := A16s z, u := A16u z, a := A16a, b := A16b, p := A16p z }

/-- The side multipliers, as computed and certified in `Multipliers.lean`. -/
noncomputable def A16alpha (c : ℝ) : Fin 16 → ℝ :=
  ![mA0 c, mA1 c, mA2 c, mA3 c, mA4 c, mA5 c, mA6 c, mA7 c,
    mA8 c, mA9 c, mA10 c, mA11 c, mA12 c, mA13 c, mA14 c, mA15 c]

/-- The active-diameter multipliers, as computed and certified in
`Multipliers.lean`. -/
noncomputable def A16lam (c : ℝ) : Fin 15 → ℝ :=
  ![mL0 c, mL1 c, mL2 c, mL3 c, mL4 c, mL5 c, mL6 c, mL7 c,
    mL8 c, mL9 c, mL10 c, mL11 c, mL12 c, mL13 c, mL14 c]

/-! ### Unfolding at literal indices

`![…] k` for a numeral `k` is definitionally the `k`-th entry, but `ring` treats
the unreduced application as an atom distinct from that entry. These `rfl`
lemmas do the reduction explicitly, so no `Matrix` simproc has to fire inside
the large `linear_combination` below. -/

@[simp] lemma A16s_0 (z : ℝ) : A16s z 0 = twice (p0 z) (p1 z) := rfl
@[simp] lemma A16s_1 (z : ℝ) : A16s z 1 = twice (p1 z) (p2 z) := rfl
@[simp] lemma A16s_2 (z : ℝ) : A16s z 2 = twice (p2 z) (p3 z) := rfl
@[simp] lemma A16s_3 (z : ℝ) : A16s z 3 = twice (p3 z) (p4 z) := rfl
@[simp] lemma A16s_4 (z : ℝ) : A16s z 4 = twice (p4 z) (p5 z) := rfl
@[simp] lemma A16s_5 (z : ℝ) : A16s z 5 = twice (p5 z) (p6 z) := rfl
@[simp] lemma A16s_6 (z : ℝ) : A16s z 6 = twice (p6 z) (p7 z) := rfl
@[simp] lemma A16s_7 (z : ℝ) : A16s z 7 = twice (p7 z) (p8 z) := rfl
@[simp] lemma A16s_8 (z : ℝ) : A16s z 8 = twice (p8 z) (p9 z) := rfl
@[simp] lemma A16s_9 (z : ℝ) : A16s z 9 = twice (p9 z) (p10 z) := rfl
@[simp] lemma A16s_10 (z : ℝ) : A16s z 10 = twice (p10 z) (p11 z) := rfl
@[simp] lemma A16s_11 (z : ℝ) : A16s z 11 = twice (p11 z) (p12 z) := rfl
@[simp] lemma A16s_12 (z : ℝ) : A16s z 12 = twice (p12 z) (p13 z) := rfl
@[simp] lemma A16s_13 (z : ℝ) : A16s z 13 = twice (p13 z) (p14 z) := rfl
@[simp] lemma A16s_14 (z : ℝ) : A16s z 14 = twice (p14 z) (p15 z) := rfl
@[simp] lemma A16s_15 (z : ℝ) : A16s z 15 = twice (p15 z) (p0 z) := rfl
@[simp] lemma A16alpha_0 (c : ℝ) : A16alpha c 0 = mA0 c := rfl
@[simp] lemma A16alpha_1 (c : ℝ) : A16alpha c 1 = mA1 c := rfl
@[simp] lemma A16alpha_2 (c : ℝ) : A16alpha c 2 = mA2 c := rfl
@[simp] lemma A16alpha_3 (c : ℝ) : A16alpha c 3 = mA3 c := rfl
@[simp] lemma A16alpha_4 (c : ℝ) : A16alpha c 4 = mA4 c := rfl
@[simp] lemma A16alpha_5 (c : ℝ) : A16alpha c 5 = mA5 c := rfl
@[simp] lemma A16alpha_6 (c : ℝ) : A16alpha c 6 = mA6 c := rfl
@[simp] lemma A16alpha_7 (c : ℝ) : A16alpha c 7 = mA7 c := rfl
@[simp] lemma A16alpha_8 (c : ℝ) : A16alpha c 8 = mA8 c := rfl
@[simp] lemma A16alpha_9 (c : ℝ) : A16alpha c 9 = mA9 c := rfl
@[simp] lemma A16alpha_10 (c : ℝ) : A16alpha c 10 = mA10 c := rfl
@[simp] lemma A16alpha_11 (c : ℝ) : A16alpha c 11 = mA11 c := rfl
@[simp] lemma A16alpha_12 (c : ℝ) : A16alpha c 12 = mA12 c := rfl
@[simp] lemma A16alpha_13 (c : ℝ) : A16alpha c 13 = mA13 c := rfl
@[simp] lemma A16alpha_14 (c : ℝ) : A16alpha c 14 = mA14 c := rfl
@[simp] lemma A16alpha_15 (c : ℝ) : A16alpha c 15 = mA15 c := rfl
@[simp] lemma A16u_0 (z : ℝ) : A16u z 0 = twice (p0 z) (p7 z) := rfl
@[simp] lemma A16a_0 : A16a 0 = 0 := rfl
@[simp] lemma A16b_0 : A16b 0 = 7 := rfl
@[simp] lemma A16lam_0 (c : ℝ) : A16lam c 0 = mL0 c := rfl
@[simp] lemma A16u_1 (z : ℝ) : A16u z 1 = twice (p0 z) (p8 z) := rfl
@[simp] lemma A16a_1 : A16a 1 = 0 := rfl
@[simp] lemma A16b_1 : A16b 1 = 8 := rfl
@[simp] lemma A16lam_1 (c : ℝ) : A16lam c 1 = mL1 c := rfl
@[simp] lemma A16u_2 (z : ℝ) : A16u z 2 = twice (p0 z) (p9 z) := rfl
@[simp] lemma A16a_2 : A16a 2 = 0 := rfl
@[simp] lemma A16b_2 : A16b 2 = 9 := rfl
@[simp] lemma A16lam_2 (c : ℝ) : A16lam c 2 = mL2 c := rfl
@[simp] lemma A16u_3 (z : ℝ) : A16u z 3 = twice (p1 z) (p9 z) := rfl
@[simp] lemma A16a_3 : A16a 3 = 1 := rfl
@[simp] lemma A16b_3 : A16b 3 = 9 := rfl
@[simp] lemma A16lam_3 (c : ℝ) : A16lam c 3 = mL3 c := rfl
@[simp] lemma A16u_4 (z : ℝ) : A16u z 4 = twice (p2 z) (p9 z) := rfl
@[simp] lemma A16a_4 : A16a 4 = 2 := rfl
@[simp] lemma A16b_4 : A16b 4 = 9 := rfl
@[simp] lemma A16lam_4 (c : ℝ) : A16lam c 4 = mL4 c := rfl
@[simp] lemma A16u_5 (z : ℝ) : A16u z 5 = twice (p2 z) (p10 z) := rfl
@[simp] lemma A16a_5 : A16a 5 = 2 := rfl
@[simp] lemma A16b_5 : A16b 5 = 10 := rfl
@[simp] lemma A16lam_5 (c : ℝ) : A16lam c 5 = mL5 c := rfl
@[simp] lemma A16u_6 (z : ℝ) : A16u z 6 = twice (p3 z) (p10 z) := rfl
@[simp] lemma A16a_6 : A16a 6 = 3 := rfl
@[simp] lemma A16b_6 : A16b 6 = 10 := rfl
@[simp] lemma A16lam_6 (c : ℝ) : A16lam c 6 = mL6 c := rfl
@[simp] lemma A16u_7 (z : ℝ) : A16u z 7 = twice (p3 z) (p11 z) := rfl
@[simp] lemma A16a_7 : A16a 7 = 3 := rfl
@[simp] lemma A16b_7 : A16b 7 = 11 := rfl
@[simp] lemma A16lam_7 (c : ℝ) : A16lam c 7 = mL7 c := rfl
@[simp] lemma A16u_8 (z : ℝ) : A16u z 8 = twice (p3 z) (p12 z) := rfl
@[simp] lemma A16a_8 : A16a 8 = 3 := rfl
@[simp] lemma A16b_8 : A16b 8 = 12 := rfl
@[simp] lemma A16lam_8 (c : ℝ) : A16lam c 8 = mL8 c := rfl
@[simp] lemma A16u_9 (z : ℝ) : A16u z 9 = twice (p4 z) (p13 z) := rfl
@[simp] lemma A16a_9 : A16a 9 = 4 := rfl
@[simp] lemma A16b_9 : A16b 9 = 13 := rfl
@[simp] lemma A16lam_9 (c : ℝ) : A16lam c 9 = mL9 c := rfl
@[simp] lemma A16u_10 (z : ℝ) : A16u z 10 = twice (p5 z) (p13 z) := rfl
@[simp] lemma A16a_10 : A16a 10 = 5 := rfl
@[simp] lemma A16b_10 : A16b 10 = 13 := rfl
@[simp] lemma A16lam_10 (c : ℝ) : A16lam c 10 = mL10 c := rfl
@[simp] lemma A16u_11 (z : ℝ) : A16u z 11 = twice (p6 z) (p13 z) := rfl
@[simp] lemma A16a_11 : A16a 11 = 6 := rfl
@[simp] lemma A16b_11 : A16b 11 = 13 := rfl
@[simp] lemma A16lam_11 (c : ℝ) : A16lam c 11 = mL11 c := rfl
@[simp] lemma A16u_12 (z : ℝ) : A16u z 12 = twice (p6 z) (p14 z) := rfl
@[simp] lemma A16a_12 : A16a 12 = 6 := rfl
@[simp] lemma A16b_12 : A16b 12 = 14 := rfl
@[simp] lemma A16lam_12 (c : ℝ) : A16lam c 12 = mL12 c := rfl
@[simp] lemma A16u_13 (z : ℝ) : A16u z 13 = twice (p7 z) (p14 z) := rfl
@[simp] lemma A16a_13 : A16a 13 = 7 := rfl
@[simp] lemma A16b_13 : A16b 13 = 14 := rfl
@[simp] lemma A16lam_13 (c : ℝ) : A16lam c 13 = mL13 c := rfl
@[simp] lemma A16u_14 (z : ℝ) : A16u z 14 = twice (p7 z) (p15 z) := rfl
@[simp] lemma A16a_14 : A16a 14 = 7 := rfl
@[simp] lemma A16b_14 : A16b 14 = 15 := rfl
@[simp] lemma A16lam_14 (c : ℝ) : A16lam c 14 = mL14 c := rfl

/-- Cyclic successor at literal indices, for the same reason. -/
@[simp] lemma A16succ_0 : (((0 : Fin 16)) + 1) = 1 := rfl
@[simp] lemma A16succ_1 : (((1 : Fin 16)) + 1) = 2 := rfl
@[simp] lemma A16succ_2 : (((2 : Fin 16)) + 1) = 3 := rfl
@[simp] lemma A16succ_3 : (((3 : Fin 16)) + 1) = 4 := rfl
@[simp] lemma A16succ_4 : (((4 : Fin 16)) + 1) = 5 := rfl
@[simp] lemma A16succ_5 : (((5 : Fin 16)) + 1) = 6 := rfl
@[simp] lemma A16succ_6 : (((6 : Fin 16)) + 1) = 7 := rfl
@[simp] lemma A16succ_7 : (((7 : Fin 16)) + 1) = 8 := rfl
@[simp] lemma A16succ_8 : (((8 : Fin 16)) + 1) = 9 := rfl
@[simp] lemma A16succ_9 : (((9 : Fin 16)) + 1) = 10 := rfl
@[simp] lemma A16succ_10 : (((10 : Fin 16)) + 1) = 11 := rfl
@[simp] lemma A16succ_11 : (((11 : Fin 16)) + 1) = 12 := rfl
@[simp] lemma A16succ_12 : (((12 : Fin 16)) + 1) = 13 := rfl
@[simp] lemma A16succ_13 : (((13 : Fin 16)) + 1) = 14 := rfl
@[simp] lemma A16succ_14 : (((14 : Fin 16)) + 1) = 15 := rfl
@[simp] lemma A16succ_15 : (((15 : Fin 16)) + 1) = 0 := rfl

/-- **Hypothesis (i), positivity half.** Every active-diameter multiplier is
strictly positive on the certified bracket — each clears `1/1000` by a Bernstein
certificate. -/
theorem A16_lam_pos (z : ℝ) (hcb : Real.cos z ∈ Set.Ioo clo chi) :
    ∀ e, 0 < A16lam (Real.cos z) e := by
  obtain ⟨h1, h2⟩ := hcb
  have hlo : clo ≤ Real.cos z := le_of_lt h1
  have hhi : Real.cos z ≤ chi := le_of_lt h2
  intro e
  fin_cases e
  · show (0:ℝ) < mL0 (Real.cos z)
    linarith [mL0_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL1 (Real.cos z)
    linarith [mL1_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL2 (Real.cos z)
    linarith [mL2_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL3 (Real.cos z)
    linarith [mL3_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL4 (Real.cos z)
    linarith [mL4_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL5 (Real.cos z)
    linarith [mL5_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL6 (Real.cos z)
    linarith [mL6_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL7 (Real.cos z)
    linarith [mL7_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL8 (Real.cos z)
    linarith [mL8_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL9 (Real.cos z)
    linarith [mL9_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL10 (Real.cos z)
    linarith [mL10_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL11 (Real.cos z)
    linarith [mL11_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL12 (Real.cos z)
    linarith [mL12_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL13 (Real.cos z)
    linarith [mL13_pos (Real.cos z) hlo hhi]
  · show (0:ℝ) < mL14 (Real.cos z)
    linarith [mL14_pos (Real.cos z) hlo hhi]

/-- **The kernel of the active equality Jacobian**, at general `dt`. A
displacement annihilated by every active constraint differential forces `dt = 0`
and is an infinitesimal rigid motion. This is `kernel_is_rigid`, restated in the
language of `Data`; `A16_Ieq_imp_R` below is the `dt = 0` case, which is what
hypothesis (ii) of Theorem 3.5 needs, and `Instances/A16Rank30.lean` uses the general form.

Only fourteen of the fifteen diameter equalities are consumed — the active
Jacobian has rank 30, not 31, so one constraint is redundant. Supplying all
fifteen and using fourteen is sound; it is LICQ failing, which is exactly the
situation Theorem 3.5 is built to tolerate. -/
theorem A16_kernel (z : ℝ) (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (w : Fin 16 → ℝ × ℝ) (dt : ℝ)
    (hside : ∀ i, (A16Data z).sideD w dt i = 0)
    (hdiam : ∀ e, (A16Data z).diamD w e = 0) :
    dt = 0 ∧ (A16Data z).R w := by
  have hs0 : dsq (p0 z) (p1 z) (w 0) (w 1) = dt := by
    have hx := hside 0
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs1 : dsq (p1 z) (p2 z) (w 1) (w 2) = dt := by
    have hx := hside 1
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs2 : dsq (p2 z) (p3 z) (w 2) (w 3) = dt := by
    have hx := hside 2
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs3 : dsq (p3 z) (p4 z) (w 3) (w 4) = dt := by
    have hx := hside 3
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs4 : dsq (p4 z) (p5 z) (w 4) (w 5) = dt := by
    have hx := hside 4
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs5 : dsq (p5 z) (p6 z) (w 5) (w 6) = dt := by
    have hx := hside 5
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs6 : dsq (p6 z) (p7 z) (w 6) (w 7) = dt := by
    have hx := hside 6
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs7 : dsq (p7 z) (p8 z) (w 7) (w 8) = dt := by
    have hx := hside 7
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs8 : dsq (p8 z) (p9 z) (w 8) (w 9) = dt := by
    have hx := hside 8
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs9 : dsq (p9 z) (p10 z) (w 9) (w 10) = dt := by
    have hx := hside 9
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs10 : dsq (p10 z) (p11 z) (w 10) (w 11) = dt := by
    have hx := hside 10
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs11 : dsq (p11 z) (p12 z) (w 11) (w 12) = dt := by
    have hx := hside 11
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs12 : dsq (p12 z) (p13 z) (w 12) (w 13) = dt := by
    have hx := hside 12
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs13 : dsq (p13 z) (p14 z) (w 13) (w 14) = dt := by
    have hx := hside 13
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs14 : dsq (p14 z) (p15 z) (w 14) (w 15) = dt := by
    have hx := hside 14
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hs15 : dsq (p15 z) (p0 z) (w 15) (w 0) = dt := by
    have hx := hside 15
    simpa [A16Data, Data.sideD, A16s, ip_twice, sub_eq_zero] using hx
  have hd0 : dsq (p0 z) (p7 z) (w 0) (w 7) = 0 := by
    have hx := hdiam 0
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd1 : dsq (p0 z) (p8 z) (w 0) (w 8) = 0 := by
    have hx := hdiam 1
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd2 : dsq (p0 z) (p9 z) (w 0) (w 9) = 0 := by
    have hx := hdiam 2
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd3 : dsq (p1 z) (p9 z) (w 1) (w 9) = 0 := by
    have hx := hdiam 3
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd4 : dsq (p2 z) (p9 z) (w 2) (w 9) = 0 := by
    have hx := hdiam 4
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd5 : dsq (p2 z) (p10 z) (w 2) (w 10) = 0 := by
    have hx := hdiam 5
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd6 : dsq (p3 z) (p10 z) (w 3) (w 10) = 0 := by
    have hx := hdiam 6
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd7 : dsq (p3 z) (p11 z) (w 3) (w 11) = 0 := by
    have hx := hdiam 7
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd8 : dsq (p3 z) (p12 z) (w 3) (w 12) = 0 := by
    have hx := hdiam 8
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd9 : dsq (p4 z) (p13 z) (w 4) (w 13) = 0 := by
    have hx := hdiam 9
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd10 : dsq (p5 z) (p13 z) (w 5) (w 13) = 0 := by
    have hx := hdiam 10
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd11 : dsq (p6 z) (p13 z) (w 6) (w 13) = 0 := by
    have hx := hdiam 11
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd12 : dsq (p6 z) (p14 z) (w 6) (w 14) = 0 := by
    have hx := hdiam 12
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  have hd13 : dsq (p7 z) (p14 z) (w 7) (w 14) = 0 := by
    have hx := hdiam 13
    simpa [A16Data, Data.diamD, A16u, A16a, A16b, ip_twice] using hx
  obtain ⟨hdt, a, b, e, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14, hw15⟩ :=
    kernel_is_rigid z hF hsz hcb w dt hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11 hd12 hd13
  refine ⟨hdt, (a, b), e, fun i => ?_⟩
  fin_cases i
  · show w 0 = (a, b) + e • J (p0 z)
    rw [hw0]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 1 = (a, b) + e • J (p1 z)
    rw [hw1]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 2 = (a, b) + e • J (p2 z)
    rw [hw2]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 3 = (a, b) + e • J (p3 z)
    rw [hw3]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 4 = (a, b) + e • J (p4 z)
    rw [hw4]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 5 = (a, b) + e • J (p5 z)
    rw [hw5]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 6 = (a, b) + e • J (p6 z)
    rw [hw6]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 7 = (a, b) + e • J (p7 z)
    rw [hw7]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 8 = (a, b) + e • J (p8 z)
    rw [hw8]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 9 = (a, b) + e • J (p9 z)
    rw [hw9]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 10 = (a, b) + e • J (p10 z)
    rw [hw10]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 11 = (a, b) + e • J (p11 z)
    rw [hw11]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 12 = (a, b) + e • J (p12 z)
    rw [hw12]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 13 = (a, b) + e • J (p13 z)
    rw [hw13]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 14 = (a, b) + e • J (p14 z)
    rw [hw14]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial
  · show w 15 = (a, b) + e • J (p15 z)
    rw [hw15]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> first | ring | trivial

/-- **Hypothesis (ii).** `I_eq ⊆ R_eq` at the certified configuration: the
`dt = 0` case of `A16_kernel`. -/
theorem A16_Ieq_imp_R (z : ℝ) (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (w : Fin 16 → ℝ × ℝ) (h : (A16Data z).Ieq w 0) : (A16Data z).R w :=
  (A16_kernel z hF hsz hcb w 0 h.1 h.2).2


/-- Expansion of a sum over `Fin 16` into literal indices. Expanding with
`Fin.sum_univ_succ` alone leaves the indices as `Fin.succ` chains, which `ring`
then treats as atoms distinct from the numerals the gradient theorems use. -/
lemma sum16 (f : Fin 16 → ℝ) : ∑ i, f i = f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7+f 8+f 9+f 10+f 11+f 12+f 13+f 14+f 15 := by
  simp [Fin.sum_univ_succ]; ring

/-- Expansion of a sum over `Fin 15` into literal indices. -/
lemma sum15 (g : Fin 15 → ℝ) : ∑ e, g e = g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7+g 8+g 9+g 10+g 11+g 12+g 13+g 14 := by
  simp [Fin.sum_univ_succ]; ring

set_option maxRecDepth 8000 in
/-- **Hypothesis (i).** The multiplier identity holds at the certified
configuration, with the side multipliers `mA*` and active-diameter multipliers
`mL*` computed in `Multipliers.lean`.

The objective coefficient is `κ = 1`: in the squared formulation the objective is
`t = ℓ²` itself. The proof is the regrouping of the 31 constraint differentials
by vertex — the coefficient of `v_k` is exactly twice the corresponding
`gradx_k` / `grady_k` expression, which those theorems prove to vanish —
together with `alpha_sum` for the `η` coefficient. -/
theorem A16_multiplier_identity (z : ℝ) (hF : Ffun z = 0) :
    (A16Data z).MultiplierIdentity 1 (A16alpha (Real.cos z)) (A16lam (Real.cos z)) := by
  intro v η
  rw [sum16, sum15]
  simp only [A16Data, Data.sideD, Data.diamD, twice, ip, Prod.fst_sub, Prod.snd_sub, A16s_0,
    A16s_1, A16s_2, A16s_3, A16s_4, A16s_5, A16s_6, A16s_7, A16s_8, A16s_9, A16s_10, A16s_11,
    A16s_12, A16s_13, A16s_14, A16s_15, A16alpha_0, A16alpha_1, A16alpha_2, A16alpha_3,
    A16alpha_4, A16alpha_5, A16alpha_6, A16alpha_7, A16alpha_8, A16alpha_9, A16alpha_10,
    A16alpha_11, A16alpha_12, A16alpha_13, A16alpha_14, A16alpha_15, A16u_0, A16a_0, A16b_0,
    A16lam_0, A16u_1, A16a_1, A16b_1, A16lam_1, A16u_2, A16a_2, A16b_2, A16lam_2, A16u_3,
    A16a_3, A16b_3, A16lam_3, A16u_4, A16a_4, A16b_4, A16lam_4, A16u_5, A16a_5, A16b_5,
    A16lam_5, A16u_6, A16a_6, A16b_6, A16lam_6, A16u_7, A16a_7, A16b_7, A16lam_7, A16u_8,
    A16a_8, A16b_8, A16lam_8, A16u_9, A16a_9, A16b_9, A16lam_9, A16u_10, A16a_10, A16b_10,
    A16lam_10, A16u_11, A16a_11, A16b_11, A16lam_11, A16u_12, A16a_12, A16b_12, A16lam_12,
    A16u_13, A16a_13, A16b_13, A16lam_13, A16u_14, A16a_14, A16b_14, A16lam_14,
    A16succ_0, A16succ_1, A16succ_2, A16succ_3, A16succ_4, A16succ_5, A16succ_6, A16succ_7, A16succ_8, A16succ_9, A16succ_10, A16succ_11, A16succ_12, A16succ_13, A16succ_14, A16succ_15]
  linear_combination (η : ℝ) * alpha_sum (Real.cos z)
    + (-2 * (v 0).1) * gradx_0 z hF + (-2 * (v 0).2) * grady_0 z hF
    + (-2 * (v 1).1) * gradx_1 z hF + (-2 * (v 1).2) * grady_1 z hF
    + (-2 * (v 2).1) * gradx_2 z hF + (-2 * (v 2).2) * grady_2 z hF
    + (-2 * (v 3).1) * gradx_3 z hF + (-2 * (v 3).2) * grady_3 z hF
    + (-2 * (v 4).1) * gradx_4 z hF + (-2 * (v 4).2) * grady_4 z hF
    + (-2 * (v 5).1) * gradx_5 z hF + (-2 * (v 5).2) * grady_5 z hF
    + (-2 * (v 6).1) * gradx_6 z hF + (-2 * (v 6).2) * grady_6 z hF
    + (-2 * (v 7).1) * gradx_7 z hF + (-2 * (v 7).2) * grady_7 z hF
    + (-2 * (v 8).1) * gradx_8 z hF + (-2 * (v 8).2) * grady_8 z hF
    + (-2 * (v 9).1) * gradx_9 z hF + (-2 * (v 9).2) * grady_9 z hF
    + (-2 * (v 10).1) * gradx_10 z hF + (-2 * (v 10).2) * grady_10 z hF
    + (-2 * (v 11).1) * gradx_11 z hF + (-2 * (v 11).2) * grady_11 z hF
    + (-2 * (v 12).1) * gradx_12 z hF + (-2 * (v 12).2) * grady_12 z hF
    + (-2 * (v 13).1) * gradx_13 z hF + (-2 * (v 13).2) * grady_13 z hF
    + (-2 * (v 14).1) * gradx_14 z hF + (-2 * (v 14).2) * grady_14 z hF
    + (-2 * (v 15).1) * gradx_15 z hF + (-2 * (v 15).2) * grady_15 z hF


/-- **The algebraic core of Theorem 3.5, at the certified `A16` — nothing
assumed about the multipliers or the rank.**

At any root of the constructor equation lying in the certified bracket and in
the upper half plane, there is no nonzero admissible blow-up direction: a
direction in the first-order feasible cone that does not decrease the objective
and is normalised into `R(p)^⊥` must vanish identically.

Both hypotheses of the abstract criterion are discharged here — the multiplier
identity with strictly positive active-diameter multipliers by
`A16_multiplier_identity` and `A16_lam_pos`, and `I_eq ⊆ R_eq` by
`A16_Ieq_imp_R`. Neither is an assumption of this statement.

Between this and Theorem 3.5 lies the analytic half of the paper's proof: that a
hypothetical sequence of feasible competitors converging to `A16` with perimeter
at least `L(p,ℓ)`, none congruent to `p`, yields a *unit* vector `(v, η)` with
exactly the three properties assumed here. That step — the local Euclidean
slice, openness of strict convexity, compactness, and the first-order limits of
the constraints — is formalised in `Feasible.lean`, `FeasibleOpen.lean`,
`FeasibleTangent.lean`, `FeasibleRigid.lean` and `FeasibleMain.lean`. With it,
`v = 0 ∧ η = 0` contradicts `‖(v, η)‖ = 1` and Theorem 3.5 follows;
`Feasible.A16_locally_maximal` carries that out. -/
theorem A16_no_admissible_direction (z : ℝ) (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (v : Fin 16 → ℝ × ℝ) (η : ℝ)
    (hK : (A16Data z).Keq v η) (hη : 0 ≤ η)
    (hslice : ∀ r, (A16Data z).R r → cip v r = 0) :
    v = 0 ∧ η = 0 :=
  no_admissible_direction one_pos (A16_multiplier_identity z hF)
    (A16_lam_pos z hcb) (A16_Ieq_imp_R z hF hsz hcb) hK hη hslice

end Chiquipoli.FirstOrder
