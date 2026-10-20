/-
**Theorem 6.4 at `A16` with the printed constants — kernel-checked.**

`Instances/A16Radius.lean` proves the statement of Theorem 6.4 with Lean's own
constants. This file proves it again by the printed argument
(`radius_of_certificate_unit`, `Theory/RadiusPrinted.lean`) from the printed
constants, and proves those constants:

  * the article's normalisation: the unit Jacobian `B = D(e,d)` (`A16DataU`:
    side rows `Δpᵢ/ℓ`, diameter rows `Δp_e`, side differential `⟪·,·⟫ − η`);
  * the article's multiplier vector — the representative of Table S2, pinned at
    `λ_(0,9) = 1/5` (`A16_lamP_pin`) — as the exact combination
    `16·((1 − θ)·M0 + θ·W1)` (`α`) and `16·((1 − θ)·M0 + θ·W1)/ℓ` (`λ`),
    `θ = 75ℓ/16`, of the witness `W1` of `Generated/Multipliers.lean` and the
    witness `M0` of `Generated/RadiusPrinted.lean`, with the identity
    `16η = α·B_e h + λ·B_d h` (`A16_multiplier_identity_printed`) and
    `Σ αᵢ = −16` (`A16_alphaP_sum`);
  * Proposition 6.2(5): `λ_e > 0.09186` (`A16_lamP_gt`), `‖α‖₂ < 4.004`
    (`A16_alphaP_sq`), on the root bracket of width `10⁻²²`;
  * Proposition 6.2(7) in the form the proof uses: `‖Bh‖² ≥ 0.09119 ‖h‖²` for
    `h ⊥ R_eq` (`A16_coercive_unit`);
  * Proposition 6.2(2) in the form the proof uses: `ℓ > 0.1959`;
  * Theorem 6.4 from these constants (`A16_radius_printed`), and the printed
    constants collected in one statement (`A16_printed_constants`).
-/
import ChiquipoliLean.Instances.A16Radius
import ChiquipoliLean.Generated.RadiusPrinted
import ChiquipoliLean.Constructor.SideLength

namespace Chiquipoli.FirstOrder

open Chiquipoli

/-- The side multipliers of the second witness `M0`. -/
noncomputable def A16alphaN (c : ℝ) : Fin 16 → ℝ :=
  ![nA0 c, nA1 c, nA2 c, nA3 c, nA4 c, nA5 c, nA6 c, nA7 c, nA8 c, nA9 c, nA10 c, nA11 c, nA12 c, nA13 c, nA14 c, nA15 c]

/-- The active-diameter multipliers of the second witness `M0`. -/
noncomputable def A16lamN (c : ℝ) : Fin 15 → ℝ :=
  ![nL0 c, nL1 c, nL2 c, nL3 c, nL4 c, nL5 c, nL6 c, nL7 c, nL8 c, nL9 c, nL10 c, nL11 c, nL12 c, nL13 c, nL14 c]

@[simp] lemma A16alphaN_0 (c : ℝ) : A16alphaN c 0 = nA0 c := rfl
@[simp] lemma A16alphaN_1 (c : ℝ) : A16alphaN c 1 = nA1 c := rfl
@[simp] lemma A16alphaN_2 (c : ℝ) : A16alphaN c 2 = nA2 c := rfl
@[simp] lemma A16alphaN_3 (c : ℝ) : A16alphaN c 3 = nA3 c := rfl
@[simp] lemma A16alphaN_4 (c : ℝ) : A16alphaN c 4 = nA4 c := rfl
@[simp] lemma A16alphaN_5 (c : ℝ) : A16alphaN c 5 = nA5 c := rfl
@[simp] lemma A16alphaN_6 (c : ℝ) : A16alphaN c 6 = nA6 c := rfl
@[simp] lemma A16alphaN_7 (c : ℝ) : A16alphaN c 7 = nA7 c := rfl
@[simp] lemma A16alphaN_8 (c : ℝ) : A16alphaN c 8 = nA8 c := rfl
@[simp] lemma A16alphaN_9 (c : ℝ) : A16alphaN c 9 = nA9 c := rfl
@[simp] lemma A16alphaN_10 (c : ℝ) : A16alphaN c 10 = nA10 c := rfl
@[simp] lemma A16alphaN_11 (c : ℝ) : A16alphaN c 11 = nA11 c := rfl
@[simp] lemma A16alphaN_12 (c : ℝ) : A16alphaN c 12 = nA12 c := rfl
@[simp] lemma A16alphaN_13 (c : ℝ) : A16alphaN c 13 = nA13 c := rfl
@[simp] lemma A16alphaN_14 (c : ℝ) : A16alphaN c 14 = nA14 c := rfl
@[simp] lemma A16alphaN_15 (c : ℝ) : A16alphaN c 15 = nA15 c := rfl
@[simp] lemma A16lamN_0 (c : ℝ) : A16lamN c 0 = nL0 c := rfl
@[simp] lemma A16lamN_1 (c : ℝ) : A16lamN c 1 = nL1 c := rfl
@[simp] lemma A16lamN_2 (c : ℝ) : A16lamN c 2 = nL2 c := rfl
@[simp] lemma A16lamN_3 (c : ℝ) : A16lamN c 3 = nL3 c := rfl
@[simp] lemma A16lamN_4 (c : ℝ) : A16lamN c 4 = nL4 c := rfl
@[simp] lemma A16lamN_5 (c : ℝ) : A16lamN c 5 = nL5 c := rfl
@[simp] lemma A16lamN_6 (c : ℝ) : A16lamN c 6 = nL6 c := rfl
@[simp] lemma A16lamN_7 (c : ℝ) : A16lamN c 7 = nL7 c := rfl
@[simp] lemma A16lamN_8 (c : ℝ) : A16lamN c 8 = nL8 c := rfl
@[simp] lemma A16lamN_9 (c : ℝ) : A16lamN c 9 = nL9 c := rfl
@[simp] lemma A16lamN_10 (c : ℝ) : A16lamN c 10 = nL10 c := rfl
@[simp] lemma A16lamN_11 (c : ℝ) : A16lamN c 11 = nL11 c := rfl
@[simp] lemma A16lamN_12 (c : ℝ) : A16lamN c 12 = nL12 c := rfl
@[simp] lemma A16lamN_13 (c : ℝ) : A16lamN c 13 = nL13 c := rfl
@[simp] lemma A16lamN_14 (c : ℝ) : A16lamN c 14 = nL14 c := rfl

/-- The multiplier identity for the second witness, in the squared
normalisation; the proof is that of `A16_multiplier_identity`, with the
stationarity identities of `M0`. -/
theorem A16_multiplier_identityN (z : ℝ) (hF : Ffun z = 0) :
    (A16Data z).MultiplierIdentity 1 (A16alphaN (Real.cos z)) (A16lamN (Real.cos z)) := by
  intro v η
  rw [sum16, sum15]
  simp only [A16Data, Data.sideD, Data.diamD, twice, ip, Prod.fst_sub, Prod.snd_sub, A16s_0,
    A16s_1, A16s_2, A16s_3, A16s_4, A16s_5, A16s_6, A16s_7, A16s_8, A16s_9, A16s_10, A16s_11,
    A16s_12, A16s_13, A16s_14, A16s_15, A16alphaN_0, A16alphaN_1, A16alphaN_2, A16alphaN_3,
    A16alphaN_4, A16alphaN_5, A16alphaN_6, A16alphaN_7, A16alphaN_8, A16alphaN_9, A16alphaN_10,
    A16alphaN_11, A16alphaN_12, A16alphaN_13, A16alphaN_14, A16alphaN_15, A16u_0, A16a_0, A16b_0,
    A16lamN_0, A16u_1, A16a_1, A16b_1, A16lamN_1, A16u_2, A16a_2, A16b_2, A16lamN_2, A16u_3,
    A16a_3, A16b_3, A16lamN_3, A16u_4, A16a_4, A16b_4, A16lamN_4, A16u_5, A16a_5, A16b_5,
    A16lamN_5, A16u_6, A16a_6, A16b_6, A16lamN_6, A16u_7, A16a_7, A16b_7, A16lamN_7, A16u_8,
    A16a_8, A16b_8, A16lamN_8, A16u_9, A16a_9, A16b_9, A16lamN_9, A16u_10, A16a_10, A16b_10,
    A16lamN_10, A16u_11, A16a_11, A16b_11, A16lamN_11, A16u_12, A16a_12, A16b_12, A16lamN_12,
    A16u_13, A16a_13, A16b_13, A16lamN_13, A16u_14, A16a_14, A16b_14, A16lamN_14,
    A16succ_0, A16succ_1, A16succ_2, A16succ_3, A16succ_4, A16succ_5, A16succ_6, A16succ_7, A16succ_8, A16succ_9, A16succ_10, A16succ_11, A16succ_12, A16succ_13, A16succ_14, A16succ_15]
  linear_combination (η : ℝ) * nalpha_sum (Real.cos z)
    + (-2 * (v 0).1) * ngradx_0 z hF + (-2 * (v 0).2) * ngrady_0 z hF
    + (-2 * (v 1).1) * ngradx_1 z hF + (-2 * (v 1).2) * ngrady_1 z hF
    + (-2 * (v 2).1) * ngradx_2 z hF + (-2 * (v 2).2) * ngrady_2 z hF
    + (-2 * (v 3).1) * ngradx_3 z hF + (-2 * (v 3).2) * ngrady_3 z hF
    + (-2 * (v 4).1) * ngradx_4 z hF + (-2 * (v 4).2) * ngrady_4 z hF
    + (-2 * (v 5).1) * ngradx_5 z hF + (-2 * (v 5).2) * ngrady_5 z hF
    + (-2 * (v 6).1) * ngradx_6 z hF + (-2 * (v 6).2) * ngrady_6 z hF
    + (-2 * (v 7).1) * ngradx_7 z hF + (-2 * (v 7).2) * ngrady_7 z hF
    + (-2 * (v 8).1) * ngradx_8 z hF + (-2 * (v 8).2) * ngrady_8 z hF
    + (-2 * (v 9).1) * ngradx_9 z hF + (-2 * (v 9).2) * ngrady_9 z hF
    + (-2 * (v 10).1) * ngradx_10 z hF + (-2 * (v 10).2) * ngrady_10 z hF
    + (-2 * (v 11).1) * ngradx_11 z hF + (-2 * (v 11).2) * ngrady_11 z hF
    + (-2 * (v 12).1) * ngradx_12 z hF + (-2 * (v 12).2) * ngrady_12 z hF
    + (-2 * (v 13).1) * ngradx_13 z hF + (-2 * (v 13).2) * ngrady_13 z hF
    + (-2 * (v 14).1) * ngradx_14 z hF + (-2 * (v 14).2) * ngrady_14 z hF
    + (-2 * (v 15).1) * ngradx_15 z hF + (-2 * (v 15).2) * ngrady_15 z hF

end Chiquipoli.FirstOrder

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder

/-- The side length `ℓ = 2 sin(z/2)`. -/
noncomputable def A16ell (z : ℝ) : ℝ := 2 * Real.sin (z / 2)

/-- The article's Jacobian `D(e,d)` at `A16`: unit side rows `Δpᵢ/ℓ`, unit
diameter rows `Δp_e`. -/
noncomputable def A16DataU (z : ℝ) : Data 16 (Fin 15) :=
  { s := fun i => (1 / A16ell z) • (A16p z (i + 1) - A16p z i),
    u := fun e => A16p z (A16b e) - A16p z (A16a e),
    a := A16a, b := A16b, p := A16p z }

/-- The weight of `W1` in the article's representative. -/
noncomputable def A16theta (z : ℝ) : ℝ := 75 * A16ell z / 16

/-- The article's side multipliers (Table S2(a)). -/
noncomputable def A16alphaP (z : ℝ) : Fin 16 → ℝ := fun i =>
  16 * ((1 - A16theta z) * A16alphaN (Real.cos z) i + A16theta z * A16alpha (Real.cos z) i)

/-- The article's active-diameter multipliers (Table S2(b)). -/
noncomputable def A16lamP (z : ℝ) : Fin 15 → ℝ := fun e =>
  16 * ((1 - A16theta z) * A16lamN (Real.cos z) e + A16theta z * A16lam (Real.cos z) e) / A16ell z

lemma A16_ell_pos {z : ℝ} (h0 : 0 < z) (hpi : z < Real.pi) : 0 < A16ell z := by
  unfold A16ell; have := sin_half_pos h0 hpi; linarith

lemma A16_ell_sq (z : ℝ) : A16ell z ^ 2 = 2 - 2 * Real.cos z := by
  unfold A16ell
  have h1 : Real.cos z = Real.cos (2 * (z / 2)) := by rw [show 2 * (z / 2) = z by ring]
  have h3 := Real.sin_sq_add_cos_sq (z / 2)
  rw [h1, Real.cos_two_mul]
  linear_combination 4 * h3

/-- The root bracket of `SideLength.lean`, widened to `[prLo, prHi]`. -/
lemma A16_c_tight {z : ℝ} (hF : Ffun z = 0) (hcb : Real.cos z ∈ Set.Ioo clo chi) :
    prLo ≤ Real.cos z ∧ Real.cos z ≤ prHi := by
  obtain ⟨h1, h2⟩ := cos_root_tight z hF hcb
  have e1 : prLo ≤ cLo := by unfold prLo cLo; norm_num
  have e2 : cHi ≤ prHi := by unfold prHi cHi; norm_num
  exact ⟨by linarith, by linarith⟩

lemma A16_ell_tight {z : ℝ} (hF : Ffun z = 0) (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (h0 : 0 < z) (hpi : z < Real.pi) : prL1 ≤ A16ell z ∧ A16ell z ≤ prL2 := by
  have hl := A16_ell_pos h0 hpi
  have hsq := A16_ell_sq z
  obtain ⟨c1, c2⟩ := A16_c_tight hF hcb
  have s1 := prL1_sq
  have s2 := prL2_sq
  constructor
  · exact le_of_pow_le_pow_left₀ two_ne_zero hl.le (by linarith)
  · exact le_of_pow_le_pow_left₀ two_ne_zero prL2_pos.le (by linarith)

lemma A16_ell_coarse {z : ℝ} (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (h0 : 0 < z) (hpi : z < Real.pi) :
    (3919 / 20000 : ℝ) ≤ A16ell z ∧ A16ell z ≤ 4899 / 25000 := by
  have hl := A16_ell_pos h0 hpi
  have hsq := A16_ell_sq z
  have c1 := hcb.1; have c2 := hcb.2
  unfold clo at c1; unfold chi at c2
  constructor
  · exact le_of_pow_le_pow_left₀ two_ne_zero hl.le (by nlinarith)
  · exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) (by nlinarith)

/-! ## The article's multiplier vector -/

/-- **The identity (multiplier-identity) of the article, with the multipliers of
Table S2.** `16 η = α·B_e h + λ·B_d h` for every `h = (v, η)`. -/
theorem A16_multiplier_identity_printed {z : ℝ} (hF : Ffun z = 0) (h0 : 0 < z)
    (hpi : z < Real.pi) :
    (A16DataU z).MultiplierIdentity 16 (A16alphaP z) (A16lamP z) :=
  MultiplierIdentity_unit (A16Data z) (A16DataU z) (p := A16p z) (A16_ell_pos h0 hpi)
    (A16_s_smul z) (fun i => rfl) (A16_u_smul z) (fun e => rfl) rfl rfl
    (MultiplierIdentity_affine (A16Data z) (A16_multiplier_identityN z hF)
      (A16_multiplier_identity z hF) (A16theta z))

/-- The normalisation of Table S2: `λ_(0,9) = 1/5`. -/
theorem A16_lamP_pin {z : ℝ} (h0 : 0 < z) (hpi : z < Real.pi) : A16lamP z 2 = 1 / 5 := by
  have hl := A16_ell_pos h0 hpi
  show 16 * ((1 - A16theta z) * nL2 (Real.cos z) + A16theta z * mL2 (Real.cos z)) / A16ell z = 1 / 5
  simp only [nL2, mL2, A16theta]
  field_simp
  ring

/-- Remark 3.2 for the article's multipliers: `Σ αᵢ = −16`. -/
theorem A16_alphaP_sum {z : ℝ} (hF : Ffun z = 0) (h0 : 0 < z) (hpi : z < Real.pi) :
    (∑ i, A16alphaP z i) = -16 :=
  multiplier_balance (A16_multiplier_identity_printed hF h0 hpi)

/-- **Proposition 6.2(5), the diameter multipliers:** every `λ_e > 0.09186`. -/
theorem A16_lamP_gt {z : ℝ} (hF : Ffun z = 0) (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (h0 : 0 < z) (hpi : z < Real.pi) : ∀ e, (9186 / 100000 : ℝ) < A16lamP z e := by
  have hc := A16_c_tight hF hcb
  have hl := A16_ell_tight hF hcb h0 hpi
  have hl0 := A16_ell_pos h0 hpi
  have key : ∀ e, A16lamP z e = 16 * A16lamN (Real.cos z) e / A16ell z
      + 75 * (A16lam (Real.cos z) e - A16lamN (Real.cos z) e) := by
    intro e; unfold A16lamP A16theta; field_simp; ring
  intro e
  rw [key e]
  fin_cases e
  · show _ < 16 * nL0 (Real.cos z) / A16ell z + 75 * (mL0 (Real.cos z) - nL0 (Real.cos z))
    linarith [lamP_lb_0 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL1 (Real.cos z) / A16ell z + 75 * (mL1 (Real.cos z) - nL1 (Real.cos z))
    linarith [lamP_lb_1 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL2 (Real.cos z) / A16ell z + 75 * (mL2 (Real.cos z) - nL2 (Real.cos z))
    linarith [lamP_lb_2 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL3 (Real.cos z) / A16ell z + 75 * (mL3 (Real.cos z) - nL3 (Real.cos z))
    linarith [lamP_lb_3 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL4 (Real.cos z) / A16ell z + 75 * (mL4 (Real.cos z) - nL4 (Real.cos z))
    linarith [lamP_lb_4 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL5 (Real.cos z) / A16ell z + 75 * (mL5 (Real.cos z) - nL5 (Real.cos z))
    linarith [lamP_lb_5 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL6 (Real.cos z) / A16ell z + 75 * (mL6 (Real.cos z) - nL6 (Real.cos z))
    linarith [lamP_lb_6 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL7 (Real.cos z) / A16ell z + 75 * (mL7 (Real.cos z) - nL7 (Real.cos z))
    linarith [lamP_lb_7 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL8 (Real.cos z) / A16ell z + 75 * (mL8 (Real.cos z) - nL8 (Real.cos z))
    linarith [lamP_lb_8 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL9 (Real.cos z) / A16ell z + 75 * (mL9 (Real.cos z) - nL9 (Real.cos z))
    linarith [lamP_lb_9 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL10 (Real.cos z) / A16ell z + 75 * (mL10 (Real.cos z) - nL10 (Real.cos z))
    linarith [lamP_lb_10 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL11 (Real.cos z) / A16ell z + 75 * (mL11 (Real.cos z) - nL11 (Real.cos z))
    linarith [lamP_lb_11 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL12 (Real.cos z) / A16ell z + 75 * (mL12 (Real.cos z) - nL12 (Real.cos z))
    linarith [lamP_lb_12 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL13 (Real.cos z) / A16ell z + 75 * (mL13 (Real.cos z) - nL13 (Real.cos z))
    linarith [lamP_lb_13 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]
  · show _ < 16 * nL14 (Real.cos z) / A16ell z + 75 * (mL14 (Real.cos z) - nL14 (Real.cos z))
    linarith [lamP_lb_14 (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2]

/-- **Proposition 6.2(5), the side multipliers:** `‖α‖₂ < 4.004`. -/
theorem A16_alphaP_sq {z : ℝ} (hF : Ffun z = 0) (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (h0 : 0 < z) (hpi : z < Real.pi) : (∑ i, A16alphaP z i ^ 2) < (4004 / 1000 : ℝ) ^ 2 := by
  have hc := A16_c_tight hF hcb
  have hl := A16_ell_tight hF hcb h0 hpi
  have key : ∀ i, A16alphaP z i = 16 * A16alphaN (Real.cos z) i
      + 75 * (A16ell z * (A16alpha (Real.cos z) i - A16alphaN (Real.cos z) i)) := by
    intro i; unfold A16alphaP A16theta; ring
  rw [Finset.sum_congr rfl (fun i _ => by rw [key i]), sum16]
  simp only [A16alphaN_0, A16alphaN_1, A16alphaN_2, A16alphaN_3, A16alphaN_4, A16alphaN_5, A16alphaN_6, A16alphaN_7, A16alphaN_8, A16alphaN_9, A16alphaN_10, A16alphaN_11, A16alphaN_12, A16alphaN_13, A16alphaN_14, A16alphaN_15, A16alpha_0, A16alpha_1, A16alpha_2, A16alpha_3, A16alpha_4, A16alpha_5, A16alpha_6, A16alpha_7, A16alpha_8, A16alpha_9, A16alpha_10, A16alpha_11, A16alpha_12, A16alpha_13, A16alpha_14, A16alpha_15]
  have h := alphaP_sq (Real.cos z) (A16ell z) hc.1 hc.2 hl.1 hl.2
  have e : ((1001 / 250 : ℝ)) ^ 2 = (4004 / 1000 : ℝ) ^ 2 := by norm_num
  linarith

/-! ## Proposition 6.2(7): coercivity of the article's Jacobian -/

/-- `D(e,d)` with no diameters, at `A16`: the side-and-rigid part of `Qform`. -/
noncomputable def A16Data0 (z : ℝ) : Data 16 (Fin 0) :=
  { s := A16s z, u := ![], a := prE0, b := prE0, p := A16p z }

/-- **Proposition 6.2(7), in the form the proof of Theorem 6.4 uses:**
`‖Bh‖² ≥ 0.09119 ‖h‖²` for `h = (v, η)` with `v ⊥ R_eq(A16)`. -/
theorem A16_coercive_unit {z : ℝ} (hsz : 0 < Real.sin z) (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (h0 : 0 < z) (hpi : z < Real.pi)
    (v : Cfg 16) (η : ℝ) (horth : ∀ w, (A16DataU z).R w → cip v w = 0) :
    (9119 / 100000 : ℝ) * (cip v v + η ^ 2)
      ≤ (∑ i, ((A16DataU z).sideD v η i) ^ 2) + ∑ e, ((A16DataU z).diamD v e) ^ 2 := by
  set l := A16ell z with hldef
  have hl : 0 < l := A16_ell_pos h0 hpi
  obtain ⟨hlu1, hlu2⟩ := A16_ell_coarse hcb h0 hpi
  set dt : ℝ := 2 * l * η with hdt
  set S1 : ℝ := ∑ i, ((A16DataU z).sideD v η i) ^ 2 with hS1
  set D1 : ℝ := ∑ e, ((A16DataU z).diamD v e) ^ 2 with hD1
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hN0 : 0 ≤ cip v v := Finset.sum_nonneg fun i _ => ip_self_nonneg _
  -- the squared-normalisation rows are `2ℓ` and `2` times the article's
  have hsd : ∀ i, (A16Data z).sideD v dt i = 2 * l * (A16DataU z).sideD v η i := by
    intro i
    simp only [Data.sideD, A16_s_smul z i, A16DataU, ip_smul_left, hdt, hldef]
    field_simp
  have hdd : ∀ e, (A16Data z).diamD v e = 2 * (A16DataU z).diamD v e := by
    intro e
    show ip ((A16Data z).u e) (v (A16b e) - v (A16a e))
      = 2 * ip (A16p z (A16b e) - A16p z (A16a e)) (v (A16b e) - v (A16a e))
    rw [A16_u_smul z e, ip_smul_left]
    rfl
  have e1 := Qform_eq_of_orth (A16Data z) (p := A16p z) rfl (A16_s_smul z) (A16_u_smul z) v dt horth
  have e0 := Qform_eq_of_orth (A16Data0 z) (p := A16p z) rfl (fun i => A16_s_smul z i)
    (fun e => e.elim0) v dt horth
  have q1 : Qform (A16p z) A16a A16b v dt = 4 * l ^ 2 * S1 + 4 * D1 := by
    rw [show Qform (A16p z) A16a A16b v dt = Qform (A16p z) (A16Data z).a (A16Data z).b v dt from rfl,
      e1, hS1, hD1, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · congr 1; ext i; rw [hsd i]; ring
    · congr 1; ext e; rw [hdd e]; ring
  have q0 : Qform (A16p z) prE0 prE0 v dt = 4 * l ^ 2 * S1 := by
    rw [show Qform (A16p z) prE0 prE0 v dt = Qform (A16p z) (A16Data0 z).a (A16Data0 z).b v dt from rfl,
      e0, Fin.sum_univ_zero, add_zero, hS1, Finset.mul_sum]
    congr 1; ext i
    rw [show (A16Data0 z).sideD v dt i = (A16Data z).sideD v dt i from rfl, hsd i]; ring
  -- perturbation from `phR` to `A16`
  have hp1 := Qform_perturb (p := A16p z) (ph := phR) A16a A16b (A16_enclosure hsz hcb)
    (t := 1 / 500) (by norm_num) (by norm_num) v dt
  have hp0 := Qform_perturb (p := A16p z) (ph := phR) prE0 prE0 (A16_enclosure hsz hcb)
    (t := 1 / 500) (by norm_num) (by norm_num) v dt
  simp only [Fintype.card_fin, Nat.cast_ofNat, Nat.cast_zero, mul_zero, add_zero] at hp1 hp0
  -- the Gram bound at `phR`, at `y = ℓη/LU1`
  set y : ℝ := l * η / (3919 / 20000) with hy
  have hdty : 2 * (3919 / 20000 : ℝ) * y = dt := by rw [hy, hdt]; field_simp
  have hh := QhatU_lower v y
  rw [hdty] at hh
  have hy2 : η ^ 2 ≤ y ^ 2 := by
    rw [hy, div_pow, mul_pow, le_div_iff₀ (by norm_num)]
    have : (3919 / 20000 : ℝ) ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ (by norm_num) hlu1 2
    nlinarith [sq_nonneg η]
  have hl2 : l ^ 2 ≤ (4899 / 25000 : ℝ) ^ 2 := pow_le_pow_left₀ hl.le hlu2 2
  have hT : (1 / 4) * Qform (A16p z) A16a A16b v dt
      + (1 / (4 * (4899 / 25000 : ℝ) ^ 2) - 1 / 4) * Qform (A16p z) prE0 prE0 v dt ≤ S1 + D1 := by
    rw [q1, q0]
    nlinarith [mul_le_mul_of_nonneg_right hl2 hS10]
  have hA := coerU_arith
  have hB := coerU_arith_eta
  have hE0 : 0 ≤ radEps ^ 2 * cip v v := mul_nonneg (sq_nonneg _) hN0
  have hc0 : (0 : ℝ) ≤ 1 / (4 * (4899 / 25000 : ℝ) ^ 2) - 1 / 4 := by norm_num
  have hhat : ((((919 / 10000 : ℚ) - 1 / 1000000000000 : ℚ) : ℝ)) * (cip v v + η ^ 2)
      ≤ (1 / 4) * Qform phR A16a A16b v dt
        + (1 / (4 * (4899 / 25000 : ℝ) ^ 2) - 1 / 4) * Qform phR prE0 prE0 v dt := by
    have hpos : (0 : ℝ) ≤ (((919 / 10000 : ℚ) - 1 / 1000000000000 : ℚ) : ℝ) := by norm_num
    have := mul_le_mul_of_nonneg_left hy2 hpos
    exact le_trans (by nlinarith) hh
  nlinarith [mul_le_mul_of_nonneg_right hA hN0, mul_le_mul_of_nonneg_right hB (sq_nonneg η),
    mul_le_mul_of_nonneg_left hp0 hc0]

/-! ## Theorem 6.4 by the printed argument -/

/-- **Theorem 6.4 at the constructor root, from the printed constants.** -/
theorem A16_radius_printed_at {z : ℝ} (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) (h0 : 0 < z) (hpi : z < Real.pi)
    (q : Cfg 16) (m : ℝ)
    (hqs : ∀ i, elen (q (i + 1) - q i) = m) (hqd : ∀ i j, elen (q j - q i) ≤ 1)
    (hlm : 2 * Real.sin (z / 2) ≤ m)
    (hdist : distMod q m (A16p z) (2 * Real.sin (z / 2)) < 663 / 1000000) :
    m = 2 * Real.sin (z / 2) ∧ Congruent q (A16p z) := by
  have hl : 0 < A16ell z := A16_ell_pos h0 hpi
  have hqs' : ∀ i, nsq (q (i + 1) - q i) = m ^ 2 := by
    intro i; rw [← elen_sq, hqs i]
  have hqd' : ∀ e, nsq (q ((A16DataU z).b e) - q ((A16DataU z).a e)) ≤ 1 := by
    intro e
    have h1 := hqd ((A16DataU z).a e) ((A16DataU z).b e)
    have h2 := elen_nonneg (q ((A16DataU z).b e) - q ((A16DataU z).a e))
    rw [← elen_sq]; nlinarith
  have hl0 : (1959 / 10000 : ℝ) ≤ A16ell z := by
    have := (A16_ell_tight hF hcb h0 hpi).1
    unfold prL1 at this; linarith
  exact radius_of_certificate_unit (A16DataU z) (p := A16p z) hl (by norm_num) rfl
    (fun i => rfl) (fun e => rfl) (A16_side_nsq hF) (A16_diam_nsq z) (by norm_num : (0 : ℝ) ≤ 16)
    (A16_multiplier_identity_printed hF h0 hpi)
    (A2 := 4004 / 1000) (Λ := 9186 / 100000) (σ2 := 9119 / 100000) (l0 := 1959 / 10000)
    (r := 663 / 1000000) (by norm_num) (by norm_num)
    (le_of_lt (A16_alphaP_sq hF hcb h0 hpi)) (fun e => le_of_lt (A16_lamP_gt hF hcb h0 hpi e))
    (fun v η horth => A16_coercive_unit hsz hcb h0 hpi v η horth) (by norm_num) (by norm_num) hl0
    (by norm_num) q m hqs' hqd' hlm hdist

/-- **THEOREM 6.4, by the printed argument from the printed constants.**
Same statement as `A16_radius`. -/
theorem A16_radius_printed :
    ∃ z : ℝ, ∃ l : ℝ, 0 < l ∧
      Ffun z = 0 ∧ Real.cos z ∈ Set.Ioo clo chi ∧
      (∀ z' : ℝ, z' ∈ Set.Icc (0:ℝ) 1 → Real.cos z' ∈ Set.Icc slo shi →
        Ffun z' = 0 → z' = z) ∧
      IsFeasibleConvex (A16p z, l) ∧
      ∀ (q : Cfg 16) (m : ℝ),
        (∀ i, elen (q (i + 1) - q i) = m) → (∀ i j, elen (q j - q i) ≤ 1) → l ≤ m →
        distMod q m (A16p z) l < 663 / 1000000 → m = l ∧ Congruent q (A16p z) := by
  obtain ⟨z, hF, hsz, hcb, h0, hpi⟩ := exists_A16_root_in_Ioo_pi
  have hfeas := A16_isFeasibleConvex hF hsz hcb h0 hpi
  have hzr : z ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨h0.le, ?_⟩
    by_contra hgt
    push Not at hgt
    have hlt : Real.cos z < Real.cos 1 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi zero_le_one hpi.le hgt
    have h59 : Real.cos 1 ≤ 5 / 9 := Real.cos_one_le
    have := hcb.1
    unfold clo at this
    linarith
  have hzs : Real.cos z ∈ Set.Icc slo shi := by
    constructor
    · have := hcb.1; unfold clo at this; unfold slo; linarith
    · have := hcb.2; unfold chi at this; unfold shi; linarith
  exact ⟨z, 2 * Real.sin (z / 2), hfeas.2.2.2, hF, hcb,
    fun z' hz' hc' hf' => constructor_root_unique_in_search hz' hzr hc' hzs hf' hF,
    hfeas, fun q m hqs hqd hlm hdist =>
      A16_radius_printed_at hF hsz hcb h0 hpi q m hqs hqd hlm hdist⟩

/-- **The printed constants of the proof of Theorem 6.4, kernel-checked.** At the
constructor root (the unique one in the search bracket), with the article's
multipliers (Table S2, `λ_(0,9) = 1/5`): the identity `16η = α·B_e h + λ·B_d h`,
`Σ αᵢ = −16`, `λ_e > 0.09186` and `‖α‖₂ < 4.004` (Proposition 6.2(5)),
`‖Bh‖² ≥ 0.09119 ‖h‖²` on `R_eq^⊥` (Proposition 6.2(7)), and `ℓ > 0.1959`
(Proposition 6.2(2)). -/
theorem A16_printed_constants :
    ∃ z : ℝ, Ffun z = 0 ∧ Real.cos z ∈ Set.Ioo clo chi ∧
      (∀ z' : ℝ, z' ∈ Set.Icc (0:ℝ) 1 → Real.cos z' ∈ Set.Icc slo shi →
        Ffun z' = 0 → z' = z) ∧
      (A16DataU z).MultiplierIdentity 16 (A16alphaP z) (A16lamP z) ∧
      A16lamP z 2 = 1 / 5 ∧ (∑ i, A16alphaP z i) = -16 ∧
      (∀ e, (9186 / 100000 : ℝ) < A16lamP z e) ∧
      (∑ i, A16alphaP z i ^ 2) < (4004 / 1000 : ℝ) ^ 2 ∧
      (∀ (v : Cfg 16) (η : ℝ), (∀ w, (A16DataU z).R w → cip v w = 0) →
        (9119 / 100000 : ℝ) * (cip v v + η ^ 2)
          ≤ (∑ i, ((A16DataU z).sideD v η i) ^ 2) + ∑ e, ((A16DataU z).diamD v e) ^ 2) ∧
      (1959 / 10000 : ℝ) < A16ell z := by
  obtain ⟨z, hF, hsz, hcb, h0, hpi⟩ := exists_A16_root_in_Ioo_pi
  have hzr : z ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨h0.le, ?_⟩
    by_contra hgt
    push Not at hgt
    have hlt : Real.cos z < Real.cos 1 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi zero_le_one hpi.le hgt
    have h59 : Real.cos 1 ≤ 5 / 9 := Real.cos_one_le
    have := hcb.1
    unfold clo at this
    linarith
  have hzs : Real.cos z ∈ Set.Icc slo shi := by
    constructor
    · have := hcb.1; unfold clo at this; unfold slo; linarith
    · have := hcb.2; unfold chi at this; unfold shi; linarith
  have hl0 : (1959 / 10000 : ℝ) < A16ell z := by
    have := (A16_ell_tight hF hcb h0 hpi).1
    unfold prL1 at this; linarith
  exact ⟨z, hF, hcb, fun z' hz' hc' hf' => constructor_root_unique_in_search hz' hzr hc' hzs hf' hF,
    A16_multiplier_identity_printed hF h0 hpi, A16_lamP_pin h0 hpi, A16_alphaP_sum hF h0 hpi,
    A16_lamP_gt hF hcb h0 hpi, A16_alphaP_sq hF hcb h0 hpi,
    fun v η horth => A16_coercive_unit hsz hcb h0 hpi v η horth, hl0⟩

end Chiquipoli.Feasible
