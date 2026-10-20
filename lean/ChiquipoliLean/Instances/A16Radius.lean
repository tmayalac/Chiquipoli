/-
**Theorem 6.4 at `A16` — the explicit radius, kernel-checked.**

`Theory/Radius.lean` proves the article's argument for Theorem 6.4 from four
hypotheses on a configuration. This file discharges all of them at the
certified configuration `A16`, from theorems already in this development and
from the rational certificate `Generated/Radius.lean`:

  * the multiplier identity in the squared normalisation is
    `A16_multiplier_identity`; the bounds `αᵢ ≥ −67/1000` and `λₑ ≥ 3/2500` on
    that same witness are Bernstein certificates (`mA*_ge`, `mL*_ge`);
  * every side has length `ℓ = 2 sin(z/2)` (`all_sides_cyclic`) and every
    declared diameter has length `1` (`A16_active`);
  * coercivity, `σ2 (‖v‖² + dt²) ≤ ‖B̃(v, dt)‖²` for `v ⊥ R(p)` with
    `σ2 = 17/625`: `Qform_eq_of_orth` identifies the right-hand side with the
    Gram form, `Qform_perturb` moves from `A16` to the rational configuration
    `phR` at the cost of the vertex enclosure `radEps` (`A16_enclosure`), and
    `Qhat_lower` is the exact `LDLᵀ` certificate at `phR`.

`A16_radius` then states Theorem 6.4 for the configuration of
`A16_locally_maximal` — the unique constructor root in the search bracket: every
equilateral small hexadecagon `(q, m)` with `m ≥ ℓ` and
`distMod (q, m) (A16, ℓ) < 663/1000000` has `m = ℓ` and is congruent to `A16`.
As in the article, the competitor is neither assumed convex nor labelled in any
cyclic order; only its side lengths and its distances enter.

WHAT DIFFERS FROM THE PRINTED PROOF. The argument is the article's; the
constants are those of the squared normalisation and of this witness: Lean's
multiplier vector is not the one of Table S2, `A` bounds `−αᵢ` rather than
`‖α‖₂`, and `σ2` bounds `‖B̃h‖²/‖h‖²` for the squared-form Jacobian `B̃`. The
radius condition `16 r² (Λ² + A²) ≤ σ2 Λ²` holds at `r = 6.63 × 10⁻⁴` with
about 24% to spare.
-/
import ChiquipoliLean.Instances.A16LocalMax
import ChiquipoliLean.Theory.Radius
import ChiquipoliLean.Generated.Radius

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder

/-! ## The squared-normalisation vectors as multiples of differences -/

lemma twice_eq_smul (a b : ℝ × ℝ) : twice a b = (2 : ℝ) • (b - a) := by
  refine Prod.ext ?_ ?_ <;> simp [twice]

lemma A16_s_smul (z : ℝ) (i : Fin 16) :
    (A16Data z).s i = (2 : ℝ) • (A16p z (i + 1) - A16p z i) := by
  show A16s z i = _
  rw [A16s_eq, twice_eq_smul]

lemma A16_u_smul (z : ℝ) (e : Fin 15) :
    (A16Data z).u e = (2 : ℝ) • (A16p z ((A16Data z).b e) - A16p z ((A16Data z).a e)) := by
  show A16u z e = _
  rw [A16u_eq, twice_eq_smul]
  rfl

/-! ## Exact sides and diameters -/

lemma A16_side_nsq {z : ℝ} (hF : Ffun z = 0) (i : Fin 16) :
    nsq (A16p z (i + 1) - A16p z i) = (2 * Real.sin (z / 2)) ^ 2 := by
  have h := all_sides_cyclic z hF i
  rw [sqd_eq_nsq, ← A16p_eq_P, ← A16p_eq_P, nxt_eq_succ] at h
  exact h

lemma A16_diam_nsq (z : ℝ) (e : Fin 15) :
    nsq (A16p z ((A16Data z).b e) - A16p z ((A16Data z).a e)) = 1 := by
  have h := A16_active (z := z) e
  rw [dC, sub_eq_zero] at h
  exact h

/-! ## Multiplier bounds on the witness of `Generated/Multipliers.lean` -/

theorem A16_alpha_ge (z : ℝ) (hcb : Real.cos z ∈ Set.Ioo clo chi) :
    ∀ i, -(67 / 1000 : ℝ) ≤ A16alpha (Real.cos z) i := by
  have h1 : clo ≤ Real.cos z := le_of_lt hcb.1
  have h2 : Real.cos z ≤ chi := le_of_lt hcb.2
  intro i
  fin_cases i
  · show _ ≤ mA0 (Real.cos z); linarith [mA0_ge (Real.cos z) h1 h2]
  · show _ ≤ mA1 (Real.cos z); linarith [mA1_ge (Real.cos z) h1 h2]
  · show _ ≤ mA2 (Real.cos z); linarith [mA2_ge (Real.cos z) h1 h2]
  · show _ ≤ mA3 (Real.cos z); linarith [mA3_ge (Real.cos z) h1 h2]
  · show _ ≤ mA4 (Real.cos z); linarith [mA4_ge (Real.cos z) h1 h2]
  · show _ ≤ mA5 (Real.cos z); linarith [mA5_ge (Real.cos z) h1 h2]
  · show _ ≤ mA6 (Real.cos z); linarith [mA6_ge (Real.cos z) h1 h2]
  · show _ ≤ mA7 (Real.cos z); linarith [mA7_ge (Real.cos z) h1 h2]
  · show _ ≤ mA8 (Real.cos z); linarith [mA8_ge (Real.cos z) h1 h2]
  · show _ ≤ mA9 (Real.cos z); linarith [mA9_ge (Real.cos z) h1 h2]
  · show _ ≤ mA10 (Real.cos z); linarith [mA10_ge (Real.cos z) h1 h2]
  · show _ ≤ mA11 (Real.cos z); linarith [mA11_ge (Real.cos z) h1 h2]
  · show _ ≤ mA12 (Real.cos z); linarith [mA12_ge (Real.cos z) h1 h2]
  · show _ ≤ mA13 (Real.cos z); linarith [mA13_ge (Real.cos z) h1 h2]
  · show _ ≤ mA14 (Real.cos z); linarith [mA14_ge (Real.cos z) h1 h2]
  · show _ ≤ mA15 (Real.cos z); linarith [mA15_ge (Real.cos z) h1 h2]

theorem A16_lam_ge (z : ℝ) (hcb : Real.cos z ∈ Set.Ioo clo chi) :
    ∀ e, (3 / 2500 : ℝ) ≤ A16lam (Real.cos z) e := by
  have h1 : clo ≤ Real.cos z := le_of_lt hcb.1
  have h2 : Real.cos z ≤ chi := le_of_lt hcb.2
  intro e
  fin_cases e
  · show _ ≤ mL0 (Real.cos z); linarith [mL0_ge (Real.cos z) h1 h2]
  · show _ ≤ mL1 (Real.cos z); linarith [mL1_ge (Real.cos z) h1 h2]
  · show _ ≤ mL2 (Real.cos z); linarith [mL2_ge (Real.cos z) h1 h2]
  · show _ ≤ mL3 (Real.cos z); linarith [mL3_ge (Real.cos z) h1 h2]
  · show _ ≤ mL4 (Real.cos z); linarith [mL4_ge (Real.cos z) h1 h2]
  · show _ ≤ mL5 (Real.cos z); linarith [mL5_ge (Real.cos z) h1 h2]
  · show _ ≤ mL6 (Real.cos z); linarith [mL6_ge (Real.cos z) h1 h2]
  · show _ ≤ mL7 (Real.cos z); linarith [mL7_ge (Real.cos z) h1 h2]
  · show _ ≤ mL8 (Real.cos z); linarith [mL8_ge (Real.cos z) h1 h2]
  · show _ ≤ mL9 (Real.cos z); linarith [mL9_ge (Real.cos z) h1 h2]
  · show _ ≤ mL10 (Real.cos z); linarith [mL10_ge (Real.cos z) h1 h2]
  · show _ ≤ mL11 (Real.cos z); linarith [mL11_ge (Real.cos z) h1 h2]
  · show _ ≤ mL12 (Real.cos z); linarith [mL12_ge (Real.cos z) h1 h2]
  · show _ ≤ mL13 (Real.cos z); linarith [mL13_ge (Real.cos z) h1 h2]
  · show _ ≤ mL14 (Real.cos z); linarith [mL14_ge (Real.cos z) h1 h2]

/-! ## Coercivity at `A16` -/

/-- Every coordinate of `A16` is within `radEps` of the rational configuration
`phR`. -/
theorem A16_enclosure {z : ℝ} (hsz : 0 < Real.sin z) (hcb : Real.cos z ∈ Set.Ioo clo chi) :
    ∀ i, |(A16p z i - phR i).1| ≤ radEps ∧ |(A16p z i - phR i).2| ≤ radEps := by
  have h1 : clo ≤ Real.cos z := le_of_lt hcb.1
  have h2 : Real.cos z ≤ chi := le_of_lt hcb.2
  obtain ⟨hs1, hs2⟩ := sin_bracket z hsz h1 h2
  intro i
  fin_cases i
  · exact p0_enc z hs1 hs2 h1 h2
  · exact p1_enc z hs1 hs2 h1 h2
  · exact p2_enc z hs1 hs2 h1 h2
  · exact p3_enc z hs1 hs2 h1 h2
  · exact p4_enc z hs1 hs2 h1 h2
  · exact p5_enc z hs1 hs2 h1 h2
  · exact p6_enc z hs1 hs2 h1 h2
  · exact p7_enc z hs1 hs2 h1 h2
  · exact p8_enc z hs1 hs2 h1 h2
  · exact p9_enc z hs1 hs2 h1 h2
  · exact p10_enc z hs1 hs2 h1 h2
  · exact p11_enc z hs1 hs2 h1 h2
  · exact p12_enc z hs1 hs2 h1 h2
  · exact p13_enc z hs1 hs2 h1 h2
  · exact p14_enc z hs1 hs2 h1 h2
  · exact p15_enc z hs1 hs2 h1 h2

/-- **Coercivity at `A16`.** On the complement of the rigid motions,
`(17/625)(‖v‖² + dt²) ≤ ‖B̃(v, dt)‖²` for the squared-normalisation Jacobian. -/
theorem A16_coercive {z : ℝ} (hsz : 0 < Real.sin z) (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (v : Cfg 16) (dt : ℝ) (horth : ∀ w, (A16Data z).R w → cip v w = 0) :
    (17 / 625 : ℝ) * (cip v v + dt ^ 2)
      ≤ (∑ i, ((A16Data z).sideD v dt i) ^ 2) + ∑ e, ((A16Data z).diamD v e) ^ 2 := by
  rw [← Qform_eq_of_orth (A16Data z) (p := A16p z) rfl (A16_s_smul z) (A16_u_smul z) v dt horth]
  have hpert := Qform_perturb (p := A16p z) (ph := phR) A16a A16b (A16_enclosure hsz hcb)
    (t := 1 / 250) (by norm_num) (by norm_num) v dt
  have hhat : (((11 / 400 : ℚ) - 1 / 1000000000000 : ℚ) : ℝ) * (cip v v + dt ^ 2)
      ≤ Qform phR A16a A16b v dt := Qhat_lower v dt
  have hN : 0 ≤ cip v v := Finset.sum_nonneg fun i _ => ip_self_nonneg _
  have hD : 0 ≤ dt ^ 2 := sq_nonneg dt
  have hcard : (Fintype.card (Fin 15) : ℝ) = 15 := by simp
  rw [hcard] at hpert
  show (17 / 625 : ℝ) * (cip v v + dt ^ 2) ≤ Qform (A16p z) A16a A16b v dt
  unfold radEps at hpert
  push_cast at hhat hpert
  nlinarith [hpert, hhat, hN, hD]

/-! ## Theorem 6.4 -/

/-- **Theorem 6.4 at a root.** At any root of the constructor equation in the
certified bracket with `sin z > 0`, every equilateral small hexadecagon whose
side length is at least `ℓ = 2 sin(z/2)` and whose distance to `A16` modulo
motions is below `663/1000000` has side length `ℓ` and is congruent to `A16`. -/
theorem A16_radius_at {z : ℝ} (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) (h0 : 0 < z) (hpi : z < Real.pi)
    (q : Cfg 16) (m : ℝ)
    (hqs : ∀ i, elen (q (i + 1) - q i) = m) (hqd : ∀ i j, elen (q j - q i) ≤ 1)
    (hlm : 2 * Real.sin (z / 2) ≤ m)
    (hdist : distMod q m (A16p z) (2 * Real.sin (z / 2)) < 663 / 1000000) :
    m = 2 * Real.sin (z / 2) ∧ Congruent q (A16p z) := by
  have hl : 0 < 2 * Real.sin (z / 2) := by have := sin_half_pos h0 hpi; linarith
  have hqs' : ∀ i, nsq (q (i + 1) - q i) = m ^ 2 := by
    intro i; rw [← elen_sq, hqs i]
  have hqd' : ∀ e, nsq (q ((A16Data z).b e) - q ((A16Data z).a e)) ≤ 1 := by
    intro e
    have h1 := hqd ((A16Data z).a e) ((A16Data z).b e)
    have h2 := elen_nonneg (q ((A16Data z).b e) - q ((A16Data z).a e))
    rw [← elen_sq]; nlinarith
  exact radius_of_certificate (A16Data z) (p := A16p z) hl rfl (A16_s_smul z) (A16_u_smul z)
    (A16_side_nsq hF) (A16_diam_nsq z) (A16_multiplier_identity z hF)
    (A := 67 / 1000) (Λ := 3 / 2500) (σ2 := 17 / 625) (r := 663 / 1000000)
    (by norm_num) (A16_alpha_ge z hcb) (A16_lam_ge z hcb)
    (fun v dt horth => A16_coercive hsz hcb v dt horth) (by norm_num)
    q m hqs' hqd' hlm hdist

/-- **THEOREM 6.4, kernel-checked.**

For the configuration of `A16_locally_maximal` — built from the unique root of
the constructor equation in the search bracket — every equilateral small
hexadecagon `(q, m)` (no convexity and no cyclic order assumed) whose side length
is at least `ℓ` and whose distance to `(A16, ℓ)` modulo orientation-preserving
Euclidean motions is less than `6.63 × 10⁻⁴` has `m = ℓ` and is the image of
`A16` under an orientation-preserving Euclidean motion. -/
theorem A16_radius :
    ∃ z : ℝ, ∃ l : ℝ, 0 < l ∧
      -- the constructor root, and it is the only one in the search bracket
      Ffun z = 0 ∧ Real.cos z ∈ Set.Ioo clo chi ∧
      (∀ z' : ℝ, z' ∈ Set.Icc (0:ℝ) 1 → Real.cos z' ∈ Set.Icc slo shi →
        Ffun z' = 0 → z' = z) ∧
      -- the configuration it builds is a strictly convex equilateral small 16-gon
      IsFeasibleConvex (A16p z, l) ∧
      -- and the explicit radius of Theorem 6.4
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
    hfeas, fun q m hqs hqd hlm hdist => A16_radius_at hF hsz hcb h0 hpi q m hqs hqd hlm hdist⟩

end Chiquipoli.Feasible
