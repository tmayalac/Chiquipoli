/-
**Theorem 6.4 as printed: the explicit radius from the article's own constants.**

`Theory/Radius.lean` proves Theorem 6.4 by the article's argument, but in the
squared normalisation and with Lean's own multiplier witness, so its
intermediate constants are not the printed ones. This file follows the printed
proof of Theorem 6.4 in the article's own normalisation, so that the four
printed constants — `‖α‖₂ < 4.004`, `λ_min > 0.09186` (Proposition 6.2(5)),
`s₃₀(B)² ≥ 0.09119` (Proposition 6.2(7)) and `ℓ > 0.1959` (Proposition 6.2(2))
— are exactly the hypotheses consumed, and the printed condition
`r ≤ σℓ / (2(1 + ‖α‖₂/λ_min))` is exactly the closing inequality.

The data are those of Definition 2.5 / `Data`: side rows `sᵢ = (p_{i+1} − pᵢ)/ℓ`
(unit vectors), diameter rows `u_e = p_b − p_a` (unit vectors), the side
differential `⟪sᵢ, Δξᵢ⟫ − η` and the objective coefficient `κ = 16` of
the perimeter. `B` is the Jacobian `D(e,d)`; on the complement of the rigid
motions `‖Bh‖² ≥ σ2 ‖h‖²` is the form of `s₃₀(B)² ≥ σ2` that the proof uses.

One step is written without square roots: the printed proof bounds
`‖Bh‖₂ ≤ ‖B_e h‖₂ + ‖B_d h‖₁`; here `‖Bh‖₂² ≤ ‖B_e h‖₂² + ‖B_d h‖₁²`, which is
sharper, is used and then relaxed to the printed factor `(1 + ‖α‖₂/λ_min)²`.
The closing condition is the printed one.

Also here: the affine-combination and change-of-normalisation lemmas that carry
a squared-normalisation multiplier identity to the article's, and four
bounds on products and quotients used by the generated file.
-/
import ChiquipoliLean.Theory.Radius
import ChiquipoliLean.Theory.Coercive

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder Finset

variable {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι]

/-! ## Bounds on products and quotients -/

omit [NeZero n] in
lemma div_lb_pos {a W l l2 : ℝ} (ha : 0 ≤ a) (hW : a ≤ W) (hl : 0 < l) (hl2 : l ≤ l2) :
    a / l2 ≤ W / l := by
  have hl2p : 0 < l2 := lt_of_lt_of_le hl hl2
  rw [div_le_div_iff₀ hl2p hl]
  nlinarith [mul_le_mul_of_nonneg_left hl2 ha, mul_le_mul_of_nonneg_right hW hl2p.le]

omit [NeZero n] in
lemma div_lb_neg {a W l l1 : ℝ} (ha : a ≤ 0) (hW : a ≤ W) (h1 : 0 < l1) (hl1 : l1 ≤ l) :
    a / l1 ≤ W / l := by
  have hl : 0 < l := lt_of_lt_of_le h1 hl1
  rw [div_le_div_iff₀ h1 hl]
  nlinarith [mul_le_mul_of_nonpos_left hl1 ha, mul_le_mul_of_nonneg_right hW h1.le]

omit [NeZero n] in
/-- `l·d ≥ l*·d_lo`, with `l* = l1` when `d_lo ≥ 0` and `l* = l2` otherwise. -/
lemma mul_lb {d dlo l lstar : ℝ} (hd : dlo ≤ d) (hl : 0 < l)
    (hs : dlo * (l - lstar) ≥ 0) : lstar * dlo ≤ l * d := by
  nlinarith [mul_le_mul_of_nonneg_left hd hl.le]

omit [NeZero n] in
/-- `l·d ≤ l*·d_hi`, with `l* = l2` when `d_hi ≥ 0` and `l* = l1` otherwise. -/
lemma mul_ub {d dhi l lstar : ℝ} (hd : d ≤ dhi) (hl : 0 < l)
    (hs : dhi * (lstar - l) ≥ 0) : l * d ≤ lstar * dhi := by
  nlinarith [mul_le_mul_of_nonneg_left hd hl.le]

/-! ## Multiplier identities -/

/-- An affine combination of two multiplier vectors for the same objective
coefficient `1` is again one. -/
theorem MultiplierIdentity_affine (D : Data n ι) {α₀ α₁ : Fin n → ℝ} {l₀ l₁ : ι → ℝ}
    (h0 : D.MultiplierIdentity 1 α₀ l₀) (h1 : D.MultiplierIdentity 1 α₁ l₁) (θ : ℝ) :
    D.MultiplierIdentity 1 (fun i => (1 - θ) * α₀ i + θ * α₁ i)
      (fun e => (1 - θ) * l₀ e + θ * l₁ e) := by
  intro v η
  have e0 := h0 v η
  have e1 := h1 v η
  have sA : ∑ i, ((1 - θ) * α₀ i + θ * α₁ i) * D.sideD v η i
      = (1 - θ) * ∑ i, α₀ i * D.sideD v η i + θ * ∑ i, α₁ i * D.sideD v η i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1; ext i; ring
  have sL : ∑ e, ((1 - θ) * l₀ e + θ * l₁ e) * D.diamD v e
      = (1 - θ) * ∑ e, l₀ e * D.diamD v e + θ * ∑ e, l₁ e * D.diamD v e := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1; ext e; ring
  rw [sA, sL]
  linear_combination (1 - θ) * e0 + θ * e1

/-- **From the squared normalisation to the article's.** If the squared data
(`sᵢ = 2Δpᵢ`, `u_e = 2Δp_e`, variable `t = ℓ²`) satisfy the multiplier identity
with objective coefficient `1`, then the unit data (`sᵢ = Δpᵢ/ℓ`, `u_e = Δp_e`,
variable `η = m − ℓ`) satisfy it with objective coefficient `K`, multipliers
`K αᵢ` and `K λ_e / ℓ`. (At first order `dt = 2ℓ η`.) -/
theorem MultiplierIdentity_unit (D DU : Data n ι) {p : Cfg n} {l K : ℝ} (hl : 0 < l)
    (hs : ∀ i, D.s i = (2 : ℝ) • (p (i + 1) - p i))
    (hsU : ∀ i, DU.s i = (1 / l) • (p (i + 1) - p i))
    (hu : ∀ e, D.u e = (2 : ℝ) • (p (D.b e) - p (D.a e)))
    (huU : ∀ e, DU.u e = p (D.b e) - p (D.a e))
    (ha : DU.a = D.a) (hb : DU.b = D.b)
    {α : Fin n → ℝ} {lam : ι → ℝ} (hm : D.MultiplierIdentity 1 α lam) :
    DU.MultiplierIdentity K (fun i => K * α i) (fun e => K * lam e / l) := by
  intro v η
  have h := hm v (2 * l * η)
  have hs' : ∀ i, D.sideD v (2 * l * η) i = 2 * l * DU.sideD v η i := by
    intro i
    simp only [Data.sideD, hs i, hsU i, ip_smul_left]
    field_simp
  have hd' : ∀ e, D.diamD v e = 2 * DU.diamD v e := by
    intro e
    simp only [Data.diamD, hu e, huU e, ha, hb, ip_smul_left]
  have eA : ∑ i, α i * D.sideD v (2 * l * η) i = 2 * l * ∑ i, α i * DU.sideD v η i := by
    rw [Finset.mul_sum]; congr 1; ext i; rw [hs' i]; ring
  have eL : ∑ e, lam e * D.diamD v e = 2 * ∑ e, lam e * DU.diamD v e := by
    rw [Finset.mul_sum]; congr 1; ext e; rw [hd' e]; ring
  have gA : ∑ i, K * α i * DU.sideD v η i = K * ∑ i, α i * DU.sideD v η i := by
    rw [Finset.mul_sum]; congr 1; ext i; ring
  have gL : ∑ e, K * lam e / l * DU.diamD v e = K / l * ∑ e, lam e * DU.diamD v e := by
    rw [Finset.mul_sum]; congr 1; ext e; ring
  rw [eA, eL] at h
  rw [gA, gL]
  have hl0 : l ≠ 0 := hl.ne'
  field_simp
  linear_combination K * h / 2

/-! ## The printed argument -/

/-- **The printed proof of Theorem 6.4, for any configuration.**

Hypotheses, in the article's normalisation: the multiplier identity with
objective coefficient `κ ≥ 0` (`κ = 16` for the perimeter), `‖α‖₂ ≤ A2`,
`λ_e ≥ Λ > 0`, `‖Bh‖² ≥ σ2 ‖h‖²` on the complement of the rigid motions,
`ℓ ≥ ℓ₀ > 0`, at most sixteen vertices (the printed bound `‖w‖₂ ≤ 4‖h‖²` uses
`‖(η², …, η²)‖₂ = 4η²` in `ℝ¹⁶`), and the printed radius condition
`r ≤ σ ℓ₀ / (2 (1 + A2/Λ))`, written without square roots as
`4 r² (Λ + A2)² ≤ σ2 ℓ₀² Λ²`. Conclusion: every equilateral competitor of
diameter at most `1`, side length `m ≥ ℓ` and distance `< r` modulo motions has
`m = ℓ` and is congruent to `p`. -/
theorem radius_of_certificate_unit (D : Data n ι) {p : Cfg n} {l : ℝ} (hl : 0 < l)
    (hn : (n : ℝ) ≤ 16)
    (hp : D.p = p)
    (hs : ∀ i, D.s i = (1 / l) • (p (i + 1) - p i))
    (hu : ∀ e, D.u e = p (D.b e) - p (D.a e))
    (hside : ∀ i, nsq (p (i + 1) - p i) = l ^ 2)
    (hdiam : ∀ e, nsq (p (D.b e) - p (D.a e)) = 1)
    {κ : ℝ} (hκ : 0 ≤ κ) {α : Fin n → ℝ} {lam : ι → ℝ} (hm : D.MultiplierIdentity κ α lam)
    {A2 Λ σ2 l0 r : ℝ} (hA2 : 0 ≤ A2) (hΛ : 0 < Λ)
    (hα : ∑ i, α i ^ 2 ≤ A2 ^ 2) (hlam : ∀ e, Λ ≤ lam e)
    (hcoer : ∀ (v : Cfg n) (η : ℝ), (∀ w, D.R w → cip v w = 0) →
      σ2 * (cip v v + η ^ 2) ≤ (∑ i, (D.sideD v η i) ^ 2) + ∑ e, (D.diamD v e) ^ 2)
    (hσ : 0 ≤ σ2) (hl0 : 0 < l0) (hll0 : l0 ≤ l)
    (hrad : 4 * r ^ 2 * (Λ + A2) ^ 2 ≤ σ2 * l0 ^ 2 * Λ ^ 2)
    (q : Cfg n) (m : ℝ)
    (hqs : ∀ i, nsq (q (i + 1) - q i) = m ^ 2)
    (hqd : ∀ e, nsq (q (D.b e) - q (D.a e)) ≤ 1)
    (hlm : l ≤ m) (hdist : distMod q m p l < r) :
    m = l ∧ Congruent q p := by
  obtain ⟨c1, hc1⟩ := exists_cost_lt_of_distMod_lt hdist
  obtain ⟨c, hmin, hsum, hrot⟩ := exists_optimal_motion q p m l
  have hcost : motionCost q m p l c < r ^ 2 := lt_of_le_of_lt (hmin c1) hc1
  set ξ : Cfg n := fun i => gmove c (q i) - p i with hξ
  set η : ℝ := m - l with hη
  have hη0 : 0 ≤ η := by rw [hη]; linarith
  have hN0 : 0 ≤ cip ξ ξ := Finset.sum_nonneg fun i _ => ip_self_nonneg _
  set H : ℝ := cip ξ ξ + η ^ 2 with hHdef
  have hH0 : 0 ≤ H := by positivity
  have hHr : H < r ^ 2 := by
    have : H = motionCost q m p l c := by
      simp only [hHdef, motionCost, cip, nsq, hξ, hη]
    rw [this]; exact hcost
  -- a motion preserves differences, and the moved competitor is `p + ξ`
  have hmove : ∀ i j, nsq ((p j + ξ j) - (p i + ξ i)) = nsq (q j - q i) := by
    intro i j
    simp only [hξ, add_sub_cancel]
    exact nsq_gmove_sub c (q j) (q i)
  -- `ξ ⊥ R(p)`
  have horth : ∀ w, D.R w → cip ξ w = 0 := by
    rintro w ⟨t, ω, hw⟩
    have hsplit : ∀ i, ip (ξ i) (w i) = ip (ξ i) t + ω * ip (ξ i) (J (p i)) := by
      intro i
      rw [hw i, hp]
      simp only [ip, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    simp only [cip]
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ i, ip (ξ i) t = ip (∑ i, ξ i) t := ip_sum_left ξ t
    rw [h1]
    have h2 : (∑ i, ξ i) = 0 := hsum
    have h3 : (∑ i, ip (ξ i) (J (p i))) = 0 := hrot
    rw [h2, h3]; simp
  -- exact Taylor expansion of the sides: `2ℓ (B_e h)ᵢ = η² − |Δξᵢ|² = −wᵢ`
  have hsideD : ∀ i, 2 * l * D.sideD ξ η i = η ^ 2 - nsq (ξ (i + 1) - ξ i) := by
    intro i
    have h1 := hmove i (i + 1)
    rw [hqs i] at h1
    have h2 : (p (i + 1) + ξ (i + 1)) - (p i + ξ i) = (p (i + 1) - p i) + (ξ (i + 1) - ξ i) := by
      abel
    rw [h2, nsq_add, hside i] at h1
    have hm' : m = l + η := by rw [hη]; ring
    rw [hm'] at h1
    have e : 2 * l * D.sideD ξ η i
        = 2 * ip (p (i + 1) - p i) (ξ (i + 1) - ξ i) - 2 * l * η := by
      simp only [Data.sideD, hs i, ip_smul_left]
      field_simp
    rw [e]
    linear_combination h1
  -- exact Taylor expansion of the active diameters: `2 (B_d h)_e ≤ −|Δξ_e|² ≤ 0`
  have hdiamD : ∀ e, 2 * D.diamD ξ e ≤ - nsq (ξ (D.b e) - ξ (D.a e)) := by
    intro e
    have h1 := hmove (D.a e) (D.b e)
    have h3 := hqd e
    rw [← h1] at h3
    have h2 : (p (D.b e) + ξ (D.b e)) - (p (D.a e) + ξ (D.a e)) =
        (p (D.b e) - p (D.a e)) + (ξ (D.b e) - ξ (D.a e)) := by abel
    rw [h2, nsq_add, hdiam e] at h3
    simp only [Data.diamD, hu e]
    linarith
  have hy0 : ∀ e, D.diamD ξ e ≤ 0 := fun e => by
    have := hdiamD e
    have := nsq_nonneg (ξ (D.b e) - ξ (D.a e))
    linarith
  have hs0 : ∀ i, 0 ≤ nsq (ξ (i + 1) - ξ i) := fun i => nsq_nonneg _
  set S : ℝ := ∑ i, nsq (ξ (i + 1) - ξ i) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hs0 i
  have hS4 : S ≤ 4 * cip ξ ξ := sum_nsq_diff_le ξ
  -- `‖B_e h‖² ≤ 4‖h‖⁴/ℓ²`, the printed `‖w‖₂ ≤ 4‖h‖²`
  set E : ℝ := ∑ i, (D.sideD ξ η i) ^ 2 with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hEw : 4 * l ^ 2 * E ≤ 16 * H ^ 2 := by
    have e1 : 4 * l ^ 2 * E = ∑ i, (η ^ 2 - nsq (ξ (i + 1) - ξ i)) ^ 2 := by
      rw [hE, Finset.mul_sum]; congr 1; ext i; rw [← hsideD i]; ring
    have e2 : ∑ i, (η ^ 2 - nsq (ξ (i + 1) - ξ i)) ^ 2
        ≤ ∑ i, ((nsq (ξ (i + 1) - ξ i)) ^ 2 + η ^ 4) :=
      Finset.sum_le_sum fun i _ => by nlinarith [hs0 i, sq_nonneg η]
    have e3 : ∑ i, ((nsq (ξ (i + 1) - ξ i)) ^ 2 + η ^ 4)
        = (∑ i, (nsq (ξ (i + 1) - ξ i)) ^ 2) + (n : ℝ) * η ^ 4 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have e4 : ∑ i, (nsq (ξ (i + 1) - ξ i)) ^ 2 ≤ S ^ 2 := by
      rw [hS]; exact sum_sq_le_sq_sum _ hs0
    have e5 : S ^ 2 ≤ 16 * cip ξ ξ ^ 2 := by
      have := pow_le_pow_left₀ hS0 hS4 2
      linarith
    have e6 : (n : ℝ) * η ^ 4 ≤ 16 * η ^ 4 :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    rw [e1, hHdef]
    linarith [mul_nonneg hN0 (sq_nonneg η)]
  -- the multiplier identity at `h = (ξ, η)`
  have hid := hm ξ η
  set Y : ℝ := ∑ e, (- D.diamD ξ e) with hYdef
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun e _ => neg_nonneg.mpr (hy0 e)
  set T : ℝ := ∑ i, α i * D.sideD ξ η i with hT
  have hΛY : Λ * Y ≤ T := by
    have h1 : ∑ e, Λ * (- D.diamD ξ e) ≤ ∑ e, lam e * (- D.diamD ξ e) :=
      Finset.sum_le_sum fun e _ =>
        mul_le_mul_of_nonneg_right (hlam e) (neg_nonneg.mpr (hy0 e))
    have h2 : ∑ e, lam e * (- D.diamD ξ e) = - ∑ e, lam e * D.diamD ξ e := by
      rw [← Finset.sum_neg_distrib]; congr 1; ext e; ring
    have h3 : Λ * Y = ∑ e, Λ * (- D.diamD ξ e) := by rw [hYdef, Finset.mul_sum]
    have h4 : 0 ≤ κ * η := mul_nonneg hκ hη0
    linarith
  -- Cauchy–Schwarz: `α · B_e h ≤ ‖α‖₂ ‖B_e h‖₂`
  have hCS : T ^ 2 ≤ A2 ^ 2 * E := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ α (fun i => D.sideD ξ η i)
    calc T ^ 2 ≤ (∑ i, α i ^ 2) * E := this
      _ ≤ A2 ^ 2 * E := mul_le_mul_of_nonneg_right hα hE0
  have hY2 : (Λ * Y) ^ 2 ≤ A2 ^ 2 * E := by
    have h0 : 0 ≤ Λ * Y := mul_nonneg hΛ.le hY0
    have := pow_le_pow_left₀ h0 hΛY 2
    linarith
  -- `‖Bh‖² ≤ ‖B_e h‖² + ‖B_d h‖₁² ≤ (1 + A2/Λ)² ‖B_e h‖²`
  have hQ2 : ∑ e, (D.diamD ξ e) ^ 2 ≤ Y ^ 2 := by
    have : ∑ e, (D.diamD ξ e) ^ 2 = ∑ e, (- D.diamD ξ e) ^ 2 := by congr 1; ext e; ring
    rw [this, hYdef]; exact sum_sq_le_sq_sum _ fun e => neg_nonneg.mpr (hy0 e)
  have hB : Λ ^ 2 * (E + ∑ e, (D.diamD ξ e) ^ 2) ≤ (Λ + A2) ^ 2 * E := by
    linarith [mul_le_mul_of_nonneg_left hQ2 (sq_nonneg Λ),
      mul_nonneg (mul_nonneg hΛ.le hA2) hE0]
  -- coercivity
  have hco := hcoer ξ η horth
  have hΛ2 : 0 < Λ ^ 2 := by positivity
  have hLA : 0 < (Λ + A2) ^ 2 := by positivity
  -- the conclusion: `h = 0`
  have hHz : H = 0 := by
    by_contra hne
    have hHpos : 0 < H := lt_of_le_of_ne hH0 (Ne.symm hne)
    -- `Λ² σ2 H ℓ² ≤ (Λ + A2)² ℓ² E ≤ 4 (Λ + A2)² H²`
    have k1 : Λ ^ 2 * (σ2 * H) ≤ (Λ + A2) ^ 2 * E :=
      le_trans (mul_le_mul_of_nonneg_left hco hΛ2.le) hB
    have k2 : l ^ 2 * E ≤ 4 * H ^ 2 := by linarith
    have k3 : Λ ^ 2 * σ2 * l ^ 2 * H ≤ 4 * (Λ + A2) ^ 2 * H ^ 2 := by
      linarith [mul_le_mul_of_nonneg_left k1 (sq_nonneg l),
        mul_le_mul_of_nonneg_left k2 hLA.le]
    have k4 : Λ ^ 2 * σ2 * l ^ 2 ≤ 4 * (Λ + A2) ^ 2 * H := by
      have : H * (Λ ^ 2 * σ2 * l ^ 2) ≤ H * (4 * (Λ + A2) ^ 2 * H) := by linarith
      exact le_of_mul_le_mul_left this hHpos
    have k5 : 4 * (Λ + A2) ^ 2 * H < 4 * r ^ 2 * (Λ + A2) ^ 2 := by
      have h4 : 0 < 4 * (Λ + A2) ^ 2 := by positivity
      linarith [mul_lt_mul_of_pos_left hHr h4]
    have k6 : σ2 * l0 ^ 2 * Λ ^ 2 ≤ Λ ^ 2 * σ2 * l ^ 2 := by
      have : l0 ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ hl0.le hll0 2
      linarith [mul_le_mul_of_nonneg_left this (mul_nonneg hσ hΛ2.le)]
    linarith
  have hN : cip ξ ξ = 0 := by linarith [sq_nonneg η]
  have hηz : η = 0 := by
    have : η ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have hξ0 : ξ = 0 := eq_zero_of_cip_self hN
  have h0 : ∀ i, ξ i = 0 := fun i => congrFun hξ0 i
  refine ⟨by rw [hη] at hηz; linarith, c, ?_⟩
  funext i
  show gmove c (q i) = p i
  exact sub_eq_zero.mp (h0 i)

end Chiquipoli.Feasible
