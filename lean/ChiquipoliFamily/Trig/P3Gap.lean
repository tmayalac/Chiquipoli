/-
# Problem 3: the gap is open, `a > 0`, for `n = 16k ≥ 32`

The horizontal width of the gap, `a = A_x − B_x`, is `y(z) = 2x_n(z) + sin((n/2−1)z)`
(`gapA_eq_yy`). At `t = π/n` we have `y(t) = (1 − cos t)(1 − 2 sin t / cos 2t) > 0`,
and the root `z` lies within `1.75 t⁵` of `π/n`. The mean value theorem and
`|y'| ≤ 16` then give `y(z) > 0` (`yy_pos`), for `n ≥ 32`. For `n = 16` the note
uses an interval certificate; here the case is covered by `T16`.
-/
import ChiquipoliFamily.Trig.P3Main

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Chiquipoli.Family.Trig.P3

open Real Set Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Chiquipoli.Family.Trig.RungVec

/-! ## `a = y(z)` -/

theorem gapA_eq_yy (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) (z : ℝ) :
    gapA hk hn (z := z) = yy n z := by
  unfold gapA
  have hBC : vB hk hn = -vC hk hn := by
    apply Fin.ext; rw [neg_val]; simp only [vB, vC]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hBC, Qc_neg k hk hn z, ConstructorAll.Qc_eq z k hk hn, ConstructorAll.Qc_eq z k hk hn]
  simp only [vA, vC, mir]
  rw [P_mid z k _ (by omega) (by omega), P_hi_low z k _ (by omega) (by omega),
    show 8 * k - 1 - 4 * k = 4 * (k - 1) + 3 by omega, midRole3,
    show 16 * k - (12 * k + 1) = 4 * (k - 1) + 3 by omega, lowRole3,
    show 2 * (k - 1) + 1 = 2 * k - 1 by omega, U_pos (by omega), Q_pos (by omega)]
  simp only [ev, tu, tq, Tm.eval]
  rw [tXa_last z k hk, pm_odd k hk]
  unfold yy
  subst hn
  have e : ((16 * k : ℕ) : ℝ) / 2 - 1 = 4 * ((2 * k - 1 : ℕ) : ℝ) + 3 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e, show 8 * (2 * k) = 16 * k by ring]
  ring

/-! ## `y` and its derivative -/

theorem hasDerivAt_yy (n : ℕ) (t : ℝ) (hD : cos (2 * t) ≠ 0) : HasDerivAt (yy n) (yd n t) t := by
  have hx := hasDerivAt_x n t hD
  have hs : HasDerivAt (fun t => sin (((n : ℝ) / 2 - 1) * t)) (cos (((n : ℝ) / 2 - 1) * t) * ((n : ℝ) / 2 - 1)) t := by
    have := ((hasDerivAt_id t).const_mul ((n : ℝ) / 2 - 1)).sin
    simpa using this
  unfold yd
  exact (hx.const_mul 2).add hs

/-- `y(π/n) = (1 − cos t)(1 − 2 sin t / cos 2t)`. -/
theorem yy_right (n : ℕ) (hn : 16 ≤ n) :
    yy n (π / n) = (1 - cos (π / n)) * (1 - 2 * sin (π / n) / cos (2 * (π / n))) := by
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < n := by linarith
  set t := π / (n : ℝ) with ht
  have e1 : ((n : ℝ) / 4 - 2) * t = π / 4 - 2 * t := by rw [ht]; field_simp
  have e2 : (n : ℝ) * t / 4 = π / 4 := by rw [ht]; field_simp
  have e3 : ((n : ℝ) / 2 - 1) * t = π / 2 - t := by rw [ht]; field_simp
  have hD : cos (2 * t) ≠ 0 := by
    apply ne_of_gt; apply cos_pos_of_mem_Ioo
    have := pi_div_le_small hn; rw [← ht] at this
    constructor <;> nlinarith [pi_pos, div_pos pi_pos hNpos]
  have hq : cos (π / 4 - 2 * t) * sin (π / 4) = (cos (2 * t) + sin (2 * t)) / 2 := by
    rw [cos_sub, cos_pi_div_four, sin_pi_div_four]
    have r2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    linear_combination (cos (2 * t) + sin (2 * t)) / 4 * r2
  unfold yy Optigon.x
  rw [e1, e2, e3, mul_assoc (2 * cos t - 1), hq, sin_pi_div_two_sub]
  have hs := sin_sq_add_cos_sq t
  rw [cos_two_mul] at hD
  rw [cos_two_mul, sin_two_mul]
  field_simp
  ring

/-! ## `a > 0` for `n ≥ 32` -/

/-- `y` is `16`-Lipschitz on `J_n`. -/
lemma yy_lip (n : ℕ) (hn : 16 ≤ n) {u v : ℝ} (hu : π / ((n : ℝ) + 2) ≤ u) (huv : u ≤ v) (hv : v ≤ π / n) :
    |yy n v - yy n u| ≤ 16 * (v - u) := by
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hsmall := pi_div_le_small hn
  have hpi := pi_pos
  have hD : ∀ s ∈ Icc u v, cos (2 * s) ≠ 0 := by
    intro s hs
    have h0 : 0 < π / ((n : ℝ) + 2) := by positivity
    exact (cos_pos_of_mem_Ioo ⟨by linarith [hs.1], by linarith [hs.2]⟩).ne'
  rcases eq_or_lt_of_le huv with h | h
  · subst h; simp
  obtain ⟨c, hc, hdc⟩ := exists_hasDerivAt_eq_slope (yy n) (yd n) h
    (fun s hs => (hasDerivAt_yy n s (hD s hs)).continuousAt.continuousWithinAt)
    (fun s hs => hasDerivAt_yy n s (hD s ⟨hs.1.le, hs.2.le⟩))
  have hb := yd_bound n hn (t := c) (by linarith [hc.1]) (by linarith [hc.2])
  rw [hdc, abs_div, abs_of_pos (sub_pos.mpr h), div_le_iff₀ (sub_pos.mpr h)] at hb
  exact hb

/-- `|F_n(π/n)| ≤ 1.05 t⁵`, `t ≤ 0.0982`. -/
lemma F_right_small (t : ℝ) (ht0 : 0 < t) (htb : t < 0.0982) :
    4 * sin t * (1 - cos t) ^ 2 * (cos (2 * t) - sin t) / cos (2 * t) ^ 2 ≤ 1.05 * t ^ 5 := by
  have hs0 : 0 ≤ sin t := (sin_pos_of_pos_of_lt_pi ht0 (by linarith [pi_gt_three])).le
  have hs1 := sin_le ht0.le
  have hc1 := one_sub_sq_div_two_le_cos (x := t)
  have hc0 := cos_le_one t
  have hc2 := one_sub_sq_div_two_le_cos (x := 2 * t)
  have hc21 := cos_le_one (2 * t)
  have htt : t ^ 2 ≤ 0.0097 := by nlinarith
  have hC : (0.98 : ℝ) ≤ cos (2 * t) := by nlinarith
  have hC2 : (0.96 : ℝ) ≤ cos (2 * t) ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  have hA : 0 ≤ 1 - cos t := by linarith
  have hA' : 1 - cos t ≤ t ^ 2 / 2 := by linarith
  have hA2 : (1 - cos t) ^ 2 ≤ (t ^ 2 / 2) ^ 2 := pow_le_pow_left₀ hA hA' 2
  have hB : cos (2 * t) - sin t ≤ 1 := by linarith
  have hB0 : 0 ≤ cos (2 * t) - sin t := by linarith
  have h1 : 4 * sin t * (1 - cos t) ^ 2 * (cos (2 * t) - sin t) ≤ 4 * t * (t ^ 2 / 2) ^ 2 * 1 :=
    mul_le_mul (mul_le_mul (by linarith) hA2 (by positivity) (by positivity)) hB hB0 (by positivity)
  have e : 4 * t * (t ^ 2 / 2) ^ 2 * 1 = t ^ 5 := by ring
  have h5 : 0 < t ^ 5 := by positivity
  have h2 : t ^ 5 ≤ 1.05 * t ^ 5 * cos (2 * t) ^ 2 := by
    have : 1.05 * t ^ 5 * cos (2 * t) ^ 2 = t ^ 5 * (1.05 * cos (2 * t) ^ 2) := by ring
    rw [this]; exact le_mul_of_one_le_right h5.le (by linarith)
  linarith

/-- `y(π/n) ≥ 0.38 t²`, `t ≤ 0.0982`. -/
lemma y_right_lower (t : ℝ) (ht0 : 0 < t) (htb : t < 0.0982) :
    0.38 * t ^ 2 ≤ (1 - cos t) * (1 - 2 * sin t / cos (2 * t)) := by
  have hs1 := sin_le ht0.le
  have hc2 := one_sub_sq_div_two_le_cos (x := 2 * t)
  have hcb := cos_bound (x := t) (by rw [abs_of_pos ht0]; linarith)
  rw [abs_le, abs_of_pos ht0] at hcb
  have ht2 : t ^ 2 ≤ 0.0097 := by nlinarith
  have ht4 : (5 / 96 : ℝ) * t ^ 4 ≤ 0.01 * t ^ 2 := by
    have : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    rw [this]; nlinarith [pow_pos ht0 2]
  have hC : (0.98 : ℝ) ≤ cos (2 * t) := by nlinarith
  have h1 : 0.49 * t ^ 2 ≤ 1 - cos t := by linarith [hcb.2]
  have h2 : 0.79 ≤ 1 - 2 * sin t / cos (2 * t) := by
    rw [show 1 - 2 * sin t / cos (2 * t) = (cos (2 * t) - 2 * sin t) / cos (2 * t) by field_simp,
      le_div_iff₀ (by linarith)]
    nlinarith [cos_le_one (2 * t)]
  have h3 : 0.49 * t ^ 2 * 0.79 ≤ (1 - cos t) * (1 - 2 * sin t / cos (2 * t)) :=
    mul_le_mul h1 h2 (by norm_num) (by linarith [pow_pos ht0 2])
  nlinarith [pow_pos ht0 2]

theorem yy_pos (n : ℕ) (hn : 32 ≤ n) {z : ℝ} (hz0 : 0 < z) (hz1 : z < π / n) (hF : Optigon.F n z = 0) :
    0 < yy n z := by
  have hn16 : 16 ≤ n := by omega
  have hN : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := pi_pos
  have hpi3 := pi_gt_three
  have hpi4 : π < 3.1416 := pi_lt_d4
  obtain ⟨hloc, hy⟩ := loc n hn16 hz0 hz1 hF
  set t := π / (n : ℝ) with ht
  have ht0 : 0 < t := by positivity
  have ht32 : t ≤ π / 32 := div_le_div_of_nonneg_left hpi.le (by norm_num) hN
  have htb : t < 0.0982 := by linarith
  have hJ : π / ((n : ℝ) + 2) ≤ z := le_trans (div_le_div_of_nonneg_left hpi.le (by linarith) (by linarith)) hloc
  -- a priori: `t − z ≤ 0.0036`
  have hΔ0 : t - z ≤ 0.0036 := by
    have e : t - π / ((n : ℝ) - 2 + π) = π * (π - 2) / ((n : ℝ) * ((n : ℝ) - 2 + π)) := by
      have h1 : (n : ℝ) ≠ 0 := by linarith
      have h2 : (n : ℝ) - 2 + π ≠ 0 := by linarith
      rw [ht, div_sub_div _ _ h1 h2]; ring
    have h1 : π * (π - 2) / ((n : ℝ) * ((n : ℝ) - 2 + π)) ≤ π * (π - 2) / 1024 := by
      apply div_le_div_of_nonneg_left (by nlinarith) (by norm_num); nlinarith
    have h2 : π * (π - 2) / 1024 ≤ 0.0036 := by rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  -- `|y| ≤ 0.062` on `[z, t]`
  have hsz : 2 * sin (z / 2) ^ 2 ≤ 0.005 := by
    have := sin_le (show 0 ≤ z / 2 by linarith)
    have := (sin_pos_of_pos_of_lt_pi (show 0 < z / 2 by linarith) (by linarith)).le
    nlinarith
  have hyb : ∀ s, z ≤ s → s ≤ t → |yy n s| ≤ 0.063 := by
    intro s h1 h2
    have := yy_lip n hn16 hJ h1 h2
    have := abs_sub_abs_le_abs_sub (yy n s) (yy n z)
    linarith
  -- `F' ≤ −0.6` on `[z, t]`
  have hFd : ∀ c, z ≤ c → c ≤ t → Fd n c ≤ -0.58 := by
    intro c h1 h2
    rw [Fd_eq]
    have hm := main_term n hn16 (t := c) (by linarith) h2
    have hd := yd_bound n hn16 (t := c) (by linarith) h2
    have hyc := hyb c h1 h2
    have : |2 * yy n c * yd n c| ≤ 2 * 0.063 * 16 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hyc (by norm_num)) hd (abs_nonneg _) (by norm_num)
    have := le_abs_self (2 * yy n c * yd n c)
    linarith
  have hD : ∀ s ∈ Icc z t, cos (2 * s) ≠ 0 := by
    intro s hs
    exact (cos_pos_of_mem_Ioo ⟨by linarith [hs.1], by linarith [hs.2]⟩).ne'
  -- `t − z ≤ 1.75 t⁵`
  obtain ⟨c, hc, hdc⟩ := exists_hasDerivAt_eq_slope (Optigon.F n) (Fd n) hz1
    (fun s hs => (hasDerivAt_F n s (hD s hs)).continuousAt.continuousWithinAt)
    (fun s hs => hasDerivAt_F n s (hD s ⟨hs.1.le, hs.2.le⟩))
  have hFc := hFd c hc.1.le hc.2.le
  rw [hF, sub_zero] at hdc
  have hFt : Optigon.F n t ≤ -0.58 * (t - z) := by
    have := hdc ▸ hFc
    rw [div_le_iff₀ (by linarith)] at this; linarith
  have hFt' : -Optigon.F n t ≤ 1.05 * t ^ 5 := by
    rw [F_right_closed n hn16, ← ht, neg_div, neg_neg]
    exact F_right_small t ht0 htb
  have hΔ : t - z ≤ 1.82 * t ^ 5 := by linarith
  -- `y(z) ≥ y(t) − 16 (t − z)` and `y(t) ≥ 0.38 t²`
  have hl := yy_lip n hn16 hJ hz1.le le_rfl
  have hyt : 0.38 * t ^ 2 ≤ yy n t := by
    rw [ht, yy_right n hn16, ← ht]; exact y_right_lower t ht0 htb
  have ht3 : t ^ 3 ≤ 0.00095 := by
    have : t ^ 3 = t * t * t := by ring
    rw [this]
    have h1 : t * t ≤ 0.0982 * 0.0982 := mul_le_mul htb.le htb.le ht0.le (by norm_num)
    have h2 : t * t * t ≤ 0.0982 * 0.0982 * 0.0982 := mul_le_mul h1 htb.le ht0.le (by norm_num)
    linarith
  rw [abs_le] at hl
  have h5 : t ^ 5 = t ^ 2 * t ^ 3 := by ring
  have hfin : 16 * (1.82 * t ^ 5) < 0.38 * t ^ 2 := by
    rw [h5]; nlinarith [pow_pos ht0 2]
  linarith [hl.1]

end Chiquipoli.Family.Trig.P3
