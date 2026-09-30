/-
# The zero of upstream's `F_n`, for every `n ≥ 16`

`root_all`: for every natural `n ≥ 16`, upstream's constructor equation `F_n` has
exactly one zero `z` in `(0, π/n)`; it lies in `(π/(n+2), π/n)` and it is simple,
`Fd n z < 0`. No numerics: the proof is by elementary bounds, valid for all `n`.

* `at_most_one_zero`: a continuous function whose derivative is negative at each
  of its zeros has at most one zero on an open interval.
* Localisation: at a zero `z < π/n`, `cos((n/2−1)z) ≤ 2 sin(z/2) ≤ z`, which with
  Jordan's inequality forces `z ≥ π/(n−2+π) > π/(n+2)`, and `|y| ≤ 2 sin²(z/2)`
  for `y = 2x + sin((n/2−1)z)`.
* Simplicity: `Fd = 2 y y' − (n/2−1) sin((n−2)t) − 2 sin t`, with `|y'| ≤ 16` and the
  last two terms `≥ 2.68` on `[π/(n+2), π/n]`.
* Existence: `F_n(π/(n+2)) > 0 > F_n(π/n)`.
-/
import ChiquipoliFamily.Interval.Root

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real Set Filter Topology

/-! ## At most one zero -/

/-- Right of a zero with negative derivative the function is negative, left of it positive. -/
lemma neg_right_of_deriv_neg {f : ℝ → ℝ} {d z : ℝ} (hD : HasDerivAt f d z) (hd : d < 0) (h0 : f z = 0) :
    ∃ u > z, ∀ t ∈ Ioo z u, f t < 0 := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hD
  have ev : ∀ᶠ t in 𝓝[≠] z, slope f z t < 0 := hs.eventually (Iio_mem_nhds hd)
  have ev' : ∀ᶠ t in 𝓝[>] z, f t < 0 := by
    have hle : 𝓝[>] z ≤ 𝓝[≠] z := nhdsWithin_mono z (fun t ht => ne_of_gt ht)
    filter_upwards [ev.filter_mono hle, self_mem_nhdsWithin] with t hsl ht
    rw [slope_def_field, h0, sub_zero] at hsl
    have htz : 0 < t - z := sub_pos.mpr ht
    exact (div_neg_iff.mp hsl).elim (fun h => absurd h.2 (not_lt.mpr htz.le)) (fun h => h.1)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp ev'
  exact ⟨u, hu, fun t ht => hsub ht⟩

lemma pos_left_of_deriv_neg {f : ℝ → ℝ} {d z : ℝ} (hD : HasDerivAt f d z) (hd : d < 0) (h0 : f z = 0) :
    ∃ l < z, ∀ t ∈ Ioo l z, 0 < f t := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hD
  have ev : ∀ᶠ t in 𝓝[≠] z, slope f z t < 0 := hs.eventually (Iio_mem_nhds hd)
  have ev' : ∀ᶠ t in 𝓝[<] z, 0 < f t := by
    have hle : 𝓝[<] z ≤ 𝓝[≠] z := nhdsWithin_mono z (fun t ht => ne_of_lt ht)
    filter_upwards [ev.filter_mono hle, self_mem_nhdsWithin] with t hsl ht
    rw [slope_def_field, h0, sub_zero] at hsl
    have htz : t - z < 0 := sub_neg.mpr ht
    exact (div_neg_iff.mp hsl).elim (fun h => h.1) (fun h => absurd h.2 (not_lt.mpr htz.le))
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp ev'
  exact ⟨l, hl, fun t ht => hsub ht⟩

/-- **At most one zero.** A function continuous on an open interval, with a negative
derivative at each of its zeros there, has at most one zero there. -/
theorem at_most_one_zero {f f' : ℝ → ℝ} {lo hi : ℝ} (hc : ContinuousOn f (Ioo lo hi))
    (hd : ∀ z ∈ Ioo lo hi, f z = 0 → HasDerivAt f (f' z) z ∧ f' z < 0) :
    ∀ z1 ∈ Ioo lo hi, ∀ z2 ∈ Ioo lo hi, f z1 = 0 → f z2 = 0 → z1 = z2 := by
  intro z1 h1 z2 h2 f1 f2
  by_contra hne
  wlog hlt : z1 < z2 generalizing z1 z2
  · exact this z2 h2 z1 h1 f2 f1 (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
  obtain ⟨u, hu, hR⟩ := neg_right_of_deriv_neg (hd z1 h1 f1).1 (hd z1 h1 f1).2 f1
  set b := (z1 + min u z2) / 2 with hb
  have hzb : z1 < b := by have := lt_min hu hlt; rw [hb]; linarith
  have hbu : b < min u z2 := by have := lt_min hu hlt; rw [hb]; linarith
  have hbz2 : b < z2 := lt_of_lt_of_le hbu (min_le_right _ _)
  have fb : f b < 0 := hR b ⟨hzb, lt_of_lt_of_le hbu (min_le_left _ _)⟩
  have hsub : Icc b z2 ⊆ Ioo lo hi := fun t ht => ⟨lt_of_lt_of_le (lt_trans h1.1 hzb) ht.1, lt_of_le_of_lt ht.2 h2.2⟩
  set S := Icc b z2 ∩ f ⁻¹' {0} with hS
  have hSc : IsClosed S := (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hz2S : z2 ∈ S := ⟨⟨hbz2.le, le_rfl⟩, f2⟩
  have hbdd : BddBelow S := ⟨b, fun t ht => ht.1.1⟩
  set s := sInf S with hs
  have hsS : s ∈ S := hSc.csInf_mem ⟨z2, hz2S⟩ hbdd
  have hbs : b < s := lt_of_le_of_ne hsS.1.1 (fun h => by have := hsS.2; rw [← h] at this; simp at this; linarith)
  have hsI : s ∈ Ioo lo hi := hsub hsS.1
  -- f < 0 on (b, s): a positive value there would give, by continuity, an earlier zero
  have hneg : ∀ t ∈ Ioo b s, f t < 0 := by
    intro t ht
    by_contra hpos
    push Not at hpos
    rcases hpos.lt_or_eq with hp | hp
    · have hcb : ContinuousOn f (Icc b t) := hc.mono (fun x hx => hsub ⟨hx.1, le_trans hx.2 (le_trans ht.2.le hsS.1.2)⟩)
      obtain ⟨c, hcI, hc0⟩ := intermediate_value_Ioo ht.1.le hcb ⟨fb, hp⟩
      have hcS : c ∈ S := ⟨⟨hcI.1.le, le_trans hcI.2.le (le_trans ht.2.le hsS.1.2)⟩, hc0⟩
      have := csInf_le hbdd hcS
      linarith [hcI.2, ht.2]
    · have htS : t ∈ S := ⟨⟨ht.1.le, le_trans ht.2.le hsS.1.2⟩, hp.symm⟩
      have := csInf_le hbdd htS
      linarith [ht.2]
  obtain ⟨l, hl, hL⟩ := pos_left_of_deriv_neg (hd s hsI hsS.2).1 (hd s hsI hsS.2).2 hsS.2
  set t := (max l b + s) / 2
  have hmax : max l b < s := max_lt hl hbs
  have ht1 : max l b < t := by show max l b < (max l b + s) / 2; linarith
  have ht2 : t < s := by show (max l b + s) / 2 < s; linarith
  have := hL t ⟨lt_of_le_of_lt (le_max_left _ _) ht1, ht2⟩
  have := hneg t ⟨lt_of_le_of_lt (le_max_right _ _) ht1, ht2⟩
  linarith

/-! ## Localisation and the endpoint values -/

/-- `y = 2x + sin((n/2−1)t)`, so that `F = y² + cos²((n/2−1)t) − 4 sin²(t/2)`. -/
noncomputable def yy (n : ℕ) (t : ℝ) : ℝ := 2 * Optigon.x n t + sin (((n : ℝ) / 2 - 1) * t)

lemma F_eq_yy (n : ℕ) (t : ℝ) :
    Optigon.F n t = yy n t ^ 2 + cos (((n : ℝ) / 2 - 1) * t) ^ 2 - 4 * sin (t / 2) ^ 2 := rfl

lemma pi_div_le_small {n : ℕ} (hn : 16 ≤ n) : π / n ≤ π / 16 := by
  have : (16 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left pi_pos.le (by norm_num) this

/-- **Localisation.** At a zero `z ∈ (0, π/n)`: `z ≥ π/(n−2+π)` and `|y(z)| ≤ 2 sin²(z/2)`. -/
theorem loc (n : ℕ) (hn : 16 ≤ n) {z : ℝ} (hz0 : 0 < z) (hz1 : z < π / n) (hF : Optigon.F n z = 0) :
    π / ((n : ℝ) - 2 + π) ≤ z ∧ |yy n z| ≤ 2 * sin (z / 2) ^ 2 := by
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < n := by linarith
  set A := (n : ℝ) / 2 - 1 with hA
  have hA0 : 0 < A := by rw [hA]; linarith
  have hNz : (n : ℝ) * z < π := by rwa [lt_div_iff₀ hNpos, mul_comm] at hz1
  have haz : A * z < π / 2 - z := by rw [hA]; nlinarith
  have haz0 : 0 ≤ A * z := by positivity
  have hzsmall : z < π / 16 := lt_of_lt_of_le hz1 (pi_div_le_small hn)
  have hpi := pi_pos
  have hsin : 0 < sin z := sin_pos_of_pos_of_lt_pi hz0 (by linarith)
  have hcos : sin z ≤ cos (A * z) := by
    rw [← cos_pi_div_two_sub]
    exact cos_le_cos_of_nonneg_of_le_pi haz0 (by linarith) haz.le
  have hsh : 0 < sin (z / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [F_eq_yy] at hF
  have hc2 : cos (A * z) ^ 2 ≤ (2 * sin (z / 2)) ^ 2 := by nlinarith [sq_nonneg (yy n z)]
  have hcl : cos (A * z) ≤ 2 * sin (z / 2) := by
    by_contra h; push Not at h; nlinarith [hcos, hsin]
  have hlz : 2 * sin (z / 2) ≤ z := by have := sin_le (show 0 ≤ z / 2 by linarith); linarith
  have hj := mul_le_sin (show 0 ≤ π / 2 - A * z by linarith) (by linarith)
  rw [sin_pi_div_two_sub] at hj
  constructor
  · rw [div_le_iff₀ (by linarith)]
    have h1 : 2 / π * (π / 2 - A * z) ≤ z := le_trans hj (le_trans hcl hlz)
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at h1
    rw [hA] at h1
    nlinarith
  · -- y² = (2 sin(z/2))² − cos² ≤ (2 sin(z/2))² − sin² z = (2 sin²(z/2))²
    have hsz : sin z = 2 * sin (z / 2) * cos (z / 2) := by rw [← sin_two_mul]; ring_nf
    have hpy := sin_sq_add_cos_sq (z / 2)
    have hy2 : yy n z ^ 2 ≤ (2 * sin (z / 2) ^ 2) ^ 2 := by
      have : yy n z ^ 2 = 4 * sin (z / 2) ^ 2 - cos (A * z) ^ 2 := by linarith
      rw [this]
      have : sin z ^ 2 ≤ cos (A * z) ^ 2 := by nlinarith
      rw [hsz] at this
      nlinarith
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (yy n z + 2 * sin (z / 2) ^ 2), sq_nonneg (sin (z / 2))],
                      by nlinarith [sq_nonneg (yy n z - 2 * sin (z / 2) ^ 2), sq_nonneg (sin (z / 2))]⟩

/-- `F_n(π/(n+2)) > 0`. -/
theorem F_left_pos (n : ℕ) (hn : 16 ≤ n) : 0 < Optigon.F n (π / ((n : ℝ) + 2)) := by
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn
  set t := π / ((n : ℝ) + 2) with ht
  have hpi := pi_pos
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ π / 18 := div_le_div_of_nonneg_left hpi.le (by norm_num) (by linarith)
  have hA : ((n : ℝ) / 2 - 1) * t = π / 2 - 2 * t := by rw [ht]; field_simp; ring
  rw [F_eq_yy, hA, cos_pi_div_two_sub]
  have hs2 : sin (2 * t) = 4 * sin (t / 2) * cos (t / 2) * cos t := by
    rw [sin_two_mul, show sin t = sin (2 * (t / 2)) by ring_nf, sin_two_mul]; ring
  have hsh : 0 < sin (t / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_gt_three])
  have hc1 := one_sub_sq_div_two_le_cos (x := t)
  have hc2 := one_sub_sq_div_two_le_cos (x := t / 2)
  have hpi4 := pi_lt_d2
  have ht18 : t < 0.175 := by linarith
  have hct : (0.98 : ℝ) ≤ cos t := by nlinarith
  have hct2 : (0.99 : ℝ) ≤ cos (t / 2) := by nlinarith
  have hcos : 1 < 2 * cos (t / 2) * cos t := by nlinarith [mul_le_mul hct2 hct (by norm_num) (by linarith)]
  have hbig : 2 * sin (t / 2) < sin (2 * t) := by rw [hs2]; nlinarith
  have hsq : (2 * sin (t / 2)) ^ 2 < sin (2 * t) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (yy n t)]

/-- `F_n(π/n) = −4 sin t (1 − cos t)² (cos 2t − sin t) / cos² 2t`, `t = π/n`. -/
theorem F_right_closed (n : ℕ) (hn : 16 ≤ n) :
    Optigon.F n (π / n) = -(4 * sin (π / n) * (1 - cos (π / n)) ^ 2 * (cos (2 * (π / n)) - sin (π / n)))
      / cos (2 * (π / n)) ^ 2 := by
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
  unfold Optigon.F Optigon.x
  rw [e1, e2, e3, mul_assoc (2 * cos t - 1), hq, sin_pi_div_two_sub, cos_pi_div_two_sub]
  have h2 : (2 * sin (t / 2)) ^ 2 = 2 - 2 * cos t := sq_two_sin_half' t
  have hs := sin_sq_add_cos_sq t
  have h4 : 4 * sin (t / 2) ^ 2 = 2 - 2 * cos t := by nlinarith [h2]
  rw [h4]
  rw [cos_two_mul] at hD
  rw [cos_two_mul, sin_two_mul]
  field_simp
  linear_combination (2 * cos t ^ 2 - 1) ^ 2 * hs

/-! ## Simplicity -/

/-- `y' = 2 x' + (n/2−1) cos((n/2−1)t)`. -/
noncomputable def yd (n : ℕ) (t : ℝ) : ℝ := 2 * xd n t + cos (((n : ℝ) / 2 - 1) * t) * ((n : ℝ) / 2 - 1)

lemma Fd_eq (n : ℕ) (t : ℝ) :
    Fd n t = 2 * yy n t * yd n t - ((n : ℝ) / 2 - 1) * sin (((n : ℝ) - 2) * t) - 2 * sin t := by
  have h : ((n : ℝ) - 2) * t = 2 * (((n : ℝ) / 2 - 1) * t) := by ring
  unfold Fd yy yd
  rw [h, sin_two_mul]
  ring

/-- Bounds on `J_n = [π/(n+2), π/n]`. -/
lemma J_facts (n : ℕ) (hn : 16 ≤ n) {t : ℝ} (ht1 : π / ((n : ℝ) + 2) ≤ t) (ht2 : t ≤ π / n) :
    0 < t ∧ t ≤ π / 16 ∧ (0.92 : ℝ) ≤ cos (2 * t) ∧ (n : ℝ) * t ≤ π ∧ π ≤ ((n : ℝ) + 2) * t := by
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := pi_pos
  have hpi4 := pi_lt_d2
  have h0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hs : t ≤ π / 16 := le_trans ht2 (pi_div_le_small hn)
  refine ⟨h0, hs, ?_, ?_, ?_⟩
  · have := one_sub_sq_div_two_le_cos (x := 2 * t)
    have : (2 * t) ^ 2 ≤ (π / 8) ^ 2 := by nlinarith
    nlinarith
  · rwa [le_div_iff₀ (by linarith), mul_comm] at ht2
  · rwa [div_le_iff₀ (by linarith), mul_comm] at ht1

/-- The quotient-rule term of `x'`, bounded by its pieces. -/
lemma quot_bound {C s g K G D s2 : ℝ} (hC : |C| ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 0.2) (hg : |g| ≤ 1)
    (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hG0 : 0 ≤ G) (hG1 : G ≤ 3.4) (hD : 0.92 ≤ D)
    (hs2 : 0 ≤ s2) (hs2' : s2 ≤ 0.4) :
    |C - (((-(2 * s)) * g + K * G) * D - K * g * (-(s2 * 2))) / D ^ 2| ≤ 6.2 := by
  have hgl := abs_le.mp hg
  set X := (-(2 * s)) * g + K * G with hX
  have hX1 : |X| ≤ 3.8 := by
    have h1 : |(-(2 * s)) * g| ≤ 0.4 := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * s)]
      nlinarith [abs_nonneg g]
    have h2 : |K * G| ≤ 3.4 := by
      rw [abs_mul, abs_of_nonneg hK0, abs_of_nonneg hG0]; nlinarith
    have := abs_add_le ((-(2 * s)) * g) (K * G)
    linarith
  have hY : |K * g * (-(s2 * 2))| ≤ 0.8 := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hK0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s2 * 2)]
    have : K * |g| ≤ 1 := by nlinarith [abs_nonneg g]
    nlinarith [abs_nonneg g, mul_nonneg hK0 (abs_nonneg g)]
  have hDp : 0 < D := by linarith
  have hE : |X * D - K * g * (-(s2 * 2))| ≤ 3.8 * D + 0.8 := by
    have := abs_sub (X * D) (K * g * (-(s2 * 2)))
    rw [abs_mul, abs_of_pos hDp] at this
    nlinarith
  have hQ : |(X * D - K * g * (-(s2 * 2))) / D ^ 2| ≤ 5.2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < D ^ 2), div_le_iff₀ (by positivity)]
    nlinarith
  have := abs_sub C ((X * D - K * g * (-(s2 * 2))) / D ^ 2)
  linarith

/-- `|x'| ≤ 6.2` on `J_n`. -/
theorem xd_bound (n : ℕ) (hn : 16 ≤ n) {t : ℝ} (ht1 : π / ((n : ℝ) + 2) ≤ t) (ht2 : t ≤ π / n) :
    |xd n t| ≤ 6.2 := by
  obtain ⟨h0, hs, hD, hNt, hNt2⟩ := J_facts n hn ht1 ht2
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := pi_pos
  have hpi4 := pi_lt_d2
  have hpi3 := pi_gt_three
  have hD1 := cos_le_one (2 * t)
  -- g' = ((A − 1) cos((A − 1)t) + 2 cos 2t) / 2, A = n/2 − 1
  have hg' : -(sin (((n : ℝ) / 4 - 2) * t) * ((n : ℝ) / 4 - 2)) * sin ((n : ℝ) / 4 * t)
      + cos (((n : ℝ) / 4 - 2) * t) * (cos ((n : ℝ) / 4 * t) * ((n : ℝ) / 4))
      = (((n : ℝ) / 2 - 2) * cos (((n : ℝ) / 2 - 2) * t) + 2 * cos (2 * t)) / 2 := by
    have e1 : ((n : ℝ) / 2 - 2) * t = ((n : ℝ) / 4 - 2) * t + (n : ℝ) / 4 * t := by ring
    have e2 : 2 * t = (n : ℝ) / 4 * t - ((n : ℝ) / 4 - 2) * t := by ring
    rw [e1, e2, cos_add, cos_sub]
    ring
  have hB0 : 0 ≤ (n : ℝ) / 2 - 2 := by linarith
  have hBt0 : 0 ≤ ((n : ℝ) / 2 - 2) * t := mul_nonneg hB0 h0.le
  have hBt1 : ((n : ℝ) / 2 - 2) * t ≤ π / 2 := by nlinarith
  have hcosB : 0 ≤ cos (((n : ℝ) / 2 - 2) * t) := cos_nonneg_of_mem_Icc ⟨by linarith, hBt1⟩
  have hcosB' : cos (((n : ℝ) / 2 - 2) * t) ≤ π / 2 - ((n : ℝ) / 2 - 2) * t := by
    rw [← sin_pi_div_two_sub]; exact sin_le (by linarith)
  have hBcos : ((n : ℝ) / 2 - 2) * cos (((n : ℝ) / 2 - 2) * t) ≤ 3 * π / 2 := by
    have h1 : ((n : ℝ) / 2 - 2) * (π / 2 - ((n : ℝ) / 2 - 2) * t) ≤ 3 * π / 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcosB' hB0]
  have hs1 : 0 ≤ sin t := (sin_pos_of_pos_of_lt_pi h0 (by linarith)).le
  have hs1' : sin t ≤ 0.2 := by have := sin_le h0.le; linarith
  have hs2 : 0 ≤ sin (2 * t) := (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le
  have hs2' : sin (2 * t) ≤ 0.4 := by have := sin_le (show 0 ≤ 2 * t by linarith); linarith
  have hct := cos_le_one t
  have hct' : (0.9 : ℝ) ≤ cos t := by
    have := one_sub_sq_div_two_le_cos (x := t); nlinarith
  have hg1 : |cos (((n : ℝ) / 4 - 2) * t) * sin ((n : ℝ) / 4 * t)| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ (abs_cos_le_one _) (abs_nonneg _) (abs_sin_le_one _)
  unfold xd
  simp only []
  rw [hg']
  exact quot_bound (abs_cos_le_one t) hs1 hs1' hg1 (by linarith) (by linarith)
    (by nlinarith [mul_nonneg hB0 hcosB]) (by linarith) hD hs2 hs2'

/-- `|y'| ≤ 16` on `J_n`. -/
theorem yd_bound (n : ℕ) (hn : 16 ≤ n) {t : ℝ} (ht1 : π / ((n : ℝ) + 2) ≤ t) (ht2 : t ≤ π / n) :
    |yd n t| ≤ 16 := by
  obtain ⟨h0, hs, hD, hNt, hNt2⟩ := J_facts n hn ht1 ht2
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi4 := pi_lt_d2
  have hx := xd_bound n hn ht1 ht2
  have hA0 : 0 ≤ (n : ℝ) / 2 - 1 := by linarith
  have hAt0 : 0 ≤ ((n : ℝ) / 2 - 1) * t := mul_nonneg hA0 h0.le
  have hAt1 : ((n : ℝ) / 2 - 1) * t ≤ π / 2 := by nlinarith
  have hcosA : 0 ≤ cos (((n : ℝ) / 2 - 1) * t) := cos_nonneg_of_mem_Icc ⟨by linarith, hAt1⟩
  have hcosA' : cos (((n : ℝ) / 2 - 1) * t) ≤ π / 2 - ((n : ℝ) / 2 - 1) * t := by
    rw [← sin_pi_div_two_sub]; exact sin_le (by linarith)
  have hAcos : cos (((n : ℝ) / 2 - 1) * t) * ((n : ℝ) / 2 - 1) ≤ π := by
    have h1 : ((n : ℝ) / 2 - 1) * (π / 2 - ((n : ℝ) / 2 - 1) * t) ≤ π := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcosA' hA0]
  unfold yd
  have := abs_add_le (2 * xd n t) (cos (((n : ℝ) / 2 - 1) * t) * ((n : ℝ) / 2 - 1))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (mul_nonneg hcosA hA0)] at this
  linarith

/-- `(n/2−1) sin((n−2)t) + 2 sin t ≥ 2.6` on `J_n`. -/
theorem main_term (n : ℕ) (hn : 16 ≤ n) {t : ℝ} (ht1 : π / ((n : ℝ) + 2) ≤ t) (ht2 : t ≤ π / n) :
    2.6 ≤ ((n : ℝ) / 2 - 1) * sin (((n : ℝ) - 2) * t) + 2 * sin t := by
  obtain ⟨h0, hs, hD, hNt, hNt2⟩ := J_facts n hn ht1 ht2
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := pi_pos
  have hpi4 := pi_lt_d2
  have hpi314 := pi_gt_d2
  -- sin((n−2)t) = sin(π − (n−2)t) ≥ sin 2t
  have hsin : sin (2 * t) ≤ sin (((n : ℝ) - 2) * t) := by
    rw [← sin_pi_sub (((n : ℝ) - 2) * t)]
    apply sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by nlinarith) (by nlinarith)
  have hs1 : 0 < sin t := sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hct := cos_le_one t
  have hct0 : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hA : 0 ≤ (n : ℝ) / 2 - 1 := by linarith
  have step1 : ((n : ℝ) / 2 - 1) * sin (2 * t) + 2 * sin t ≤ ((n : ℝ) / 2 - 1) * sin (((n : ℝ) - 2) * t) + 2 * sin t := by
    nlinarith [mul_le_mul_of_nonneg_left hsin hA]
  have step2 : (n : ℝ) / 2 * sin (2 * t) ≤ ((n : ℝ) / 2 - 1) * sin (2 * t) + 2 * sin t := by
    rw [sin_two_mul]; nlinarith [mul_nonneg hs1.le (sub_nonneg.mpr hct)]
  have hcube := sin_gt_sub_cube (show 0 < 2 * t by linarith)
  have hNt3 : 7 * π / 8 ≤ (n : ℝ) * t := by nlinarith
  have htt : t ^ 2 ≤ (π / 16) ^ 2 := by nlinarith
  have step3 : 2.6 ≤ (n : ℝ) / 2 * sin (2 * t) := by
    have : (n : ℝ) / 2 * (2 * t - (2 * t) ^ 3 / 6) ≤ (n : ℝ) / 2 * sin (2 * t) :=
      mul_le_mul_of_nonneg_left hcube.le (by linarith)
    have e : (n : ℝ) / 2 * (2 * t - (2 * t) ^ 3 / 6) = (n : ℝ) * t * (1 - 2 / 3 * t ^ 2) := by ring
    rw [e] at this
    have h2 : (0.97 : ℝ) ≤ 1 - 2 / 3 * t ^ 2 := by nlinarith
    nlinarith [mul_le_mul hNt3 h2 (by norm_num) (by nlinarith)]
  linarith

/-- **Simplicity.** At every zero of `F_n` in `(0, π/n)`, `Fd < 0`. -/
theorem Fd_neg_at_zero (n : ℕ) (hn : 16 ≤ n) {z : ℝ} (hz0 : 0 < z) (hz1 : z < π / n) (hF : Optigon.F n z = 0) :
    Fd n z < 0 := by
  obtain ⟨hloc, hy⟩ := loc n hn hz0 hz1 hF
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := pi_pos
  have hpi4 := pi_lt_d2
  have ht1 : π / ((n : ℝ) + 2) ≤ z := le_trans (div_le_div_of_nonneg_left hpi.le (by linarith) (by linarith [pi_lt_four])) hloc
  have hyd := yd_bound n hn ht1 hz1.le
  have hM := main_term n hn ht1 hz1.le
  have hsmall : z ≤ π / 16 := le_trans hz1.le (pi_div_le_small hn)
  have hsh := sin_le (show 0 ≤ z / 2 by linarith)
  have hsh0 : 0 ≤ sin (z / 2) := (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le
  have hsq : sin (z / 2) ^ 2 ≤ 0.0097 := by nlinarith
  rw [Fd_eq]
  have h2 : 2 * yy n z * yd n z ≤ 2 * (2 * sin (z / 2) ^ 2) * 16 := by
    have := abs_mul (yy n z) (yd n z)
    have h3 : |yy n z * yd n z| ≤ 2 * sin (z / 2) ^ 2 * 16 := by
      rw [abs_mul]; exact mul_le_mul hy hyd (abs_nonneg _) (by positivity)
    nlinarith [le_abs_self (yy n z * yd n z)]
  nlinarith

/-! ## The theorem -/

/-- **The zero of `F_n`, for every `n ≥ 16`.** `F_n` has exactly one zero `z` in
`(0, π/n)`; it lies in `(π/(n+2), π/n)` and it is simple. -/
theorem root_all (n : ℕ) (hn : 16 ≤ n) :
    ∃ z : ℝ, z ∈ Ioo (π / ((n : ℝ) + 2)) (π / n) ∧ Optigon.F n z = 0 ∧ Fd n z < 0 ∧
      ∀ z' ∈ Ioo 0 (π / n), Optigon.F n z' = 0 → z' = z := by
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := pi_pos
  have hpi4 := pi_lt_d2
  have hlt : π / ((n : ℝ) + 2) < π / n := div_lt_div_of_pos_left hpi (by linarith) (by linarith)
  have hsmall := pi_div_le_small hn
  have hcos : ∀ t ∈ Icc (π / ((n : ℝ) + 2)) (π / n), cos (2 * t) ≠ 0 := by
    intro t ht
    have : 0 < π / ((n : ℝ) + 2) := by positivity
    exact cos_two_ne (by linarith [ht.1]) (by linarith [ht.2])
  have hcont := F_continuousOn n _ _ hcos
  have hL := F_left_pos n hn
  have hR : Optigon.F n (π / n) < 0 := by
    rw [F_right_closed n hn]
    set t := π / (n : ℝ)
    have h0 : 0 < t := by positivity
    have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi h0 (by linarith)
    have hc : cos t < 1 := by
      have := cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith) h0
      rwa [cos_zero] at this
    have hc2 : sin t < cos (2 * t) := by
      have := one_sub_sq_div_two_le_cos (x := 2 * t)
      have := sin_le h0.le
      nlinarith
    have hD : 0 < cos (2 * t) := by linarith
    apply div_neg_of_neg_of_pos _ (by positivity)
    have : 0 < 4 * sin t * (1 - cos t) ^ 2 * (cos (2 * t) - sin t) := by
      have := sq_pos_of_pos (sub_pos.mpr hc)
      have := sub_pos.mpr hc2
      positivity
    linarith
  obtain ⟨z, hz, hFz⟩ := intermediate_value_Ioo' hlt.le hcont ⟨hR, hL⟩
  have hz0 : 0 < z := lt_trans (by positivity) hz.1
  refine ⟨z, hz, hFz, Fd_neg_at_zero n hn hz0 hz.2 hFz, ?_⟩
  -- uniqueness on (0, π/n)
  have hcont' : ContinuousOn (Optigon.F n) (Ioo 0 (π / n)) := by
    intro t ht
    exact (hasDerivAt_F n t (cos_two_ne ht.1 (by linarith [ht.2]))).continuousAt.continuousWithinAt
  have hd : ∀ w ∈ Ioo 0 (π / (n : ℝ)), Optigon.F n w = 0 → HasDerivAt (Optigon.F n) (Fd n w) w ∧ Fd n w < 0 :=
    fun w hw hFw => ⟨hasDerivAt_F n w (cos_two_ne hw.1 (by linarith [hw.2])), Fd_neg_at_zero n hn hw.1 hw.2 hFw⟩
  intro z' hz' hF'
  exact at_most_one_zero hcont' hd z' hz' z ⟨hz0, hz.2⟩ hF' hFz

end Chiquipoli.Family.Trig
