/-
# Problem 1: the angle of every side, and convexity, for every `n = 16k`

`sideAng k z β x` is the direction of side `x → x + 1` of the published polygon
(`side_all`):
* first half: `θ_j + z/2 + π/2` on the `a`-sides and `3π/2 + z/2 + θ_j` on the
  `t`-sides, where `j` is the step of the strip that creates the side;
* second half: the mirror images;
* closing sides: `π/2 − β` and `3π/2 + β`, with `β = arctan(a / sin φ)`.
Along the labels these angles increase and span less than `2π`
(`sideAng_mono`, `sideAng_span`), so the polygon is convex (`convex_all`).
-/
import ChiquipoliFamily.AllN.Feasibility.Sides

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Chiquipoli.Family.Trig.P1

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Chiquipoli.Family.Trig.RungVec
  Chiquipoli.Family.Trig.P3

/-- The step of the strip that creates side `s` (first half), in closed form. -/
def jA (k a : ℕ) : ℕ := JhiA a - 8 * k - 1
def jT (k x : ℕ) : ℕ := JhiT (x - 8 * k) - 8 * k - 1

/-- The direction of side `x`. -/
noncomputable def sideAng (k : ℕ) (z β : ℝ) (x : ℕ) : ℝ :=
  if x ≤ 4 * k - 2 then π / 2 - z / 2 - θ k z (jT k (16 * k - 1 - x))
  else if x = 4 * k - 1 then π / 2 - β
  else if x ≤ 8 * k - 1 then θ k z (jA k x) + z / 2 + π / 2
  else if x ≤ 12 * k - 1 then 3 * π / 2 - z / 2 - θ k z (jA k (16 * k - 1 - x))
  else if x = 12 * k then 3 * π / 2 + β
  else 3 * π / 2 + z / 2 + θ k z (jT k x)

lemma e_add_pi_div_two (t : ℝ) : e (t + π / 2) = (-sin t, cos t) := by
  simp [e, cos_add_pi_div_two, sin_add_pi_div_two]

lemma e_add_three_pi_div_two (t : ℝ) : e (t + 3 * π / 2) = (sin t, -cos t) := by
  have h : t + 3 * π / 2 = (t + π / 2) + π := by ring
  rw [h]; simp [e, cos_add_pi, sin_add_pi, cos_add_pi_div_two, sin_add_pi_div_two]

/-- `e(θ_{j+1}) − e(θ_j) = ℓ e(θ_j + z/2 + π/2)`. -/
lemma e_step (k : ℕ) (z : ℝ) (j : ℕ) :
    e (θ k z (j + 1)) - e (θ k z j) = (2 * sin (z / 2)) • e (θ k z j + z / 2 + π / 2) := by
  rw [← θ_succ, e_diff, e_add_pi_div_two]

lemma mir_smul_e (l a : ℝ) : -mir (l • e a) = l • e (2 * π - a) := by
  simp only [mir, e, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_neg, Prod.snd_neg,
    cos_two_pi_sub, sin_two_pi_sub]
  constructor <;> ring

/-- `ℓ (sin β, cos β) = (a, s)` for `β = arctan(a/s)`, when `ℓ² = a² + s²`. -/
lemma arctan_vec (a s l : ℝ) (hs : 0 < s) (hl : 0 < l) (h : l ^ 2 = a ^ 2 + s ^ 2) :
    l * sin (arctan (a / s)) = a ∧ l * cos (arctan (a / s)) = s := by
  have hq : √(1 + (a / s) ^ 2) = l / s := by
    rw [show 1 + (a / s) ^ 2 = (l / s) ^ 2 by field_simp; linarith]
    exact Real.sqrt_sq (by positivity)
  rw [sin_arctan, cos_arctan, hq]
  constructor <;> field_simp

lemma JhiA_strict (a b : ℕ) (h : a < b) : JhiA a < JhiA b := by unfold JhiA; split_ifs <;> omega
lemma JhiT_strict (a b : ℕ) (h : a < b) : JhiT a < JhiT b := by unfold JhiT; split_ifs <;> omega

lemma θ_strict (k : ℕ) {z : ℝ} (hz : 0 < z) {i j : ℕ} (h : i < j) : θ k z i < θ k z j := by
  unfold θ; have : (i : ℝ) < j := by exact_mod_cast h
  nlinarith

lemma θ_val (k : ℕ) (z : ℝ) (j : ℕ) (hj : j ≤ 8 * k) : θ k z j = π / 2 - ((8 * k - 1 - j : ℤ) : ℝ) * z := by
  unfold θ φ; push_cast; ring

lemma JhiT_ge (t : ℕ) (k : ℕ) (h : 4 * k + 1 ≤ t) : 8 * k + 2 ≤ JhiT t := by unfold JhiT; split_ifs <;> omega
lemma JhiA_ge (a : ℕ) (k : ℕ) (h : 4 * k ≤ a) : 8 * k + 1 ≤ JhiA a := by
  unfold JhiA; split_ifs <;> omega

section all
variable {k : ℕ} (hk : 2 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ}
  (hz0 : 0 < z) (hz1 : z < π / n) (hF : Optigon.F n z = 0)
include hk hn hz0 hz1 hF

/-- The width of the gap and its angle. -/
noncomputable def gapβ : ℝ :=
  arctan (gapA (show 1 ≤ k by omega) hn (z := z) / sin (φ k z))

lemma basic_facts : cos (2 * z) ≠ 0 ∧ 0 < sin (φ k z) ∧ 0 < 2 * sin (z / 2) ∧
    z < π / 32 ∧ 16 * (k : ℝ) * z < π := by
  have hN : (32 : ℝ) ≤ n := by
    have : 32 ≤ n := by omega
    exact_mod_cast this
  have hpi := pi_pos
  have hz32 : z < π / 32 := lt_of_lt_of_le hz1 (div_le_div_of_nonneg_left hpi.le (by norm_num) hN)
  have hkz : 16 * (k : ℝ) * z < π := by
    have := hz1; rw [lt_div_iff₀ (by linarith)] at this
    have e : (n : ℝ) = 16 * k := by rw [hn]; push_cast; ring
    rw [e] at this; linarith
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨(cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne', ?_, ?_, hz32, hkz⟩
  · unfold φ; apply sin_pos_of_pos_of_lt_pi <;> nlinarith
  · have := sin_pos_of_pos_of_lt_pi (show 0 < z / 2 by linarith) (by linarith); linarith

/-- **Every side, as `ℓ e(α)`.** -/
theorem side_all (x : Fin n) :
    Qc n z (x + 1) - Qc n z x = (2 * sin (z / 2)) • e (sideAng k z (gapβ hk hn (z := z)) x.val) := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hc, hsφ, hl, hz32, hkz⟩ := basic_facts hk hn hz0 hz1 hF
  set l := 2 * sin (z / 2) with hldef
  set β := gapβ hk hn (z := z) with hβ
  have hx := x.isLt
  -- the mirror of a side
  have hmir : ∀ y : Fin n, Qc n z (-y - 1 + 1) - Qc n z (-y - 1) = -mir (Qc n z (y + 1) - Qc n z y) := by
    intro y
    rw [sub_add_cancel, show -y - 1 = -(y + 1) by abel, Qc_neg k hk1 hn z, Qc_neg k hk1 hn z, ← mir_sub]
    abel
  have hneg : ∀ y : Fin n, (-y - 1).val = n - 1 - y.val := fun y => neg_sub_one_val y (by omega)
  have hRe : ∀ y : Fin n, 12 * k + 1 ≤ y.val →
      Qc n z (y + 1) - Qc n z y = l • e (θ k z (jT k y.val) + z / 2 + 3 * π / 2) := by
    intro y hy
    rw [side_R hk1 hn hc y hy, e_step, ← neg_smul, show θ k z (jT k y.val) + z / 2 + 3 * π / 2
      = (θ k z (JhiT (y.val - 8 * k) - 8 * k - 1) + z / 2) + 3 * π / 2 by rfl, e_add_three_pi_div_two,
      e_add_pi_div_two]
    simp only [Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_neg, Prod.snd_neg]
    constructor <;> ring
  have hLe : ∀ y : Fin n, 4 * k ≤ y.val → y.val ≤ 8 * k - 1 →
      Qc n z (y + 1) - Qc n z y = l • e (θ k z (jA k y.val) + z / 2 + π / 2) := by
    intro y h1 h2
    rw [side_L hk1 hn hc y h1 h2, e_step]; rfl
  -- the gap
  have hw : sin (z / 2) ≠ 0 := by intro h; rw [hldef, h] at hl; linarith
  have hcw : cos (z / 2) ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩).ne'
  have hAB := gap_AB hk1 hn hc hw hcw
  have hCD := gap_CD hk1 hn hc hw hcw
  set ag := gapA hk1 hn (z := z) with hag
  -- `ℓ² = a² + sin² φ`: the closing side has length `ℓ` at the root
  have hl2 : l ^ 2 = ag ^ 2 + sin (φ k z) ^ 2 := by
    have h := closing_all z k hk1 hn (vB hk1 hn) rfl
    rw [hF, zero_add, show vB hk1 hn + 1 = vA hk1 hn from Fin.ext (by
      rw [fin_add_one_val' _ (by simp only [vB]; omega)]; simp only [vA, vB]; omega)] at h
    rw [hldef, ← h, nsq_eq, hAB, hag, gapA]
  obtain ⟨hβs, hβc⟩ := arctan_vec ag (sin (φ k z)) l hsφ hl hl2
  have hβdef : β = arctan (ag / sin (φ k z)) := rfl
  obtain ⟨v, hv⟩ : ∃ v, x.val = v := ⟨_, rfl⟩
  rw [hv]
  -- the mirrored sides: `x = −y − 1`
  have hxy : ∀ y : Fin n, y.val = 16 * k - 1 - v → x = -y - 1 := by
    intro y hy; apply Fin.ext; rw [hneg y, hy, hv]; omega
  rcases Nat.lt_or_ge v (4 * k - 1) with r1 | r1
  · set y : Fin n := ⟨16 * k - 1 - v, by omega⟩
    rw [hxy y rfl, hmir y, hRe y (by simp only [y]; omega), mir_smul_e]
    unfold sideAng; rw [if_pos (by omega)]
    congr 2; simp only [y]; ring
  rcases Nat.eq_or_lt_of_le r1 with r2 | r2
  · -- the closing side `B → A`
    have hx : x = vB hk1 hn := Fin.ext (by rw [hv, ← r2]; rfl)
    have hx1 : x + 1 = vA hk1 hn := by
      rw [hx]; apply Fin.ext; rw [fin_add_one_val' _ (by simp only [vB]; omega)]; simp only [vA, vB]; omega
    rw [hx1, hx]
    unfold sideAng; rw [if_neg (by omega), if_pos r2.symm]
    simp only [e, cos_pi_div_two_sub, sin_pi_div_two_sub, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    exact ⟨by rw [← hβdef] at hβs; rw [hβs, hag, gapA], by rw [← hβdef] at hβc; rw [hβc, ← hAB]⟩
  rcases Nat.lt_or_ge v (8 * k) with r3 | r3
  · rw [hLe x (by omega) (by omega), hv]
    unfold sideAng; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rcases Nat.lt_or_ge v (12 * k) with r4 | r4
  · set y : Fin n := ⟨16 * k - 1 - v, by omega⟩
    rw [hxy y rfl, hmir y, hLe y (by simp only [y]; omega) (by simp only [y]; omega), mir_smul_e]
    unfold sideAng; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    congr 2; simp only [y]; ring
  rcases Nat.eq_or_lt_of_le r4 with r5 | r5
  · -- the closing side `D → C`
    have hx : x = vD hk1 hn := Fin.ext (by rw [hv, ← r5]; rfl)
    have hx1 : x + 1 = vC hk1 hn := by
      rw [hx]; apply Fin.ext; rw [fin_add_one_val' _ (by simp only [vD]; omega)]; simp only [vC, vD]
    rw [hx1, hx, hCD]
    unfold sideAng; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos r5.symm, show 3 * π / 2 + β = β + 3 * π / 2 by ring, e_add_three_pi_div_two]
    simp only [Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [← hβdef] at hβs hβc
    exact ⟨by rw [hβs, hag]; rfl, by rw [mul_neg, hβc]⟩
  · rw [hRe x (by omega), hv]
    unfold sideAng; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    congr 2; ring

/-- The gap angle: `0 < β < z/2`. -/
lemma gapβ_facts : 0 < gapβ hk hn (z := z) ∧ gapβ hk hn (z := z) < z / 2 := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hc, hsφ, hl, hz32, hkz⟩ := basic_facts hk hn hz0 hz1 hF
  have hn16 : 16 ≤ n := by omega
  obtain ⟨hloc, hy⟩ := loc n hn16 hz0 hz1 hF
  have hag0 : 0 < gapA hk1 hn (z := z) := by
    rw [gapA_eq_yy k hk1 hn z]; exact yy_pos n (by omega) hz0 hz1 hF
  have hag : gapA hk1 hn (z := z) ≤ 2 * sin (z / 2) ^ 2 := by
    rw [gapA_eq_yy k hk1 hn z]; exact le_trans (le_abs_self _) hy
  have hzn : z < π / ((16 * k : ℕ) : ℝ) := by rw [← hn]; exact hz1
  have hloc' : π / (((16 * k : ℕ) : ℝ) - 2 + π) ≤ z := by rw [← hn]; exact hloc
  obtain ⟨hp1, hp2⟩ := phi_facts hk hz0 hzn hloc' _ hag0 hag
  have hpi3 := pi_gt_three
  unfold gapβ
  constructor
  · exact arctan_pos.mpr (div_pos hag0 hsφ)
  · -- `a / sin φ < 2 sin²(z/2) / sin z = tan(z/2)`
    have hsz : sin z < sin (φ k z) := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hp1
    have hsz0 : 0 < sin z := sin_pos_of_pos_of_lt_pi hz0 (by linarith)
    have hcw : 0 < cos (z / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hsw : 0 < sin (z / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have htan : tan (z / 2) = 2 * sin (z / 2) ^ 2 / sin z := by
      rw [tan_eq_sin_div_cos, show sin z = sin (2 * (z / 2)) by ring_nf, sin_two_mul]
      field_simp
    have hr : gapA hk1 hn (z := z) / sin (φ k z) < tan (z / 2) := by
      rw [htan, div_lt_div_iff₀ hsφ hsz0]
      calc gapA hk1 hn (z := z) * sin z ≤ 2 * sin (z / 2) ^ 2 * sin z :=
            mul_le_mul_of_nonneg_right hag hsz0.le
        _ < 2 * sin (z / 2) ^ 2 * sin (φ k z) := mul_lt_mul_of_pos_left hsz (by positivity)
    calc arctan (gapA hk1 hn (z := z) / sin (φ k z)) < arctan (tan (z / 2)) := arctan_strictMono hr
      _ = z / 2 := arctan_tan (by linarith) (by linarith)

lemma θ_pos (j : ℕ) : 0 < θ k z j := by
  obtain ⟨hc, hsφ, hl, hz32, hkz⟩ := basic_facts hk hn hz0 hz1 hF
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold θ φ
  have : (0 : ℝ) ≤ j * z := by positivity
  nlinarith

/-- Consecutive sides turn left. -/
theorem sideAng_succ (x : ℕ) (hx : x + 1 < n) :
    sideAng k z (gapβ hk hn (z := z)) x < sideAng k z (gapβ hk hn (z := z)) (x + 1) := by
  obtain ⟨hβ0, hβ1⟩ := gapβ_facts hk hn hz0 hz1 hF
  obtain ⟨hc, hsφ, hl, hz32, hkz⟩ := basic_facts hk hn hz0 hz1 hF
  have hθ := θ_pos hk hn hz0 hz1 hF
  set β := gapβ hk hn (z := z)
  have hpi3 := pi_gt_three
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold sideAng
  rcases Nat.lt_or_ge (x + 1) (4 * k - 1) with r1 | r1
  · rw [if_pos (by omega), if_pos (by omega)]
    have := θ_strict k hz0 (show jT k (16 * k - 1 - (x + 1)) < jT k (16 * k - 1 - x) by
      unfold jT
      have h1 := JhiT_strict (16 * k - 1 - (x + 1) - 8 * k) (16 * k - 1 - x - 8 * k) (by omega)
      have h2 := JhiT_ge (16 * k - 1 - (x + 1) - 8 * k) k (by omega)
      omega)
    linarith
  rcases Nat.eq_or_lt_of_le r1 with r2 | r2
  · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    linarith [hθ (jT k (16 * k - 1 - x))]
  rcases Nat.eq_or_lt_of_le r2 with r3 | r3
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    linarith [hθ (jA k (x + 1))]
  rcases Nat.lt_or_ge (x + 1) (8 * k) with r4 | r4
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega)]
    have := θ_strict k hz0 (show jA k x < jA k (x + 1) by
      unfold jA
      have h1 := JhiA_strict x (x + 1) (by omega)
      have h2 := JhiA_ge x k (by omega)
      omega)
    linarith
  rcases Nat.eq_or_lt_of_le r4 with r5 | r5
  · -- the junction `8k − 1 → 8k`
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega)]
    have hx8 : x = 8 * k - 1 := by omega
    have e1 : jA k x = 8 * k - 2 := by rw [hx8]; unfold jA JhiA; split_ifs <;> omega
    have e2 : jA k (16 * k - 1 - (x + 1)) = 8 * k - 2 := by
      rw [show 16 * k - 1 - (x + 1) = 8 * k - 1 by omega]; unfold jA JhiA; split_ifs <;> omega
    rw [e1, e2, θ_val k z _ (by omega)]
    push_cast [show (1 : ℕ) ≤ 8 * k - 2 by omega]
    rw [Nat.cast_sub (by omega)]; push_cast
    nlinarith
  rcases Nat.lt_or_ge (x + 1) (12 * k) with r6 | r6
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have := θ_strict k hz0 (show jA k (16 * k - 1 - (x + 1)) < jA k (16 * k - 1 - x) by
      unfold jA
      have h1 := JhiA_strict (16 * k - 1 - (x + 1)) (16 * k - 1 - x) (by omega)
      have h2 := JhiA_ge (16 * k - 1 - (x + 1)) k (by omega)
      omega)
    linarith
  rcases Nat.eq_or_lt_of_le r6 with r7 | r7
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    linarith [hθ (jA k (16 * k - 1 - x))]
  rcases Nat.eq_or_lt_of_le r7 with r8 | r8
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    linarith [hθ (jT k (x + 1))]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have := θ_strict k hz0 (show jT k x < jT k (x + 1) by
      unfold jT
      have h1 := JhiT_strict (x - 8 * k) (x + 1 - 8 * k) (by omega)
      have h2 := JhiT_ge (x - 8 * k) k (by omega)
      omega)
    linarith

theorem sideAng_mono : ∀ i j, i < j → j < n →
    sideAng k z (gapβ hk hn (z := z)) i < sideAng k z (gapβ hk hn (z := z)) j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hij) with h | h
    · subst h; exact sideAng_succ hk hn hz0 hz1 hF i hj
    · exact lt_trans (ih h (by omega)) (sideAng_succ hk hn hz0 hz1 hF j hj)

theorem sideAng_span :
    sideAng k z (gapβ hk hn (z := z)) (n - 1) < sideAng k z (gapβ hk hn (z := z)) 0 + 2 * π := by
  obtain ⟨hc, hsφ, hl, hz32, hkz⟩ := basic_facts hk hn hz0 hz1 hF
  have h0 : sideAng k z (gapβ hk hn (z := z)) 0 = π / 2 - z / 2 - θ k z (jT k (16 * k - 1)) := by
    unfold sideAng; rw [if_pos (by omega), Nat.sub_zero]
  have hN : sideAng k z (gapβ hk hn (z := z)) (n - 1) = 3 * π / 2 + z / 2 + θ k z (jT k (16 * k - 1)) := by
    unfold sideAng
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show n - 1 = 16 * k - 1 by omega]
  have e : jT k (16 * k - 1) = 8 * k - 3 := by unfold jT JhiT; split_ifs <;> omega
  rw [h0, hN, e, θ_val k z _ (by omega), Nat.cast_sub (by omega)]
  push_cast
  nlinarith [pi_pos]

/-- **The published polygon is convex**, for every `n = 16k ≥ 32`. -/
theorem convex_all : ConvexOrdered (Qc n z) :=
  convex_of_angles (Qc n z) (2 * sin (z / 2)) (sideAng k z (gapβ hk hn (z := z)))
    (side_all hk hn hz0 hz1 hF) (by omega) (basic_facts hk hn hz0 hz1 hF).2.2.1
    (sideAng_mono hk hn hz0 hz1 hF) (sideAng_span hk hn hz0 hz1 hF)

end all

lemma JhiA_step (a : ℕ) : JhiA (a + 1) ≤ JhiA a + 3 := by unfold JhiA; split_ifs <;> omega
lemma JhiT_step (a : ℕ) : JhiT (a + 1) ≤ JhiT a + 3 := by unfold JhiT; split_ifs <;> omega

lemma θ_diff (k : ℕ) (z : ℝ) (i j : ℕ) (h : i ≤ j) : θ k z j - θ k z i = ((j - i : ℕ) : ℝ) * z := by
  unfold θ; rw [Nat.cast_sub h]; ring

section turn
variable {k : ℕ} (hk : 2 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ}
  (hz0 : 0 < z) (hz1 : z < π / n) (hF : Optigon.F n z = 0)
include hk hn hz0 hz1 hF

lemma phi_le : φ k z ≤ 0.16 ∧ z < φ k z := by
  have hk1 : 1 ≤ k := by omega
  have hn16 : 16 ≤ n := by omega
  obtain ⟨hloc, hy⟩ := loc n hn16 hz0 hz1 hF
  have hag0 : 0 < gapA hk1 hn (z := z) := by
    rw [gapA_eq_yy k hk1 hn z]; exact yy_pos n (by omega) hz0 hz1 hF
  have hag : gapA hk1 hn (z := z) ≤ 2 * sin (z / 2) ^ 2 := by
    rw [gapA_eq_yy k hk1 hn z]; exact le_trans (le_abs_self _) hy
  have hzn : z < π / ((16 * k : ℕ) : ℝ) := by rw [← hn]; exact hz1
  have hloc' : π / (((16 * k : ℕ) : ℝ) - 2 + π) ≤ z := by rw [← hn]; exact hloc
  obtain ⟨hp1, hp2⟩ := phi_facts hk hz0 hzn hloc' _ hag0 hag
  exact ⟨hp2, hp1⟩

/-- Every turn is small: `α(x+1) − α(x) ≤ 1/2`. -/
theorem sideAng_turn' (x : ℕ) (hx : x + 1 < n) :
    -(1 / 2) ≤ sideAng k z (gapβ hk hn (z := z)) x - sideAng k z (gapβ hk hn (z := z)) (x + 1) := by
  obtain ⟨hβ0, hβ1⟩ := gapβ_facts hk hn hz0 hz1 hF
  obtain ⟨hc, hsφ, hl, hz32, hkz⟩ := basic_facts hk hn hz0 hz1 hF
  obtain ⟨hφ, hφz⟩ := phi_le hk hn hz0 hz1 hF
  set β := gapβ hk hn (z := z)
  have hpi4 : π < 3.1416 := pi_lt_d4
  have hz3 : 3 * z ≤ 1 / 2 := by linarith
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  -- `θ_2 = φ + 2z`, `θ_0 = φ`
  have h2 : θ k z 2 = φ k z + 2 * z := by unfold θ; push_cast; ring
  have h0 : θ k z 0 = φ k z := by unfold θ; simp
  have hstep : ∀ i j : ℕ, i ≤ j → j ≤ i + 3 → θ k z j - θ k z i ≤ 1 / 2 := by
    intro i j hij hji
    rw [θ_diff k z i j hij]
    have : ((j - i : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show j - i ≤ 3 by omega)
    nlinarith
  unfold sideAng
  rcases Nat.lt_or_ge (x + 1) (4 * k - 1) with r1 | r1
  · rw [if_pos (by omega), if_pos (by omega)]
    have h1 := JhiT_step (16 * k - 1 - (x + 1) - 8 * k)
    have h1' := JhiT_strict (16 * k - 1 - (x + 1) - 8 * k) (16 * k - 1 - x - 8 * k) (by omega)
    have h3 := JhiT_ge (16 * k - 1 - (x + 1) - 8 * k) k (by omega)
    rw [show 16 * k - 1 - (x + 1) - 8 * k + 1 = 16 * k - 1 - x - 8 * k by omega] at h1
    have := hstep (jT k (16 * k - 1 - (x + 1))) (jT k (16 * k - 1 - x)) (by unfold jT; omega) (by unfold jT; omega)
    linarith
  rcases Nat.eq_or_lt_of_le r1 with r2 | r2
  · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    have e : jT k (16 * k - 1 - x) = 2 := by
      rw [show 16 * k - 1 - x = 12 * k + 1 by omega]; unfold jT JhiT; split_ifs <;> omega
    rw [e, h2]; linarith
  rcases Nat.eq_or_lt_of_le r2 with r3 | r3
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have e : jA k (x + 1) = 0 := by
      rw [show x + 1 = 4 * k by omega]; unfold jA JhiA; split_ifs <;> omega
    rw [e, h0]; linarith
  rcases Nat.lt_or_ge (x + 1) (8 * k) with r4 | r4
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega)]
    have h1 := JhiA_step x
    have h1' := JhiA_strict x (x + 1) (by omega)
    have h3 := JhiA_ge x k (by omega)
    have := hstep (jA k x) (jA k (x + 1)) (by unfold jA; omega) (by unfold jA; omega)
    linarith
  rcases Nat.eq_or_lt_of_le r4 with r5 | r5
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega)]
    have hx8 : x = 8 * k - 1 := by omega
    have e1 : jA k x = 8 * k - 2 := by rw [hx8]; unfold jA JhiA; split_ifs <;> omega
    have e2 : jA k (16 * k - 1 - (x + 1)) = 8 * k - 2 := by
      rw [show 16 * k - 1 - (x + 1) = 8 * k - 1 by omega]; unfold jA JhiA; split_ifs <;> omega
    rw [e1, e2, θ_val k z _ (by omega), Nat.cast_sub (by omega)]
    push_cast; nlinarith
  rcases Nat.lt_or_ge (x + 1) (12 * k) with r6 | r6
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have h1 := JhiA_step (16 * k - 1 - (x + 1))
    have h1' := JhiA_strict (16 * k - 1 - (x + 1)) (16 * k - 1 - x) (by omega)
    have h3 := JhiA_ge (16 * k - 1 - (x + 1)) k (by omega)
    rw [show 16 * k - 1 - (x + 1) + 1 = 16 * k - 1 - x by omega] at h1
    have := hstep (jA k (16 * k - 1 - (x + 1))) (jA k (16 * k - 1 - x)) (by unfold jA; omega) (by unfold jA; omega)
    linarith
  rcases Nat.eq_or_lt_of_le r6 with r7 | r7
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have e : jA k (16 * k - 1 - x) = 0 := by
      rw [show 16 * k - 1 - x = 4 * k by omega]; unfold jA JhiA; split_ifs <;> omega
    rw [e, h0]; linarith
  rcases Nat.eq_or_lt_of_le r7 with r8 | r8
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have e : jT k (x + 1) = 2 := by
      rw [show x + 1 = 12 * k + 1 by omega]; unfold jT JhiT; split_ifs <;> omega
    rw [e, h2]; linarith
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have h1 := JhiT_step (x - 8 * k)
    have h1' := JhiT_strict (x - 8 * k) (x + 1 - 8 * k) (by omega)
    have h3 := JhiT_ge (x - 8 * k) k (by omega)
    rw [show x - 8 * k + 1 = x + 1 - 8 * k by omega] at h1
    have := hstep (jT k x) (jT k (x + 1)) (by unfold jT; omega) (by unfold jT; omega)
    linarith

theorem sideAng_turn (x : ℕ) (hx : x + 1 < n) :
    sideAng k z (gapβ hk hn (z := z)) (x + 1) - sideAng k z (gapβ hk hn (z := z)) x ≤ 1 / 2 := by
  have := sideAng_turn' hk hn hz0 hz1 hF x hx; linarith

end turn

end Chiquipoli.Family.Trig.P1
