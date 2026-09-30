/-
# Problem 1: the published polygon is small, for every `n = 16k ≥ 32`

For every direction `ψ` we exhibit vertices `x`, `y` that support `ψ` and `ψ + π`
and are at distance `≤ 1` (`antipodal`). Then `small_of_antipodal` gives
`Small`. Modulo `2π` and the swap `ψ ↦ ψ + π`, three cases cover every
direction:
* the sector `[θ_j − z/2, θ_j + z/2]` of a rung of the first half: `x`, `y` are
  its ends;
* the sector around `π/2`: the middle rung `{8k, 0}`;
* the gap arc `[−(φ − z/2), φ − z/2]`. It is split at `±β`, giving the pairs
  `B–D` (a rung), `A–D` (width `a + cos φ ≤ 1`) and `A–C` (a rung).
The sectors of the second half are the mirror images of those of the first.
-/
import ChiquipoliFamily.AllN.Feasibility.Angles

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Chiquipoli.Family.Trig.P1

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Chiquipoli.Family.Trig.RungVec
  Chiquipoli.Family.Trig.P3

lemma e_add_two_pi (a : ℝ) : e (a + 2 * π) = e a := by simp [e]
lemma e_sub_two_pi (a : ℝ) : e (a - 2 * π) = e a := by simp [e]

lemma JhiA_pred (a : ℕ) (h : 1 ≤ a) : JhiA (a - 1) + 1 = JloA a := by
  unfold JhiA JloA; split_ifs <;> omega
lemma JhiT_pred (t : ℕ) (h : 1 ≤ t) : JhiT (t - 1) + 1 = JloT t := by
  unfold JhiT JloT; split_ifs <;> omega

lemma e_add_int (a : ℝ) (m : ℤ) : e (a + m * (2 * π)) = e a := by
  simp only [e, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]

section small
variable {k : ℕ} (hk : 2 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ}
  (hz0 : 0 < z) (hz1 : z < π / n) (hF : Optigon.F n z = 0)
include hk hn hz0 hz1 hF

/-- A vertex `x ≥ 1` supports every direction of its normal cone. -/
lemma supp_at (x : Fin n) (hx : 1 ≤ x.val) (ψ : ℝ)
    (h1 : sideAng k z (gapβ hk hn (z := z)) (x.val - 1) - π / 2 ≤ ψ)
    (h2 : ψ ≤ sideAng k z (gapβ hk hn (z := z)) x.val - π / 2) : Supp (Qc n z) x (e ψ) := by
  obtain ⟨hc, hsφ, hl, hz32, hkz⟩ := basic_facts hk hn hz0 hz1 hF
  have hxm : (x - 1).val = x.val - 1 := fin_sub_one_val x hx (by omega)
  have he1 : Qc n z x - Qc n z (x - 1) = (2 * sin (z / 2)) • e (sideAng k z (gapβ hk hn (z := z)) (x.val - 1)) := by
    have := side_all hk hn hz0 hz1 hF (x - 1)
    rw [sub_add_cancel, hxm] at this; exact this
  have hsucc := sideAng_succ hk hn hz0 hz1 hF (x.val - 1) (by have := x.isLt; omega)
  have hturn := sideAng_turn hk hn hz0 hz1 hF (x.val - 1) (by have := x.isLt; omega)
  rw [Nat.sub_add_cancel hx] at hsucc hturn
  exact supp_of_cone (Qc n z) (convex_all hk hn hz0 hz1 hF) hl x _ _ he1 (side_all hk hn hz0 hz1 hF x)
    (by linarith) (by linarith [pi_gt_three]) ψ h1 h2

lemma sideAng_zero : sideAng k z (gapβ hk hn (z := z)) 0 = 3 * (z / 2) ∧
    sideAng k z (gapβ hk hn (z := z)) (n - 1) = 2 * π - 3 * (z / 2) := by
  have h0 : sideAng k z (gapβ hk hn (z := z)) 0 = π / 2 - z / 2 - θ k z (jT k (16 * k - 1)) := by
    unfold sideAng; rw [if_pos (by omega), Nat.sub_zero]
  have hN : sideAng k z (gapβ hk hn (z := z)) (n - 1) = 3 * π / 2 + z / 2 + θ k z (jT k (16 * k - 1)) := by
    unfold sideAng
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show n - 1 = 16 * k - 1 by omega]
  have e : jT k (16 * k - 1) = 8 * k - 3 := by unfold jT JhiT; split_ifs <;> omega
  rw [h0, hN, e, θ_val k z _ (by omega), Nat.cast_sub (by omega)]
  push_cast
  constructor <;> ring

/-- The vertex `0` supports `[−π/2 − 3z/2, −π/2 + 3z/2]`. -/
lemma supp_zero (ψ : ℝ) (h1 : -(π / 2) - 3 * (z / 2) ≤ ψ) (h2 : ψ ≤ -(π / 2) + 3 * (z / 2)) :
    Supp (Qc n z) 0 (e ψ) := by
  obtain ⟨hc, hsφ, hl, hz32, hkz⟩ := basic_facts hk hn hz0 hz1 hF
  obtain ⟨hα0, hαN⟩ := sideAng_zero hk hn hz0 hz1 hF
  have hm : ((0 : Fin n) - 1).val = n - 1 := by
    have := neg_sub_one_val (0 : Fin n) (by omega); simpa using this
  have he1 : Qc n z 0 - Qc n z (0 - 1) = (2 * sin (z / 2)) • e (2 * π - 3 * (z / 2) - 2 * π) := by
    have := side_all hk hn hz0 hz1 hF (0 - 1)
    rw [sub_add_cancel, hm, hαN] at this; rw [e_sub_two_pi]; exact this
  have he2 := side_all hk hn hz0 hz1 hF 0
  rw [show ((0 : Fin n)).val = 0 from rfl, hα0] at he2
  exact supp_of_cone (Qc n z) (convex_all hk hn hz0 hz1 hF) hl 0 _ _ he1 he2
    (by linarith) (by linarith [pi_gt_three]) ψ (by linarith) (by linarith)

/-- The angles at the special vertices. -/
lemma ang_vals :
    sideAng k z (gapβ hk hn (z := z)) (4 * k - 2) = π / 2 - z / 2 - (φ k z + 2 * z) ∧
    sideAng k z (gapβ hk hn (z := z)) (4 * k - 1) = π / 2 - gapβ hk hn (z := z) ∧
    sideAng k z (gapβ hk hn (z := z)) (4 * k) = φ k z + z / 2 + π / 2 ∧
    sideAng k z (gapβ hk hn (z := z)) (8 * k - 1) = π - z / 2 ∧
    sideAng k z (gapβ hk hn (z := z)) (8 * k) = π + z / 2 ∧
    sideAng k z (gapβ hk hn (z := z)) (12 * k - 1) = 3 * π / 2 - z / 2 - φ k z ∧
    sideAng k z (gapβ hk hn (z := z)) (12 * k) = 3 * π / 2 + gapβ hk hn (z := z) ∧
    sideAng k z (gapβ hk hn (z := z)) (12 * k + 1) = 3 * π / 2 + z / 2 + (φ k z + 2 * z) := by
  have h2 : θ k z 2 = φ k z + 2 * z := by unfold θ; push_cast; ring
  have h0 : θ k z 0 = φ k z := by unfold θ; simp
  have h8 : θ k z (8 * k - 2) = π / 2 - z := by
    rw [θ_val k z _ (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have jT2 : jT k (12 * k + 1) = 2 := by unfold jT JhiT; split_ifs <;> omega
  have jA0 : jA k (4 * k) = 0 := by unfold jA JhiA; split_ifs <;> omega
  have jA8 : jA k (8 * k - 1) = 8 * k - 2 := by unfold jA JhiA; split_ifs <;> omega
  unfold sideAng
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [if_pos (by omega), show 16 * k - 1 - (4 * k - 2) = 12 * k + 1 by omega, jT2, h2]
  · rw [if_neg (by omega), if_pos rfl]
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), jA0, h0]
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), jA8, h8]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show 16 * k - 1 - 8 * k = 8 * k - 1 by omega, jA8, h8]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show 16 * k - 1 - (12 * k - 1) = 4 * k by omega, jA0, h0]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), jT2, h2]

/-- Antipodal pairs. -/
def Anti (q : Cfg n) (ψ : ℝ) : Prop :=
  ∃ x y : Fin n, Supp q x (e ψ) ∧ Supp q y (e (ψ + π)) ∧ nsq (q x - q y) ≤ 1

/-- The sector around `π/2`: the middle rung `{8k, 0}`. -/
lemma caseM (ψ : ℝ) (h1 : π / 2 - z / 2 ≤ ψ) (h2 : ψ ≤ π / 2 + z / 2) : Anti (Qc n z) ψ := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨-, -, -, hv8m, hv8, -, -, -⟩ := ang_vals hk hn hz0 hz1 hF
  refine ⟨vH hk1 hn, 0, ?_, ?_, ?_⟩
  · apply supp_at hk hn hz0 hz1 hF _ (by simp only [vH]; omega)
    · rw [show (vH hk1 hn).val - 1 = 8 * k - 1 from rfl, hv8m]; linarith
    · rw [show (vH hk1 hn).val = 8 * k from rfl, hv8]; linarith
  · rw [show ψ + π = (ψ - π) + 2 * π by ring, e_add_two_pi]
    apply supp_zero hk hn hz0 hz1 hF <;> linarith
  · -- the middle rung
    have hs : Strip.Sj k (8 * k - 1) = 0 := by unfold Strip.Sj; rw [if_neg (by omega)]; omega
    have hR1 : (Strip.R n k (8 * k - 1)).1 = 0 := by
      apply Fin.ext; simp only [Strip.R, Strip.ver, hs, show Strip.Pa 0 = 0 from rfl, Nat.zero_mod]; rfl
    have hR2 : (Strip.R n k (8 * k - 1)).2 = vH hk1 hn := by
      apply Fin.ext; simp only [Strip.R, Strip.ver, hs, show Strip.Pt 0 = 0 from rfl, add_zero, vH]
      exact Nat.mod_eq_of_lt (by omega)
    have := rungs_eq_root hk1 hn hz0 (by linarith [basic_facts hk hn hz0 hz1 hF |>.2.2.2.1, pi_pos]) hF
      (8 * k - 1) (by omega)
    rw [hR1, hR2] at this
    rw [this]

/-- The gap arc around `0`. -/
lemma caseG (ψ : ℝ) (h1 : -(φ k z - z / 2) ≤ ψ) (h2 : ψ ≤ φ k z - z / 2) : Anti (Qc n z) ψ := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hc, hsφ, hl, hz32, hkz⟩ := basic_facts hk hn hz0 hz1 hF
  have hw : sin (z / 2) ≠ 0 := by intro h; rw [h] at hl; linarith
  have hcw : cos (z / 2) ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩).ne'
  obtain ⟨hβ0, hβ1⟩ := gapβ_facts hk hn hz0 hz1 hF
  obtain ⟨hφ, hφz⟩ := phi_le hk hn hz0 hz1 hF
  obtain ⟨v2, v3, v4, -, -, v12m, v12, v12p⟩ := ang_vals hk hn hz0 hz1 hF
  set β := gapβ hk hn (z := z)
  have hz4 : z < π / 4 := by linarith [pi_pos]
  -- the two rungs at the gap
  have hRlast : Strip.R n k (16 * k - 2) = (vB hk1 hn, vD hk1 hn) := by
    have hs : Strip.Sj k (16 * k - 2) = 8 * k - 1 := by unfold Strip.Sj; rw [if_neg (by omega)]; omega
    have hp := Strip.PaPt (k - 1) 7 (by norm_num)
    rw [show 8 * (k - 1) + 7 = 8 * k - 1 by omega] at hp
    simp only [Strip.da, Strip.dt] at hp
    apply Prod.ext <;> apply Fin.ext <;> simp only [Strip.R, Strip.ver, hs, hp.1, hp.2, vB, vD]
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hBD := rungs_eq_root hk1 hn hz0 hz4 hF (16 * k - 2) (by omega)
  rw [hRlast] at hBD
  have hAC := rungs_eq_root hk1 hn hz0 hz4 hF 0 (by omega)
  rw [R0 hk1 hn hc hw hcw] at hAC
  simp only at hAC hBD
  have hsB : ∀ ψ', -(z / 2) - (φ k z + 2 * z) ≤ ψ' → ψ' ≤ -β → Supp (Qc n z) (vB hk1 hn) (e ψ') := by
    intro ψ' a b
    apply supp_at hk hn hz0 hz1 hF _ (by simp only [vB]; omega)
    · rw [show (vB hk1 hn).val - 1 = 4 * k - 2 from rfl, v2]; linarith
    · rw [show (vB hk1 hn).val = 4 * k - 1 from rfl, v3]; linarith
  have hsA : ∀ ψ', -β ≤ ψ' → ψ' ≤ φ k z + z / 2 → Supp (Qc n z) (vA hk1 hn) (e ψ') := by
    intro ψ' a b
    apply supp_at hk hn hz0 hz1 hF _ (by simp only [vA]; omega)
    · rw [show (vA hk1 hn).val - 1 = 4 * k - 1 by simp only [vA], v3]; linarith
    · rw [show (vA hk1 hn).val = 4 * k from rfl, v4]; linarith
  have hsD : ∀ ψ', π - z / 2 - φ k z ≤ ψ' → ψ' ≤ π + β → Supp (Qc n z) (vD hk1 hn) (e ψ') := by
    intro ψ' a b
    apply supp_at hk hn hz0 hz1 hF _ (by simp only [vD]; omega)
    · rw [show (vD hk1 hn).val - 1 = 12 * k - 1 by simp only [vD], v12m]; linarith
    · rw [show (vD hk1 hn).val = 12 * k from rfl, v12]; linarith
  have hsC : ∀ ψ', π + β ≤ ψ' → ψ' ≤ π + z / 2 + (φ k z + 2 * z) → Supp (Qc n z) (vC hk1 hn) (e ψ') := by
    intro ψ' a b
    apply supp_at hk hn hz0 hz1 hF _ (by simp only [vC]; omega)
    · rw [show (vC hk1 hn).val - 1 = 12 * k by simp only [vC]; omega, v12]; linarith
    · rw [show (vC hk1 hn).val = 12 * k + 1 from rfl, v12p]; linarith
  rcases le_or_gt ψ (-β) with c1 | c1
  · exact ⟨vB hk1 hn, vD hk1 hn, hsB ψ (by linarith) c1, hsD _ (by linarith) (by linarith),
      by rw [nsq_comm] at hBD; rw [hBD]⟩
  rcases le_or_gt ψ β with c2 | c2
  · refine ⟨vA hk1 hn, vD hk1 hn, hsA ψ c1.le (by linarith), hsD _ (by linarith) (by linarith), ?_⟩
    -- `A − D = (2 A_x, 0)`, `2 A_x = a + cos φ ≤ 1`
    have hDA : Qc n z (vD hk1 hn) = mir (Qc n z (vA hk1 hn)) := by
      rw [D_neg hk1 hn hc hw hcw, Qc_neg k hk1 hn z]
    have hBC : Qc n z (vB hk1 hn) = mir (Qc n z (vC hk1 hn)) := by
      rw [B_neg hk1 hn hc hw hcw, Qc_neg k hk1 hn z]
    have hCA := gap_CA hk1 hn hc hw hcw
    have hag : gapA hk1 hn (z := z) = (Qc n z (vA hk1 hn)).1 - (Qc n z (vB hk1 hn)).1 := rfl
    have h2A : 2 * (Qc n z (vA hk1 hn)).1 = gapA hk1 hn (z := z) + cos (φ k z) := by
      rw [hag, hBC]
      have := congrArg Prod.fst hCA
      simp only [Prod.fst_sub, Prod.fst_neg, e, mir] at this ⊢
      linarith
    have hn16 : 16 ≤ n := by omega
    obtain ⟨-, hy⟩ := loc n hn16 hz0 hz1 hF
    have hag0 : 0 < gapA hk1 hn (z := z) := by
      rw [gapA_eq_yy k hk1 hn z]; exact yy_pos n (by omega) hz0 hz1 hF
    have hagl : gapA hk1 hn (z := z) ≤ 2 * sin (z / 2) ^ 2 := by
      rw [gapA_eq_yy k hk1 hn z]; exact le_trans (le_abs_self _) hy
    have hcz : cos (φ k z) ≤ cos z := cos_le_cos_of_nonneg_of_le_pi hz0.le (by linarith [pi_gt_three]) hφz.le
    have hsq := sq_two_sin_half' z
    have hcp : 0 < cos (φ k z) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩
    have hle : gapA hk1 hn (z := z) + cos (φ k z) ≤ 1 := by nlinarith
    rw [hDA]
    simp only [nsq, ip, mir, Prod.fst_sub, Prod.snd_sub, sub_self]
    nlinarith
  · exact ⟨vA hk1 hn, vC hk1 hn, hsA ψ (by linarith) (by linarith), hsC _ (by linarith) (by linarith),
      by rw [nsq_comm, hAC]⟩

lemma angL (a : ℕ) (h1 : 4 * k ≤ a) (h2 : a ≤ 8 * k - 1) :
    sideAng k z (gapβ hk hn (z := z)) a = θ k z (jA k a) + z / 2 + π / 2 := by
  unfold sideAng; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

lemma angR (x : ℕ) (h1 : 12 * k + 1 ≤ x) :
    sideAng k z (gapβ hk hn (z := z)) x = 3 * π / 2 + z / 2 + θ k z (jT k x) := by
  unfold sideAng
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma θ_mono (i j : ℕ) (h : i ≤ j) : θ k z i ≤ θ k z j := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [h']
  · exact (θ_strict k hz0 h').le

/-- A direction in the sector of a rung of the first half. -/
lemma pick_j (ψ : ℝ) (h1 : φ k z - z / 2 ≤ ψ) (h2 : ψ ≤ π / 2 - z / 2) :
    ∃ j, j ≤ 8 * k - 2 ∧ θ k z j - z / 2 ≤ ψ ∧ ψ ≤ θ k z j + z / 2 := by
  set r := (ψ - φ k z + z / 2) / z with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hz0.le
  have hf1 := Nat.floor_le hr0
  have hf2 := Nat.lt_floor_add_one r
  have hθ : ∀ j : ℕ, θ k z j = φ k z + j * z := fun j => rfl
  rcases le_or_gt ⌊r⌋₊ (8 * k - 2) with h | h
  · refine ⟨⌊r⌋₊, h, ?_, ?_⟩
    · rw [hθ]; have := mul_le_mul_of_nonneg_right hf1 hz0.le; rw [hr, div_mul_cancel₀ _ hz0.ne'] at this; linarith
    · rw [hθ]; have := mul_lt_mul_of_pos_right hf2 hz0; rw [hr, div_mul_cancel₀ _ hz0.ne'] at this
      push_cast at this; linarith
  · refine ⟨8 * k - 2, le_rfl, ?_, ?_⟩
    · have hf : ((8 * k - 1 : ℕ) : ℝ) ≤ r := le_trans (by exact_mod_cast (show 8 * k - 1 ≤ ⌊r⌋₊ by omega)) hf1
      have := mul_le_mul_of_nonneg_right hf hz0.le
      rw [hr, div_mul_cancel₀ _ hz0.ne'] at this
      rw [θ_val k z _ (by omega), Nat.cast_sub (by omega)]
      rw [Nat.cast_sub (by omega)] at this
      unfold φ at this; push_cast at this ⊢; linarith
    · rw [θ_val k z _ (by omega), Nat.cast_sub (by omega)]; push_cast; linarith

/-- The sector of a rung of the first half. -/
lemma caseS (ψ : ℝ) (h1 : φ k z - z / 2 ≤ ψ) (h2 : ψ ≤ π / 2 - z / 2) : Anti (Qc n z) ψ := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hc, hsφ, hl, hz32, hkz⟩ := basic_facts hk hn hz0 hz1 hF
  obtain ⟨hβ0, hβ1⟩ := gapβ_facts hk hn hz0 hz1 hF
  obtain ⟨hφ, hφz⟩ := phi_le hk hn hz0 hz1 hF
  obtain ⟨-, v3, -, -, -, -, v12, -⟩ := ang_vals hk hn hz0 hz1 hF
  have hz4 : z < π / 4 := by linarith [pi_pos]
  obtain ⟨j, hj, hj1, hj2⟩ := pick_j hk hn hz0 hz1 hF ψ h1 h2
  set J := 8 * k + 1 + j with hJ
  obtain ⟨ra, rt⟩ := R_first hk1 hn j (by omega)
  have hPa := Strip.Pa_lt k J (by omega)
  obtain ⟨hPa4, hPt4⟩ := Pa_Pt_hi k J (by omega) (by omega)
  obtain ⟨hlo, hhi⟩ := (Pa_eq_iff (Strip.Pa J) J).mp rfl
  have hPt8 : Strip.Pt J ≤ 8 * k := by
    rcases Nat.lt_or_ge J (16 * k - 1) with h | h
    · exact (Strip.Pt_lt k J h).le
    · rw [show J = 16 * k - 1 by omega]; exact (Strip.P_last k hk1).2.le
  obtain ⟨hloT, hhiT⟩ := (Pt_eq_iff (Strip.Pt J) J (Or.inl (by omega))).mp rfl
  set a := Strip.Pa J with ha
  set t := Strip.Pt J with ht
  refine ⟨(Strip.R n k j).1, (Strip.R n k j).2, ?_, ?_, ?_⟩
  · -- the `a`-end supports `ψ`
    apply supp_at hk hn hz0 hz1 hF _ (by rw [ra]; omega)
    · rw [ra]
      rcases eq_or_lt_of_le hPa4 with h | h
      · rw [← h, v3]; linarith
      · rw [angL hk hn hz0 hz1 hF (a - 1) (by omega) (by omega)]
        have hp := JhiA_pred a (by omega)
        have hj' : jA k (a - 1) ≤ j - 1 := by unfold jA; omega
        have hA2 : JloA a ≥ 8 * k + 2 := by unfold JloA; split_ifs <;> omega
        have := θ_mono hk hn hz0 hz1 hF _ _ hj'
        have e : θ k z (j - 1) = θ k z j - z := by
          have := θ_diff k z (j - 1) j (by omega)
          rw [show j - (j - 1) = 1 by omega] at this; push_cast at this; linarith
        linarith
    · rw [ra, angL hk hn hz0 hz1 hF a hPa4 (by omega)]
      have := θ_mono hk hn hz0 hz1 hF j (jA k a) (by unfold jA; omega)
      linarith
  · -- the `t`-end supports `ψ + π`
    rcases Nat.lt_or_ge t (8 * k) with htt | htt
    · have hyv : (Strip.R n k j).2.val = 8 * k + t := by rw [rt, Nat.mod_eq_of_lt (by omega)]
      apply supp_at hk hn hz0 hz1 hF _ (by rw [hyv]; omega)
      · rw [hyv]
        rcases eq_or_lt_of_le (show 4 * k + 1 ≤ t by omega) with h | h
        · rw [← h, show 8 * k + (4 * k + 1) - 1 = 12 * k by omega, v12]; linarith
        · rw [angR hk hn hz0 hz1 hF _ (by omega)]
          have hp := JhiT_pred t (by omega)
          have hA2 : JloT t ≥ 8 * k + 2 := by unfold JloT; split_ifs <;> omega
          have hj' : jT k (8 * k + t - 1) ≤ j - 1 := by
            unfold jT; rw [show 8 * k + t - 1 - 8 * k = t - 1 by omega]; omega
          have := θ_mono hk hn hz0 hz1 hF _ _ hj'
          have e : θ k z (j - 1) = θ k z j - z := by
            have := θ_diff k z (j - 1) j (by omega)
            rw [show j - (j - 1) = 1 by omega] at this; push_cast at this; linarith
          linarith
      · rw [hyv, angR hk hn hz0 hz1 hF _ (by omega)]
        have := θ_mono hk hn hz0 hz1 hF j (jT k (8 * k + t)) (by
          unfold jT; rw [show 8 * k + t - 8 * k = t by omega]; omega)
        linarith
    · -- the vertex `0`
      have hy0 : (Strip.R n k j).2 = 0 := by
        apply Fin.ext; rw [rt, show 8 * k + t = n by omega, Nat.mod_self]; rfl
      have hj8 : j = 8 * k - 2 := by
        by_contra hne
        have := Strip.Pt_lt k J (by omega); omega
      rw [hy0, show ψ + π = (ψ - π) + 2 * π by ring, e_add_two_pi]
      rw [hj8, θ_val k z _ (by omega), Nat.cast_sub (by omega)] at hj1 hj2
      push_cast at hj1 hj2
      apply supp_zero hk hn hz0 hz1 hF <;> linarith
  · rw [nsq_comm, rungs_eq_root hk1 hn hz0 hz4 hF j (by omega)]

lemma supp_mirror (x : Fin n) (ψ : ℝ) (h : Supp (Qc n z) x (e ψ)) : Supp (Qc n z) (-x) (e (π - ψ)) := by
  have hk1 : 1 ≤ k := by omega
  intro m
  have hm := h (-m)
  have e1 : Qc n z m = mir (Qc n z (-m)) := by rw [Qc_neg k hk1 hn z, mir_mir]
  rw [e1, Qc_neg k hk1 hn z x]
  simp only [ip, mir, e, Prod.fst_sub, Prod.snd_sub, cos_pi_sub, sin_pi_sub] at hm ⊢
  linarith

/-- The mirror sector. -/
lemma caseS' (ψ : ℝ) (h1 : π / 2 + z / 2 ≤ ψ) (h2 : ψ ≤ π - (φ k z - z / 2)) : Anti (Qc n z) ψ := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨x, y, hx, hy, hxy⟩ := caseS hk hn hz0 hz1 hF (π - ψ) (by linarith) (by linarith)
  refine ⟨-x, -y, ?_, ?_, ?_⟩
  · have := supp_mirror hk hn hz0 hz1 hF x _ hx; rwa [show π - (π - ψ) = ψ by ring] at this
  · have := supp_mirror hk hn hz0 hz1 hF y _ hy
    rwa [show π - (π - ψ + π) = (ψ + π) - 2 * π by ring, e_sub_two_pi] at this
  · rw [Qc_neg k hk1 hn z, Qc_neg k hk1 hn z, mir_sub, show nsq (mir (Qc n z x - Qc n z y)) = nsq (Qc n z x - Qc n z y)
      by simp only [nsq, ip, mir, Prod.fst_sub, Prod.snd_sub]; ring]
    exact hxy

/-- Half of the circle. -/
lemma core (ψ : ℝ) (h1 : -(φ k z - z / 2) ≤ ψ) (h2 : ψ ≤ π - (φ k z - z / 2)) : Anti (Qc n z) ψ := by
  rcases le_or_gt ψ (φ k z - z / 2) with c1 | c1
  · exact caseG hk hn hz0 hz1 hF ψ h1 c1
  rcases le_or_gt ψ (π / 2 - z / 2) with c2 | c2
  · exact caseS hk hn hz0 hz1 hF ψ c1.le c2
  rcases le_or_gt ψ (π / 2 + z / 2) with c3 | c3
  · exact caseM hk hn hz0 hz1 hF ψ c2.le c3
  · exact caseS' hk hn hz0 hz1 hF ψ c3.le h2

/-- **Every direction has an antipodal pair at distance `≤ 1`.** -/
theorem antipodal (ψ : ℝ) : Anti (Qc n z) ψ := by
  obtain ⟨hφ, hφz⟩ := phi_le hk hn hz0 hz1 hF
  have hpi := pi_pos
  set c := φ k z - z / 2 with hc
  have hc0 : 0 < c := by linarith
  set m := ⌊(ψ + c) / (2 * π)⌋ with hm
  set ψ0 := ψ - m * (2 * π) with hψ0
  have hA := Int.floor_le ((ψ + c) / (2 * π))
  have hB := Int.lt_floor_add_one ((ψ + c) / (2 * π))
  rw [← hm] at hA hB
  have hlo : -c ≤ ψ0 := by
    have := mul_le_mul_of_nonneg_right hA (show 0 ≤ 2 * π by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at this; linarith
  have hhi : ψ0 < 2 * π - c := by
    have := mul_lt_mul_of_pos_right hB (show 0 < 2 * π by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at this; push_cast at this; linarith
  have eψ : e ψ = e ψ0 := by
    rw [hψ0, ← e_add_int (ψ - (m : ℝ) * (2 * π)) m, sub_add_cancel]
  have eψπ : e (ψ + π) = e (ψ0 + π) := by
    rw [hψ0, ← e_add_int (ψ - (m : ℝ) * (2 * π) + π) m]; congr 1; ring
  rcases le_or_gt ψ0 (π - c) with h | h
  · obtain ⟨x, y, hx, hy, hxy⟩ := core hk hn hz0 hz1 hF ψ0 hlo h
    exact ⟨x, y, eψ ▸ hx, eψπ ▸ hy, hxy⟩
  · obtain ⟨x, y, hx, hy, hxy⟩ := core hk hn hz0 hz1 hF (ψ0 - π) (by linarith) (by linarith)
    refine ⟨y, x, ?_, ?_, by rw [nsq_comm]; exact hxy⟩
    · rw [eψ, show ψ0 = ψ0 - π + π by ring]; exact hy
    · rw [eψπ, show ψ0 + π = (ψ0 - π) + 2 * π by ring, e_add_two_pi]; exact hx

/-- **The published polygon is small**, for every `n = 16k ≥ 32`. -/
theorem small_all : Small (Qc n z) := small_of_antipodal (Qc n z) (antipodal hk hn hz0 hz1 hF)

end small

end Chiquipoli.Family.Trig.P1
