/-
# Problem 1: every side of the published polygon, as `ℓ e(α)`

Lemma T of the note on Problem 1, for every `n = 16k`:
* the side `a → a + 1` of the first half (`4k ≤ a ≤ 8k − 1`) is
  `e(θ_{j+1}) − e(θ_j)` with `j = stepOf a` (`side_L`);
* the side `x → x + 1`, `x = 8k + t` (`4k + 1 ≤ t ≤ 8k − 1`), is
  `−(e(θ_{j+1}) − e(θ_j))` (`side_R`).
The second half follows by symmetry, and the two closing sides from the gap.
-/
import ChiquipoliFamily.Trig.P3Final
import ChiquipoliFamily.Trig.P1Generic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Chiquipoli.Family.Trig.P1

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Chiquipoli.Family.Trig.RungVec
  Chiquipoli.Family.Trig.P3

section sides
variable {k : ℕ} (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ} (hc : cos (2 * z) ≠ 0)
include hk hn hc

set_option maxHeartbeats 1000000 in
/-- The side `a → a + 1` of the first half. -/
theorem side_L (x : Fin n) (hx1 : 4 * k ≤ x.val) (hx2 : x.val ≤ 8 * k - 1) :
    Qc n z (x + 1) - Qc n z x = e (θ k z (JhiA x.val - 8 * k - 1 + 1)) - e (θ k z (JhiA x.val - 8 * k - 1)) := by
  obtain ⟨a, ha⟩ : ∃ a, x.val = a := ⟨_, rfl⟩
  rw [ha] at hx1 hx2 ⊢
  have hra := Nat.mod_lt a (show 4 > 0 by norm_num)
  obtain ⟨hA0, hA1, hA2, hA3⟩ := JA_vals a
  have c4 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have hhi : JhiA a ≤ 16 * k - 1 ∧ JloA a ≤ JhiA a ∧ 8 * k ≤ JloA a := by
    rcases c4 with hc | hc | hc | hc
    · rw [(hA0 hc).1, (hA0 hc).2]; omega
    · rw [(hA1 hc).1, (hA1 hc).2]; omega
    · rw [(hA2 hc).1, (hA2 hc).2]; omega
    · rw [(hA3 hc).1, (hA3 hc).2]; omega
  have hPa_hi : Strip.Pa (JhiA a) = a := (Pa_eq_iff a _).mpr ⟨hhi.2.1, le_rfl⟩
  obtain ⟨hi, hhi_def⟩ : ∃ hi, hi = JhiA a - 8 * k - 1 := ⟨_, rfl⟩
  rw [← hhi_def]
  have hJ1 : 8 * k + 1 ≤ JhiA a := by
    rcases c4 with hc | hc | hc | hc
    · rw [(hA0 hc).2]; omega
    · rw [(hA1 hc).2]; omega
    · rw [(hA2 hc).2]; omega
    · rw [(hA3 hc).2]; omega
  rcases Nat.lt_or_ge a (8 * k - 1) with hlt | hge
  · have hJ : JhiA a % 8 = 1 ∨ JhiA a % 8 = 2 ∨ JhiA a % 8 = 4 ∨ JhiA a % 8 = 7 := by
      rcases c4 with hc | hc | hc | hc
      · rw [(hA0 hc).2]; omega
      · rw [(hA1 hc).2]; omega
      · rw [(hA2 hc).2]; omega
      · rw [(hA3 hc).2]; omega
    have hhi2 : JhiA a ≤ 16 * k - 3 := by
      rcases c4 with hc | hc | hc | hc
      · rw [(hA0 hc).2]; omega
      · rw [(hA1 hc).2]; omega
      · rw [(hA2 hc).2]; omega
      · rw [(hA3 hc).2]; omega
    obtain ⟨hPa, hPt⟩ := P_succ_a (JhiA a) hJ
    have r1 := R_first hk hn hi (by omega)
    have r2 := R_first hk hn (hi + 1) (by omega)
    rw [show 8 * k + 1 + hi = JhiA a by omega] at r1
    rw [show 8 * k + 1 + (hi + 1) = JhiA a + 1 by omega] at r2
    have e1 : (Strip.R n k hi).1 = x := by rw [Fin.ext_iff, r1.1, hPa_hi, ha]
    have e2 : (Strip.R n k (hi + 1)).1 = x + 1 := by
      rw [Fin.ext_iff, r2.1, hPa, hPa_hi, fin_add_one_val' x (by omega), ha]
    have e3 : (Strip.R n k (hi + 1)).2 = (Strip.R n k hi).2 := Fin.ext (by rw [r1.2, r2.2, hPt])
    have v1 := rung_e k hk hn z hc hi (by omega)
    have v2 := rung_e k hk hn z hc (hi + 1) (by omega)
    rw [e1] at v1
    rw [e2, e3] at v2
    rw [show Qc n z (x + 1) - Qc n z x = (Qc n z (Strip.R n k hi).2 - Qc n z x)
        - (Qc n z (Strip.R n k hi).2 - Qc n z (x + 1)) by abel, v1, v2]
    abel
  · -- the junction side `{8k − 1, 8k}`
    have hhi' : hi = 8 * k - 2 := by rw [hhi_def, (hA3 (by omega)).2]; omega
    rw [hhi', show 8 * k - 2 + 1 = 8 * k - 1 by omega]
    have v1 := rung_e k hk hn z hc (8 * k - 2) (by omega)
    have v2 := rung_mid k hk hn z hc
    have r1 := R_first hk hn (8 * k - 2) (by omega)
    rw [show 8 * k + 1 + (8 * k - 2) = 16 * k - 1 by omega, (Strip.P_last k hk).1, (Strip.P_last k hk).2,
      show 8 * k + 8 * k = 16 * k by ring] at r1
    have hs : Strip.Sj k (8 * k - 1) = 0 := by unfold Strip.Sj; rw [if_neg (by omega)]; omega
    have e1 : (Strip.R n k (8 * k - 2)).1 = x := by rw [Fin.ext_iff, r1.1, ha]; omega
    have e2 : (Strip.R n k (8 * k - 2)).2 = (Strip.R n k (8 * k - 1)).1 := by
      rw [Fin.ext_iff, r1.2]
      simp only [Strip.R, Strip.ver, hs, show Strip.Pa 0 = 0 from rfl, Nat.zero_mod]
      rw [show 16 * k = n by omega, Nat.mod_self]
    have e3 : (Strip.R n k (8 * k - 1)).2 = x + 1 := by
      rw [Fin.ext_iff, fin_add_one_val' x (by omega), ha]
      simp only [Strip.R, Strip.ver, hs, show Strip.Pt 0 = 0 from rfl, add_zero]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [e1, e2] at v1
    rw [e3] at v2
    rw [show Qc n z (x + 1) - Qc n z x = (Qc n z (x + 1) - Qc n z (Strip.R n k (8 * k - 1)).1)
        + (Qc n z (Strip.R n k (8 * k - 1)).1 - Qc n z x) by abel, v1, v2]
    abel

set_option maxHeartbeats 1000000 in
/-- The side `x → x + 1`, `x = 8k + t`, of the first half. -/
theorem side_R (x : Fin n) (hx1 : 12 * k + 1 ≤ x.val) :
    Qc n z (x + 1) - Qc n z x =
      -(e (θ k z (JhiT (x.val - 8 * k) - 8 * k - 1 + 1)) - e (θ k z (JhiT (x.val - 8 * k) - 8 * k - 1))) := by
  obtain ⟨t, ht⟩ : ∃ t, x.val = 8 * k + t := ⟨x.val - 8 * k, by omega⟩
  have hxn : 8 * k + t < n := ht ▸ x.isLt
  rw [ht, show 8 * k + t - 8 * k = t by omega]
  have ht1 : 4 * k + 1 ≤ t := by omega
  have ht2 : t ≤ 8 * k - 1 := by omega
  have hra := Nat.mod_lt t (show 4 > 0 by norm_num)
  obtain ⟨hT0, hT1, hT2, hT3⟩ := JT_vals t
  have c4 : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  have hhi : JhiT t ≤ 16 * k - 2 ∧ JloT t ≤ JhiT t ∧ 8 * k + 1 ≤ JloT t := by
    rcases c4 with hc | hc | hc | hc
    · rw [(hT0 hc).1, (hT0 hc).2]; omega
    · rw [(hT1 hc).1, (hT1 hc).2]; omega
    · rw [(hT2 hc).1, (hT2 hc).2]; omega
    · rw [(hT3 hc).1, (hT3 hc).2]; omega
  obtain ⟨hi, hhi_def⟩ : ∃ hi, hi = JhiT t - 8 * k - 1 := ⟨_, rfl⟩
  rw [← hhi_def]
  have hJ : JhiT t % 8 = 0 ∨ JhiT t % 8 = 3 ∨ JhiT t % 8 = 5 ∨ JhiT t % 8 = 6 := by
    rcases c4 with hc | hc | hc | hc
    · rw [(hT0 hc).2]; omega
    · rw [(hT1 hc).2]; omega
    · rw [(hT2 hc).2]; omega
    · rw [(hT3 hc).2]; omega
  obtain ⟨hPa, hPt⟩ := P_succ_t (JhiT t) hJ
  have hPt_hi : Strip.Pt (JhiT t) = t := (Pt_eq_iff t _ (Or.inl (by omega))).mpr ⟨hhi.2.1, le_rfl⟩
  have r1 := R_first hk hn hi (by omega)
  have r2 := R_first hk hn (hi + 1) (by omega)
  rw [show 8 * k + 1 + hi = JhiT t by omega] at r1
  rw [show 8 * k + 1 + (hi + 1) = JhiT t + 1 by omega] at r2
  have e1 : (Strip.R n k hi).2 = x := by rw [Fin.ext_iff, r1.2, hPt_hi, ht, Nat.mod_eq_of_lt (by omega)]
  have e2 : (Strip.R n k (hi + 1)).2 = x + 1 := by
    rw [Fin.ext_iff, r2.2, hPt, hPt_hi, fin_add_one_val, ht]; ring_nf
  have e3 : (Strip.R n k (hi + 1)).1 = (Strip.R n k hi).1 := Fin.ext (by rw [r1.1, r2.1, hPa])
  have v1 := rung_e k hk hn z hc hi (by omega)
  have v2 := rung_e k hk hn z hc (hi + 1) (by omega)
  rw [e1] at v1
  rw [e2, e3] at v2
  rw [show Qc n z (x + 1) - Qc n z x = (Qc n z (x + 1) - Qc n z (Strip.R n k hi).1)
      - (Qc n z x - Qc n z (Strip.R n k hi).1) by abel, v1, v2]
  abel

end sides

end Chiquipoli.Family.Trig.P1
