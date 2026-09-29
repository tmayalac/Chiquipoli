/-
# Lemma R: the rungs of the strip turn by exactly `z`, for every `n = 16k`

With `Φ_κ = (sin κz, cos κz)`, the rung `ρ_i` of the strip (`Strip.R`), oriented
from its `a`-end to its `t`-end, is

    −Φ_{8k−1−i}   for i ≤ 8k − 2,        +Φ_{8k−1−i}   for i ≥ 8k − 1

(`rung_vec`). Consecutive rungs thus differ by a rotation by `z`, except at the
junction `i = 8k − 2 → 8k − 1`, where the orientation flips. This is Lemma R of
the notes on Problems 1–3; both the multipliers (Problem 3) and the width
function (Problem 1) are built on it.

The proof reads the rung off the layout (`ConstructorAll`). In the first half a
rung joins `midRole d` to `lowRole y`, and the vector between them is `−Φ_{d+1+y}`
(`role_vec`); in the second half it is the mirror image of such a pair.
-/
import ChiquipoliFamily.Trig.ConstructorAll

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig.RungVec

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Tm

variable (z : ℝ)

/-- `Φ_κ = (sin κz, cos κz)`. -/
noncomputable def Φ (κ : ℝ) : ℝ × ℝ := (sin (κ * z), cos (κ * z))

/-! ## The chords of a block, as vectors -/

lemma pm_eval (i : ℕ) : (pm i).eval z = (-1 : ℝ) ^ i := rfl

lemma fan_vec_r (i : ℕ) : ev z (tr i) - ev z (tq i) = (-((-1 : ℝ) ^ i)) • Φ z (4 * i + 2) := by
  simp only [ev, tr, tq, Tm.eval, Φ, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  constructor <;> ring
lemma fan_vec_u (i : ℕ) : ev z (tu i) - ev z (tq i) = (-((-1 : ℝ) ^ i)) • Φ z (4 * i + 3) := by
  simp only [ev, tu, tq, Tm.eval, Φ, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  constructor <;> ring
lemma fan_vec_t (i : ℕ) : ev z (tt i) - ev z (tq i) = (-((-1 : ℝ) ^ i)) • Φ z (4 * i + 1) := by
  simp only [ev, tt, tq, Tm.eval, Φ, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  constructor <;> ring

lemma fan0_vec_r : ev z tr0 - ev z tq0 = (-1 : ℝ) • Φ z 2 := by
  simp only [ev, tr0, tq0, Tm.eval, Φ, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  constructor <;> ring
lemma fan0_vec_u : ev z tu0 - ev z tq0 = (-1 : ℝ) • Φ z 3 := by
  simp only [ev, tu0, tq0, Tm.eval, Φ, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  constructor <;> ring
lemma fan0_vec_t : ev z tOrigin - ev z tq0 = (-1 : ℝ) • Φ z 1 := by
  simp only [ev, tOrigin, tq0, Tm.eval, Φ, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  constructor <;> ring

/-- The cross chord `u_i → t_{i+1}` is `(−1)^i Φ_{4i+4}`. -/
lemma cross_vec (hc : cos (2 * z) ≠ 0) (i : ℕ) :
    ev z (tt (i + 1)) - ev z (tu i) = ((-1 : ℝ) ^ i) • Φ z (4 * i + 4) := by
  have hA := blockA z i hc
  have hB := blockB z i hc
  have p : ((-1 : ℝ) ^ (i + 1)) = -((-1) ^ i) := by rw [pow_succ]; ring
  have hs := sin_add_sub_z ((4 * (i : ℝ) + 4) * z) z
  have hcz := cos_add_sub_z ((4 * (i : ℝ) + 4) * z) z
  have e5 : (4 * ((i + 1 : ℕ) : ℝ) + 1) * z = (4 * (i : ℝ) + 4) * z + z := by push_cast; ring
  have e3 : (4 * (i : ℝ) + 3) * z = (4 * (i : ℝ) + 4) * z - z := by ring
  simp only [ev, tt, tu, Tm.eval, Φ, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  rw [e5, e3, pow_succ] at *
  rw [p] at hA hB
  constructor
  · push_cast; linear_combination hA + ((-1) ^ i) * hs
  · push_cast; linear_combination hB + ((-1) ^ i) * hcz

lemma cross0_vec (hc : cos (2 * z) ≠ 0) : ev z (tt 1) - ev z tu0 = Φ z 4 := by
  have h := cross_vec z hc 0
  have e : ev z tu0 = ev z (tu 0) := by
    simp only [ev, tu, tu0, Tm.eval, Prod.ext_iff]
    rw [tXa_zero, tXb_zero]; simp
  rw [e, h]; simp

/-! ## The vector of a chord, from the roles -/

/-- **A chord of the first half is `−Φ_{d+1+y}`** (same conditions as `chordLM`). -/
theorem role_vec (hc : cos (2 * z) ≠ 0) (d y : ℕ)
    (h : (y = d + 2 ∧ (d % 4 = 0 ∨ d % 4 = 1)) ∨ y = d + 1 ∨ (y = d ∧ (d % 4 = 0 ∨ d % 4 = 3))) :
    ev z (lowRole y) - ev z (midRole d) = (-1 : ℝ) • Φ z ((d : ℝ) + 1 + y) := by
  obtain ⟨s, c, hc4, rfl⟩ := split4 d
  have ev2 : ((-1 : ℝ) ^ (2 * s)) = 1 := by rw [pow_mul]; simp
  have od2 : ((-1 : ℝ) ^ (2 * s + 1)) = -1 := by rw [pow_succ, pow_mul]; simp
  interval_cases c
  · rw [show 4 * s + 0 = 4 * s by ring, midRole0] at *
    rcases h with ⟨rfl, -⟩ | rfl | ⟨rfl, -⟩
    · rw [lowRole2]
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · rw [U0, Q0, fan0_vec_u]; norm_num
      · rw [U_pos (by omega), Q_pos (by omega), fan_vec_u, ev2]; push_cast; ring_nf
    · rw [lowRole1]
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · rw [Rr0, Q0, fan0_vec_r]; norm_num
      · rw [Rr_pos (by omega), Q_pos (by omega), fan_vec_r, ev2]; push_cast; ring_nf
    · rw [lowRole0]
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · rw [T0, Q0, fan0_vec_t]; norm_num
      · rw [T_pos (by omega), Q_pos (by omega), fan_vec_t, ev2]; push_cast; ring_nf
  · rw [midRole1, T_pos (by omega)]
    rcases h with ⟨rfl, -⟩ | rfl | ⟨rfl, h⟩
    · rw [show 4 * s + 1 + 2 = 4 * s + 3 by ring, lowRole3, Q_pos (by omega),
        show ev z (tq (2 * s + 1)) - ev z (tt (2 * s + 1)) = -(ev z (tt (2 * s + 1)) - ev z (tq (2 * s + 1))) by abel,
        fan_vec_t, od2]
      simp only [Φ, Prod.ext_iff, Prod.neg_mk, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg,
        smul_eq_mul]
      push_cast; constructor <;> ring_nf
    · rw [show 4 * s + 1 + 1 = 4 * s + 2 by ring, lowRole2]
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · rw [U0, show 2 * 0 + 1 = 1 by rfl,
          show ev z tu0 - ev z (tt 1) = -(ev z (tt 1) - ev z tu0) by abel, cross0_vec z hc]
        simp only [Φ, Prod.ext_iff, Prod.neg_mk, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg,
          smul_eq_mul]
        push_cast; constructor <;> ring_nf
      · rw [U_pos (by omega),
          show ev z (tu (2 * s)) - ev z (tt (2 * s + 1)) = -(ev z (tt (2 * s + 1)) - ev z (tu (2 * s))) by abel,
          cross_vec z hc, ev2]
        simp only [Φ, Prod.ext_iff, Prod.neg_mk, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg,
          smul_eq_mul]
        push_cast; constructor <;> ring_nf
    · omega
  · rw [midRole2, Rr_pos (by omega)]
    rcases h with ⟨rfl, h⟩ | rfl | ⟨rfl, h⟩
    · omega
    · rw [show 4 * s + 2 + 1 = 4 * s + 3 by ring, lowRole3, Q_pos (by omega),
        show ev z (tq (2 * s + 1)) - ev z (tr (2 * s + 1)) = -(ev z (tr (2 * s + 1)) - ev z (tq (2 * s + 1))) by abel,
        fan_vec_r, od2]
      simp only [Φ, Prod.ext_iff, Prod.neg_mk, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg,
        smul_eq_mul]
      push_cast; constructor <;> ring_nf
    · omega
  · rw [midRole3, U_pos (by omega)]
    rcases h with ⟨rfl, h⟩ | rfl | ⟨rfl, -⟩
    · omega
    · rw [show 4 * s + 3 + 1 = 4 * (s + 1) by ring, lowRole0, T_pos (by omega),
        show 2 * (s + 1) = 2 * s + 1 + 1 by ring, cross_vec z hc, od2]
      simp only [Φ, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      push_cast; constructor <;> ring_nf
    · rw [lowRole3, Q_pos (by omega),
        show ev z (tq (2 * s + 1)) - ev z (tu (2 * s + 1)) = -(ev z (tu (2 * s + 1)) - ev z (tq (2 * s + 1))) by abel,
        fan_vec_u, od2]
      simp only [Φ, Prod.ext_iff, Prod.neg_mk, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg,
        smul_eq_mul]
      push_cast; constructor <;> ring_nf


/-! ## Lemma R along the strip -/

open Chiquipoli.Family.Trig.Strip in
lemma Pa_add_Pt (j : ℕ) : Pa j + Pt j = j := by
  have hq := Nat.div_add_mod j 8
  have hr := Nat.mod_lt j (show 8 > 0 by norm_num)
  simp only [Pa, Pt]
  generalize hR : j % 8 = r at *
  interval_cases r <;> simp only [da, dt] <;> omega

open Chiquipoli.Family.Trig.Strip in
lemma Pa_Pt_hi (k j : ℕ) (hj : 8 * k < j) (hj2 : j < 16 * k) : 4 * k ≤ Pa j ∧ 4 * k < Pt j := by
  have hq := Nat.div_add_mod j 8
  have hr := Nat.mod_lt j (show 8 > 0 by norm_num)
  simp only [Pa, Pt]
  generalize hR : j % 8 = r at *
  interval_cases r <;> simp only [da, dt] <;> omega

open Chiquipoli.Family.Trig.Strip in
lemma Pa_Pt_lo (k j : ℕ) (hk : 1 ≤ k) (hj : j < 8 * k) : Pa j < 4 * k ∧ Pt j ≤ 4 * k ∧ (Pt j = 0 → j = 0) := by
  have hq := Nat.div_add_mod j 8
  have hr := Nat.mod_lt j (show 8 > 0 by norm_num)
  simp only [Pa, Pt]
  generalize hR : j % 8 = r at *
  interval_cases r <;> simp only [da, dt] <;> omega

lemma mir_sub (p q : ℝ × ℝ) : mir p - mir q = mir (p - q) := by
  simp only [mir, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]; exact ⟨by ring, trivial⟩

/-- **Lemma R.** The rung `ρ_i`, from its `a`-end to its `t`-end, is
`−Φ_{8k−1−i}` before the junction and `+Φ_{8k−1−i}` after it. -/
theorem rung_vec (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) (hc : cos (2 * z) ≠ 0)
    (i : ℕ) (hi : i < 16 * k - 1) :
    Qc n z (Strip.R n k i).2 - Qc n z (Strip.R n k i).1 =
      (if i + 1 < 8 * k then (-1 : ℝ) else 1) • Φ z (8 * (k : ℝ) - 1 - i) := by
  rw [ConstructorAll.Qc_eq z k hk hn, ConstructorAll.Qc_eq z k hk hn]
  subst hn
  obtain ⟨hlt, hne⟩ := Strip.Sj_lt k i hi
  have hsum := Pa_add_Pt (Strip.Sj k i)
  have hΔ := Strip.P_delta k _ hlt hne
  simp only [Strip.R, Strip.ver]
  set j := Strip.Sj k i with hj
  set a := Strip.Pa j
  set t := Strip.Pt j
  split_ifs with hh
  · -- first half
    have hjv : j = 8 * k + 1 + i := by rw [hj]; unfold Strip.Sj; rw [if_pos hh]
    obtain ⟨ha4, ht4⟩ := Pa_Pt_hi k j (by omega) hlt
    have ha8 := Strip.Pa_lt k j hlt
    have ht8 : t ≤ 8 * k := by
      rcases Nat.lt_or_ge j (16 * k - 1) with h | h
      · exact (Strip.Pt_lt k j h).le
      · have := (Strip.P_last k hk).2
        have hj' : j = 16 * k - 1 := by omega
        simp only [t, hj', this, le_refl]
    rw [Nat.mod_eq_of_lt (by omega : a < 16 * k), P_mid z k a ha4 ha8]
    have hT : ev z (spec k ((8 * k + t) % (16 * k))) = ev z (lowRole (8 * k - t)) := by
      rcases Nat.lt_or_ge t (8 * k) with h | h
      · rw [Nat.mod_eq_of_lt (by omega), P_hi_low z k _ (by omega) (by omega),
          show 16 * k - (8 * k + t) = 8 * k - t by omega]
      · rw [show t = 8 * k by omega, show 8 * k + 8 * k = 16 * k by ring, Nat.mod_self,
          P_low z k 0 (by omega), Nat.sub_self, lowRole_zero, mir_origin]
    rw [hT, role_vec z hc _ _ (by omega)]
    congr 2
    have : ((8 * k - 1 - a : ℕ) : ℝ) + 1 + ((8 * k - t : ℕ) : ℝ) = 8 * (k : ℝ) - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      have : (a : ℝ) + t = 8 * k + 1 + i := by exact_mod_cast (by omega : a + t = 8 * k + 1 + i)
      push_cast; linarith
    rw [this]
  · -- second half
    have hjv : j = i + 1 - 8 * k := by rw [hj]; unfold Strip.Sj; rw [if_neg hh]
    obtain ⟨ha4, ht4, ht0⟩ := Pa_Pt_lo k j hk (by omega)
    rw [Nat.mod_eq_of_lt (by omega : a < 16 * k), P_low z k a ha4, Nat.mod_eq_of_lt (by omega)]
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · have hj0 := ht0 h0
      have ha0 : a = 0 := by omega
      rw [h0, add_zero, P_top, ha0, lowRole_zero, mir_origin]
      have hi' : (i : ℝ) = 8 * k - 1 := by
        have : i = 8 * k - 1 := by omega
        rw [this, Nat.cast_sub (by omega)]; push_cast; ring
      simp only [ev, tTop, tOrigin, Tm.eval, Φ, hi', Prod.ext_iff, Prod.fst_sub, Prod.snd_sub,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      norm_num
    · rw [P_hi_mid z k _ (by omega) (by omega), show 8 * k - 1 - (16 * k - (8 * k + t)) = t - 1 by omega,
        mir_sub]
      have hv := role_vec z hc (t - 1) a (by omega)
      have hv' : ev z (midRole (t - 1)) - ev z (lowRole a) = Φ z (((t - 1 : ℕ) : ℝ) + 1 + a) := by
        rw [show ev z (midRole (t - 1)) - ev z (lowRole a) = -(ev z (lowRole a) - ev z (midRole (t - 1))) by abel,
          hv, neg_smul, one_smul, neg_neg]
      rw [hv']
      have e : ((t - 1 : ℕ) : ℝ) + 1 + a = (j : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        have : (a : ℝ) + t = j := by exact_mod_cast (by omega : a + t = j)
        push_cast; linarith
      have e2 : (8 * (k : ℝ) - 1 - i) = -(j : ℝ) := by
        have : (j : ℝ) + 8 * k = i + 1 := by exact_mod_cast (by omega : j + 8 * k = i + 1)
        linarith
      rw [e, e2]
      simp only [mir, Φ, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, one_mul, neg_mul,
        sin_neg, cos_neg]
      simp

end Chiquipoli.Family.Trig.RungVec
