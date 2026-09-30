/-
# Problem 3: equilibrium at the vertices of the first half

The `a`-end `a` carries the rungs with `P`-index `J ∈ [JloA a, JhiA a]`, and the
`t`-end `t` those with `J ∈ [JloT t, JhiT t]` (`Pa_eq_iff`, `Pt_eq_iff`). With
`i = J − 8k − 1` these are runs of the strip, and `force_L` and `force_R` apply at
every interior vertex of the first half.
-/
import ChiquipoliFamily.AllN.Multipliers.Stress

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Chiquipoli.Family.Trig.P3

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Chiquipoli.Family.Trig.RungVec

/-! ## Runs of rungs -/

def JloA (a : ℕ) : ℕ := if a % 4 = 2 ∨ a % 4 = 3 then 2 * a - 1 else 2 * a
def JhiA (a : ℕ) : ℕ := if a % 4 = 0 ∨ a % 4 = 3 then 2 * a + 1 else 2 * a
def JloT (t : ℕ) : ℕ := if t % 4 = 0 ∨ t % 4 = 1 then 2 * t - 1 else 2 * t
def JhiT (t : ℕ) : ℕ := if t % 4 = 1 ∨ t % 4 = 2 then 2 * t + 1 else 2 * t

open Strip in
lemma Pa_eq_iff (a J : ℕ) : Pa J = a ↔ JloA a ≤ J ∧ J ≤ JhiA a := by
  have hq := Nat.div_add_mod J 8
  have hr := Nat.mod_lt J (show 8 > 0 by norm_num)
  have hqa := Nat.div_add_mod a 4
  have hra := Nat.mod_lt a (show 4 > 0 by norm_num)
  simp only [Pa, JloA, JhiA]
  generalize hR : J % 8 = r at *
  interval_cases r <;> simp only [da] <;> split_ifs <;> omega

open Strip in
lemma Pt_eq_iff (t J : ℕ) (hJ : 1 ≤ J ∨ t = 0) : Pt J = t ↔ JloT t ≤ J ∧ J ≤ JhiT t := by
  have hq := Nat.div_add_mod J 8
  have hr := Nat.mod_lt J (show 8 > 0 by norm_num)
  have hqa := Nat.div_add_mod t 4
  have hra := Nat.mod_lt t (show 4 > 0 by norm_num)
  simp only [Pt, JloT, JhiT]
  generalize hR : J % 8 = r at *
  interval_cases r <;> simp only [dt] <;> split_ifs <;> omega

/-- `ε_i` by the residue of `i`. -/
lemma eps_val (i : ℕ) (hi : 1 ≤ i) :
    eps i = if i % 8 = 2 ∨ i % 8 = 4 ∨ i % 8 = 7 then 1
      else if i % 8 = 0 ∨ i % 8 = 3 ∨ i % 8 = 6 then -1 else 0 := by
  have h8 := Nat.mod_lt i (show 8 > 0 by norm_num)
  have e : (i - 1) % 8 = (i % 8 + 7) % 8 := by omega
  unfold eps
  have hA := typA_iff (i - 1)
  have hB := typA_iff i
  have hA' := typA_false_iff (i - 1)
  have hB' := typA_false_iff i
  generalize hR : i % 8 = r at *
  interval_cases r <;> simp only [e] at hA hA' <;> norm_num at hA hA' hB hB' <;>
    simp [hA, hB, hA', hB']

lemma sum_Icc_1 {V : Type*} [AddCommMonoid V] (f : ℕ → V) (a : ℕ) : ∑ i ∈ Finset.Icc a a, f i = f a := by simp
lemma sum_Icc_2 {V : Type*} [AddCommMonoid V] (f : ℕ → V) (a : ℕ) : ∑ i ∈ Finset.Icc a (a + 1), f i = f a + f (a + 1) := by
  rw [Finset.sum_Icc_succ_top (by omega)]; simp
lemma sum_Icc_3 {V : Type*} [AddCommMonoid V] (f : ℕ → V) (a : ℕ) : ∑ i ∈ Finset.Icc a (a + 2), f i = f a + f (a + 1) + f (a + 2) := by
  rw [show a + 2 = a + 1 + 1 by ring, Finset.sum_Icc_succ_top (by omega), sum_Icc_2]

lemma JA_vals (a : ℕ) :
    (a % 4 = 0 → JloA a = 2 * a ∧ JhiA a = 2 * a + 1) ∧ (a % 4 = 1 → JloA a = 2 * a ∧ JhiA a = 2 * a) ∧
    (a % 4 = 2 → JloA a = 2 * a - 1 ∧ JhiA a = 2 * a) ∧ (a % 4 = 3 → JloA a = 2 * a - 1 ∧ JhiA a = 2 * a + 1) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [JloA, JhiA, h]

lemma JT_vals (t : ℕ) :
    (t % 4 = 0 → JloT t = 2 * t - 1 ∧ JhiT t = 2 * t) ∧ (t % 4 = 1 → JloT t = 2 * t - 1 ∧ JhiT t = 2 * t + 1) ∧
    (t % 4 = 2 → JloT t = 2 * t ∧ JhiT t = 2 * t + 1) ∧ (t % 4 = 3 → JloT t = 2 * t ∧ JhiT t = 2 * t) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [JloT, JhiT, h]

/-- On an `a`-run the switches cancel. -/
lemma eps_run_A (k a : ℕ) (ha : 4 * k + 1 ≤ a) :
    ∑ i ∈ Finset.Icc (JloA a - 8 * k - 1) (JhiA a - 8 * k - 1), eps i = 0 := by
  have hra := Nat.mod_lt a (show 4 > 0 by norm_num)
  obtain ⟨h0, h1, h2, h3⟩ := JA_vals a
  rcases (show a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 by omega) with hc | hc | hc | hc
  · rw [(h0 hc).1, (h0 hc).2, show 2 * a + 1 - 8 * k - 1 = (2 * a - 8 * k - 1) + 1 by omega, sum_Icc_2,
      eps_val _ (by omega), eps_val _ (by omega)]
    rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]; norm_num
  · rw [(h1 hc).1, (h1 hc).2, sum_Icc_1, eps_val _ (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [(h2 hc).1, (h2 hc).2, show 2 * a - 8 * k - 1 = (2 * a - 1 - 8 * k - 1) + 1 by omega, sum_Icc_2,
      eps_val _ (by omega), eps_val _ (by omega)]
    rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]; norm_num
  · rw [(h3 hc).1, (h3 hc).2, show 2 * a + 1 - 8 * k - 1 = (2 * a - 1 - 8 * k - 1) + 2 by omega, sum_Icc_3,
      eps_val _ (by omega), eps_val _ (by omega), eps_val _ (by omega)]
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; norm_num

/-- On a `t`-run the switches cancel. -/
lemma eps_run_T (k t : ℕ) (ht : 4 * k + 2 ≤ t) :
    ∑ i ∈ Finset.Icc (JloT t - 8 * k - 1) (JhiT t - 8 * k - 1), eps i = 0 := by
  have hra := Nat.mod_lt t (show 4 > 0 by norm_num)
  obtain ⟨h0, h1, h2, h3⟩ := JT_vals t
  rcases (show t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 by omega) with hc | hc | hc | hc
  · rw [(h0 hc).1, (h0 hc).2, show 2 * t - 8 * k - 1 = (2 * t - 1 - 8 * k - 1) + 1 by omega, sum_Icc_2,
      eps_val _ (by omega), eps_val _ (by omega)]
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]; norm_num
  · rw [(h1 hc).1, (h1 hc).2, show 2 * t + 1 - 8 * k - 1 = (2 * t - 1 - 8 * k - 1) + 2 by omega, sum_Icc_3,
      eps_val _ (by omega), eps_val _ (by omega), eps_val _ (by omega)]
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; norm_num
  · rw [(h2 hc).1, (h2 hc).2, show 2 * t + 1 - 8 * k - 1 = (2 * t - 8 * k - 1) + 1 by omega, sum_Icc_2,
      eps_val _ (by omega), eps_val _ (by omega)]
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]; norm_num
  · rw [(h3 hc).1, (h3 hc).2, sum_Icc_1, eps_val _ (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## Fin arithmetic -/

lemma fin_add_one_val' {n : ℕ} [NeZero n] (x : Fin n) (h : x.val + 1 < n) : (x + 1).val = x.val + 1 := by
  rw [fin_add_one_val, Nat.mod_eq_of_lt h]

lemma fin_sub_one_val {n : ℕ} [NeZero n] (x : Fin n) (h : 1 ≤ x.val) (hn : 2 ≤ n) : (x - 1).val = x.val - 1 := by
  rw [Fin.sub_val_of_le]
  · rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  · rw [Fin.le_def, Fin.val_one', Nat.mod_eq_of_lt (by omega)]; exact h

lemma stepOf_A (k a : ℕ) (h1 : 4 * k ≤ a) (h2 : a ≤ 8 * k - 1) : stepOf k a = JhiA a - 8 * k - 1 := by
  have hq := Nat.div_add_mod a 4
  have hr := Nat.mod_lt a (show 4 > 0 by norm_num)
  unfold stepOf JhiA
  split_ifs <;> omega

lemma stepOf_T (k t : ℕ) (hk : 1 ≤ k) (h1 : 4 * k + 1 ≤ t) (h2 : t ≤ 8 * k - 1) :
    stepOf k (8 * k + t) = JhiT t - 8 * k - 1 := by
  have hq := Nat.div_add_mod t 4
  have hr := Nat.mod_lt t (show 4 > 0 by norm_num)
  unfold stepOf JhiT
  rw [show 8 * k + t - 8 * k = t by omega]
  split_ifs <;> omega

section vertex
variable {k : ℕ} (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ} (ag : ℝ)
  (hc : cos (2 * z) ≠ 0) (hw : sin (z / 2) ≠ 0) (hcw : cos (z / 2) ≠ 0)
include hk hn hc hw hcw

/-- The `t`-end of every rung is in `[8k, 16k) ∪ {0}`. -/
lemma R_snd_range (i : ℕ) (hi : i < 16 * k - 1) :
    8 * k ≤ (Strip.R n k i).2.val ∨ (Strip.R n k i).2.val = 0 := by
  rcases Nat.lt_or_ge (i + 1) (8 * k) with h | h
  · obtain ⟨-, h2⟩ := R_first hk hn i h
    rw [h2]
    have hPt : Strip.Pt (8 * k + 1 + i) ≤ 8 * k := by
      rcases Nat.lt_or_ge (8 * k + 1 + i) (16 * k - 1) with h' | h'
      · exact (Strip.Pt_lt k _ h').le
      · rw [show 8 * k + 1 + i = 16 * k - 1 by omega]; exact (Strip.P_last k hk).2.le
    subst hn
    rcases Nat.lt_or_ge (Strip.Pt (8 * k + 1 + i)) (8 * k) with h3 | h3
    · left; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · right; rw [show 8 * k + Strip.Pt (8 * k + 1 + i) = 16 * k by omega, Nat.mod_self]
  · left; exact (R_second hk hn i h hi).2.1

set_option maxHeartbeats 1000000 in
/-- **Equilibrium at every `a`-end of the first half** other than the gap vertex `4k`. -/
theorem force_A_interior (x : Fin n) (hx1 : 4 * k + 1 ≤ x.val) (hx2 : x.val ≤ 8 * k - 1) :
    force k z ag x = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, x.val = a := ⟨_, rfl⟩
  rw [ha] at hx1 hx2
  have hxn : a < n := ha ▸ x.isLt
  have hra := Nat.mod_lt a (show 4 > 0 by norm_num)
  obtain ⟨hA0, hA1, hA2, hA3⟩ := JA_vals a
  have hlo : 8 * k + 2 ≤ JloA a := by
    rcases (show a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 by omega) with hc | hc | hc | hc
    · rw [(hA0 hc).1]; omega
    · rw [(hA1 hc).1]; omega
    · rw [(hA2 hc).1]; omega
    · rw [(hA3 hc).1]; omega
  have hhi : JhiA a ≤ 16 * k - 1 ∧ JloA a ≤ JhiA a := by
    rcases (show a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 by omega) with hc | hc | hc | hc
    · rw [(hA0 hc).1, (hA0 hc).2]; omega
    · rw [(hA1 hc).1, (hA1 hc).2]; omega
    · rw [(hA2 hc).1, (hA2 hc).2]; omega
    · rw [(hA3 hc).1, (hA3 hc).2]; omega
  obtain ⟨lo, hlo_def⟩ : ∃ lo, lo = JloA a - 8 * k - 1 := ⟨_, rfl⟩
  obtain ⟨hi, hhi_def⟩ : ∃ hi, hi = JhiA a - 8 * k - 1 := ⟨_, rfl⟩
  -- the rungs at `x`
  have hinc1 : ∀ i < n - 1, ((Strip.R n k i).1 = x ↔ lo ≤ i ∧ i ≤ hi) := by
    intro i hi'
    rw [Fin.ext_iff, ha]
    rcases Nat.lt_or_ge (i + 1) (8 * k) with h | h
    · rw [(R_first hk hn i h).1, Pa_eq_iff]; omega
    · have := (R_second hk hn i h (by omega)).1
      constructor
      · intro h'; omega
      · intro h'; omega
  have hinc2 : ∀ i < n - 1, (Strip.R n k i).2 ≠ x := by
    intro i hi' h
    have := R_snd_range hk hn hc hw hcw i (by omega)
    rw [h, ha] at this; omega
  -- the two sides
  have hsx : sigS k z ag x.val = -tau k z ag hi / ell z := by
    unfold sigS
    rw [ha, if_neg (by omega), if_pos (show firstSide k a from Or.inl ⟨by omega, by omega⟩), stepOf_A k a (by omega) hx2,
      hhi_def]
  have hx1v : (x - 1).val = a - 1 := by rw [fin_sub_one_val x (by omega) (by omega), ha]
  have hsx1 : sigS k z ag (x - 1).val = -tau k z ag (lo - 1) / ell z := by
    rw [hx1v]
    unfold sigS
    rw [if_neg (by omega), if_pos (show firstSide k (a - 1) from Or.inl ⟨by omega, by omega⟩),
      stepOf_A k (a - 1) (by omega) (by omega), hlo_def]
    congr 3
    have := JA_vals (a - 1)
    rcases (show a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 by omega) with hc | hc | hc | hc
    · rw [(this.2.2.2 (by omega)).2, (hA0 hc).1]; omega
    · rw [(this.1 (by omega)).2, (hA1 hc).1]; omega
    · rw [(this.2.1 (by omega)).2, (hA2 hc).1]; omega
    · rw [(this.2.2.1 (by omega)).2, (hA3 hc).1]; omega
  -- the rung `lo − 1` shares the `t`-end of `lo`
  have hJ' : (JloA a - 1) % 8 = 1 ∨ (JloA a - 1) % 8 = 2 ∨ (JloA a - 1) % 8 = 4 ∨ (JloA a - 1) % 8 = 7 := by
    rcases (show a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 by omega) with hc | hc | hc | hc
    · rw [(hA0 hc).1]; omega
    · rw [(hA1 hc).1]; omega
    · rw [(hA2 hc).1]; omega
    · rw [(hA3 hc).1]; omega
  obtain ⟨hPa', hPt'⟩ := P_succ_a (JloA a - 1) hJ'
  rw [show JloA a - 1 + 1 = JloA a by omega] at hPa' hPt'
  have hPa_lo : Strip.Pa (JloA a) = a := (Pa_eq_iff a _).mpr ⟨le_rfl, hhi.2⟩
  have hvx1 : Qc n z (x - 1) - Qc n z x = -(e (θ k z (lo - 1 + 1)) - e (θ k z (lo - 1))) := by
    have r1 := R_first hk hn (lo - 1) (by omega)
    have r2 := R_first hk hn lo (by omega)
    rw [show 8 * k + 1 + (lo - 1) = JloA a - 1 by omega] at r1
    rw [show 8 * k + 1 + lo = JloA a by omega] at r2
    have e1 : (Strip.R n k (lo - 1)).1 = x - 1 := by
      rw [Fin.ext_iff, r1.1, hx1v]; omega
    have e2 : (Strip.R n k lo).1 = x := by rw [Fin.ext_iff, r2.1, hPa_lo, ha]
    have e3 : (Strip.R n k (lo - 1)).2 = (Strip.R n k lo).2 := Fin.ext (by rw [r1.2, r2.2, ← hPt'])
    have v1 := rung_e k hk hn z hc (lo - 1) (by omega)
    have v2 := rung_e k hk hn z hc lo (by omega)
    rw [e1, e3] at v1
    rw [e2] at v2
    rw [Nat.sub_add_cancel (by omega)]
    rw [show Qc n z (x - 1) - Qc n z x = (Qc n z (Strip.R n k lo).2 - Qc n z x)
        - (Qc n z (Strip.R n k lo).2 - Qc n z (x - 1)) by abel, v1, v2]
    abel
  -- the side `x → x + 1`
  have hvx : Qc n z (x + 1) - Qc n z x = e (θ k z (hi + 1)) - e (θ k z hi) := by
    rcases Nat.lt_or_ge a (8 * k - 1) with hlt | hge
    · have hJ : JhiA a % 8 = 1 ∨ JhiA a % 8 = 2 ∨ JhiA a % 8 = 4 ∨ JhiA a % 8 = 7 := by
        rcases (show a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 by omega) with hc | hc | hc | hc
        · rw [(hA0 hc).2]; omega
        · rw [(hA1 hc).2]; omega
        · rw [(hA2 hc).2]; omega
        · rw [(hA3 hc).2]; omega
      have hhi2 : JhiA a ≤ 16 * k - 3 := by
        rcases (show a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 by omega) with hc | hc | hc | hc
        · rw [(hA0 hc).2]; omega
        · rw [(hA1 hc).2]; omega
        · rw [(hA2 hc).2]; omega
        · rw [(hA3 hc).2]; omega
      obtain ⟨hPa, hPt⟩ := P_succ_a (JhiA a) hJ
      have hPa_hi : Strip.Pa (JhiA a) = a := (Pa_eq_iff a _).mpr ⟨hhi.2, le_rfl⟩
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
      have ha' : a = 8 * k - 1 := by omega
      have hhi' : hi = 8 * k - 2 := by
        rw [hhi_def, (hA3 (by omega)).2]; omega
      rw [hhi', show 8 * k - 2 + 1 = 8 * k - 1 by omega]
      have v1 := rung_e k hk hn z hc (8 * k - 2) (by omega)
      have v2 := rung_mid k hk hn z hc
      have r1 := R_first hk hn (8 * k - 2) (by omega)
      rw [show 8 * k + 1 + (8 * k - 2) = 16 * k - 1 by omega, (Strip.P_last k hk).1, (Strip.P_last k hk).2,
        show 8 * k + 8 * k = 16 * k by ring] at r1
      have hs : Strip.Sj k (8 * k - 1) = 0 := by unfold Strip.Sj; rw [if_neg (by omega)]; omega
      have e1 : (Strip.R n k (8 * k - 2)).1 = x := by rw [Fin.ext_iff, r1.1]; omega
      have e2 : (Strip.R n k (8 * k - 2)).2 = (Strip.R n k (8 * k - 1)).1 := by
        rw [Fin.ext_iff, r1.2]
        simp only [Strip.R, Strip.ver, hs, show Strip.Pa 0 = 0 from rfl, Nat.zero_mod]
        rw [show 16 * k = n by omega, Nat.mod_self]
      have e3 : (Strip.R n k (8 * k - 1)).2 = x + 1 := by
        rw [Fin.ext_iff, fin_add_one_val' x (by omega)]
        simp only [Strip.R, Strip.ver, hs, show Strip.Pt 0 = 0 from rfl, add_zero]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [e1, e2] at v1
      rw [e3] at v2
      rw [show Qc n z (x + 1) - Qc n z x = (Qc n z (x + 1) - Qc n z (Strip.R n k (8 * k - 1)).1)
          + (Qc n z (Strip.R n k (8 * k - 1)).1 - Qc n z x) by abel, v1, v2]
      abel
  exact force_L hk hn ag hc hw hcw x lo hi (by omega) (by omega) (by omega) hinc1 hinc2 hsx hsx1 hvx hvx1
    (by rw [hlo_def, hhi_def]; exact eps_run_A k a (by omega))

set_option maxHeartbeats 1000000 in
/-- **Equilibrium at every `t`-end of the first half** other than the gap vertex
`12k + 1` and the vertex `0`. -/
theorem force_T_interior (x : Fin n) (hx1 : 12 * k + 2 ≤ x.val) :
    force k z ag x = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, x.val = 8 * k + t := ⟨x.val - 8 * k, by omega⟩
  have hxn : 8 * k + t < n := ht ▸ x.isLt
  have ht1 : 4 * k + 2 ≤ t := by omega
  have ht2 : t ≤ 8 * k - 1 := by omega
  have hra := Nat.mod_lt t (show 4 > 0 by norm_num)
  obtain ⟨hT0, hT1, hT2, hT3⟩ := JT_vals t
  have c4 : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  have hlo : 8 * k + 2 ≤ JloT t := by
    rcases c4 with hc | hc | hc | hc
    · rw [(hT0 hc).1]; omega
    · rw [(hT1 hc).1]; omega
    · rw [(hT2 hc).1]; omega
    · rw [(hT3 hc).1]; omega
  have hhi : JhiT t ≤ 16 * k - 2 ∧ JloT t ≤ JhiT t := by
    rcases c4 with hc | hc | hc | hc
    · rw [(hT0 hc).1, (hT0 hc).2]; omega
    · rw [(hT1 hc).1, (hT1 hc).2]; omega
    · rw [(hT2 hc).1, (hT2 hc).2]; omega
    · rw [(hT3 hc).1, (hT3 hc).2]; omega
  obtain ⟨lo, hlo_def⟩ : ∃ lo, lo = JloT t - 8 * k - 1 := ⟨_, rfl⟩
  obtain ⟨hi, hhi_def⟩ : ∃ hi, hi = JhiT t - 8 * k - 1 := ⟨_, rfl⟩
  have hinc1 : ∀ i < n - 1, ((Strip.R n k i).2 = x ↔ lo ≤ i ∧ i ≤ hi) := by
    intro i hi'
    rw [Fin.ext_iff, ht]
    rcases Nat.lt_or_ge (i + 1) (8 * k) with h | h
    · rw [(R_first hk hn i h).2]
      have hPt : Strip.Pt (8 * k + 1 + i) ≤ 8 * k := by
        rcases Nat.lt_or_ge (8 * k + 1 + i) (16 * k - 1) with h' | h'
        · exact (Strip.Pt_lt k _ h').le
        · rw [show 8 * k + 1 + i = 16 * k - 1 by omega]; exact (Strip.P_last k hk).2.le
      rcases Nat.lt_or_ge (Strip.Pt (8 * k + 1 + i)) (8 * k) with h3 | h3
      · rw [Nat.mod_eq_of_lt (by omega)]
        have := Pt_eq_iff t (8 * k + 1 + i) (Or.inl (by omega))
        constructor
        · intro h4; have := this.mp (by omega); omega
        · intro h4; have := this.mpr (by omega); omega
      · rw [show 8 * k + Strip.Pt (8 * k + 1 + i) = n by omega, Nat.mod_self]
        have := Pt_eq_iff t (8 * k + 1 + i) (Or.inl (by omega))
        constructor
        · intro h4; omega
        · intro h4; have := this.mpr (by omega); omega
    · have := (R_second hk hn i h (by omega)).2.2
      constructor
      · intro h'; omega
      · intro h'; omega
  have hinc2 : ∀ i < n - 1, (Strip.R n k i).1 ≠ x := by
    intro i hi' h
    rw [Fin.ext_iff, ht] at h
    rcases Nat.lt_or_ge (i + 1) (8 * k) with h' | h'
    · rw [(R_first hk hn i h').1] at h
      have := Strip.Pa_lt k (8 * k + 1 + i) (by omega); omega
    · have := (R_second hk hn i h' (by omega)).1; omega
  have hsx : sigS k z ag x.val = -tau k z ag hi / ell z := by
    unfold sigS
    rw [ht, if_neg (by omega), if_pos (show firstSide k (8 * k + t) from Or.inr ⟨by omega, by omega⟩),
      stepOf_T k t hk (by omega) ht2, hhi_def]
  have hx1v : (x - 1).val = 8 * k + (t - 1) := by rw [fin_sub_one_val x (by omega) (by omega), ht]; omega
  have hsx1 : sigS k z ag (x - 1).val = -tau k z ag (lo - 1) / ell z := by
    rw [hx1v]
    unfold sigS
    rw [if_neg (by omega), if_pos (show firstSide k (8 * k + (t - 1)) from Or.inr ⟨by omega, by omega⟩),
      stepOf_T k (t - 1) hk (by omega) (by omega), hlo_def]
    congr 3
    have := JT_vals (t - 1)
    rcases c4 with hc | hc | hc | hc
    · rw [(this.2.2.2 (by omega)).2, (hT0 hc).1]; omega
    · rw [(this.1 (by omega)).2, (hT1 hc).1]; omega
    · rw [(this.2.1 (by omega)).2, (hT2 hc).1]; omega
    · rw [(this.2.2.1 (by omega)).2, (hT3 hc).1]; omega
  -- the rung `lo − 1` shares the `a`-end of `lo`
  have hJ' : (JloT t - 1) % 8 = 0 ∨ (JloT t - 1) % 8 = 3 ∨ (JloT t - 1) % 8 = 5 ∨ (JloT t - 1) % 8 = 6 := by
    rcases c4 with hc | hc | hc | hc
    · rw [(hT0 hc).1]; omega
    · rw [(hT1 hc).1]; omega
    · rw [(hT2 hc).1]; omega
    · rw [(hT3 hc).1]; omega
  obtain ⟨hPa', hPt'⟩ := P_succ_t (JloT t - 1) hJ'
  rw [show JloT t - 1 + 1 = JloT t by omega] at hPa' hPt'
  have hPt_lo : Strip.Pt (JloT t) = t := (Pt_eq_iff t _ (Or.inl (by omega))).mpr ⟨le_rfl, hhi.2⟩
  have hvx1 : Qc n z (x - 1) - Qc n z x = e (θ k z (lo - 1 + 1)) - e (θ k z (lo - 1)) := by
    have r1 := R_first hk hn (lo - 1) (by omega)
    have r2 := R_first hk hn lo (by omega)
    rw [show 8 * k + 1 + (lo - 1) = JloT t - 1 by omega] at r1
    rw [show 8 * k + 1 + lo = JloT t by omega] at r2
    have e1 : (Strip.R n k (lo - 1)).2 = x - 1 := by
      rw [Fin.ext_iff, r1.2, hx1v, Nat.mod_eq_of_lt (by omega)]; omega
    have e2 : (Strip.R n k lo).2 = x := by
      rw [Fin.ext_iff, r2.2, hPt_lo, ht, Nat.mod_eq_of_lt (by omega)]
    have e3 : (Strip.R n k (lo - 1)).1 = (Strip.R n k lo).1 := Fin.ext (by rw [r1.1, r2.1, hPa'])
    have v1 := rung_e k hk hn z hc (lo - 1) (by omega)
    have v2 := rung_e k hk hn z hc lo (by omega)
    rw [e1, e3] at v1
    rw [e2] at v2
    rw [Nat.sub_add_cancel (by omega)]
    rw [show Qc n z (x - 1) - Qc n z x = (Qc n z (x - 1) - Qc n z (Strip.R n k lo).1)
        - (Qc n z x - Qc n z (Strip.R n k lo).1) by abel, v1, v2]
    abel
  have hvx : Qc n z (x + 1) - Qc n z x = -(e (θ k z (hi + 1)) - e (θ k z hi)) := by
    have hJ : JhiT t % 8 = 0 ∨ JhiT t % 8 = 3 ∨ JhiT t % 8 = 5 ∨ JhiT t % 8 = 6 := by
      rcases c4 with hc | hc | hc | hc
      · rw [(hT0 hc).2]; omega
      · rw [(hT1 hc).2]; omega
      · rw [(hT2 hc).2]; omega
      · rw [(hT3 hc).2]; omega
    obtain ⟨hPa, hPt⟩ := P_succ_t (JhiT t) hJ
    have hPt_hi : Strip.Pt (JhiT t) = t := (Pt_eq_iff t _ (Or.inl (by omega))).mpr ⟨hhi.2, le_rfl⟩
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
  exact force_R hk hn ag hc hw hcw x lo hi (by omega) (by omega) (by omega) hinc1 hinc2 hsx hsx1 hvx hvx1
    (by rw [hlo_def, hhi_def]; exact eps_run_T k t ht1)

end vertex

end Chiquipoli.Family.Trig.P3
