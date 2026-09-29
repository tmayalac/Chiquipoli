/-
# Problem 3: the mirror symmetry `σ(x) = n − x`

The published polygon is symmetric, `p_{−x} = mir(p_x)` with `mir(u, v) = (−u, v)`
(`Qc_neg`). The strip is symmetric too: `σ(ρ_i) = ρ_{n−2−i}` (`rung_refl`). The
stress is symmetric by construction (`sigS_sym`, `lamR_sym`). Hence
`force(−x) = mir(force x)` (`force_neg`), and equilibrium on the first half gives
equilibrium on the second.
-/
import ChiquipoliFamily.Trig.P3Vertices

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Chiquipoli.Family.Trig.P3

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Chiquipoli.Family.Trig.RungVec

/-! ## `mir` -/

lemma mir_mir (p : ℝ × ℝ) : mir (mir p) = p := by simp [mir]
lemma mir_add' (p q : ℝ × ℝ) : mir (p + q) = mir p + mir q := by
  ext <;> simp [mir]; ring
lemma mir_smul' (c : ℝ) (p : ℝ × ℝ) : mir (c • p) = c • mir p := by
  ext <;> simp [mir]
lemma mir_zero' : mir 0 = 0 := by simp [mir]
lemma mir_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ) : mir (∑ i ∈ s, f i) = ∑ i ∈ s, mir (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mir_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mir_add', ih]

/-! ## The polygon is symmetric -/

lemma neg_val {n : ℕ} [NeZero n] (x : Fin n) : (-x).val = (n - x.val) % n := by
  rw [Fin.neg_def]

theorem Qc_neg (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) (z : ℝ) (x : Fin n) :
    Qc n z (-x) = mir (Qc n z x) := by
  rw [ConstructorAll.Qc_eq z k hk hn, ConstructorAll.Qc_eq z k hk hn, neg_val]
  have hx := x.isLt
  subst hn
  obtain ⟨v, hv⟩ : ∃ v, x.val = v := ⟨_, rfl⟩
  rw [hv] at hx ⊢
  rcases Nat.eq_zero_or_pos v with h0 | h0
  · subst h0
    rw [Nat.sub_zero, Nat.mod_self, P_low z k 0 (by omega), lowRole_zero, mir_origin, mir_origin]
  rw [Nat.mod_eq_of_lt (by omega)]
  rcases Nat.lt_or_ge v (4 * k) with r1 | r1
  · rw [P_low z k v r1, P_hi_low z k _ (by omega) (by omega), show 16 * k - (16 * k - v) = v by omega, mir_mir]
  rcases Nat.lt_or_ge v (8 * k) with r2 | r2
  · rw [P_mid z k v r1 r2, P_hi_mid z k _ (by omega) (by omega), show 16 * k - (16 * k - v) = v by omega]
  rcases Nat.eq_or_lt_of_le r2 with r3 | r3
  · rw [← r3, show 16 * k - 8 * k = 8 * k by omega, P_top, mir_top]
  rcases Nat.lt_or_ge (16 * k - v) (4 * k) with r4 | r4
  · rw [P_hi_low z k v r3 r4, P_low z k _ r4]
  · rw [P_hi_mid z k v r3 r4, P_mid z k _ r4 (by omega), mir_mir]

/-! ## The strip is symmetric -/

open Strip in
lemma P_refl (J : ℕ) (k : ℕ) (h1 : 1 ≤ J) (h2 : J ≤ 16 * k - 1) :
    Pa (16 * k - J) + Pt J = 8 * k ∧ Pt (16 * k - J) + Pa J = 8 * k := by
  have hq := Nat.div_add_mod J 8
  have hr := Nat.mod_lt J (show 8 > 0 by norm_num)
  have hq' := Nat.div_add_mod (16 * k - J) 8
  have hr' := Nat.mod_lt (16 * k - J) (show 8 > 0 by norm_num)
  simp only [Pa, Pt]
  generalize hR : J % 8 = r at *
  interval_cases r
  · rw [show (16 * k - J) % 8 = 0 by omega, show (16 * k - J) / 8 = 2 * k - J / 8 by omega]
    simp only [da, dt]; omega
  all_goals
    rw [show (16 * k - J) / 8 = 2 * k - J / 8 - 1 by omega]
    first
    | (rw [show (16 * k - J) % 8 = 7 by omega]; simp only [da, dt]; omega)
    | (rw [show (16 * k - J) % 8 = 6 by omega]; simp only [da, dt]; omega)
    | (rw [show (16 * k - J) % 8 = 5 by omega]; simp only [da, dt]; omega)
    | (rw [show (16 * k - J) % 8 = 4 by omega]; simp only [da, dt]; omega)
    | (rw [show (16 * k - J) % 8 = 3 by omega]; simp only [da, dt]; omega)
    | (rw [show (16 * k - J) % 8 = 2 by omega]; simp only [da, dt]; omega)
    | (rw [show (16 * k - J) % 8 = 1 by omega]; simp only [da, dt]; omega)

lemma contrib_swap {n : ℕ} (p : Cfg n) (a b y : Fin n) (hab : a ≠ b) :
    contrib p (a, b) y = contrib p (b, a) y := by
  unfold contrib
  by_cases h1 : a = y <;> by_cases h2 : b = y
  · exact absurd (h1.trans h2.symm) hab
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

lemma contrib_neg {n : ℕ} [NeZero n] (p : Cfg n) (hp : ∀ y, p (-y) = mir (p y)) (a b y : Fin n) :
    contrib p (-a, -b) (-y) = mir (contrib p (a, b) y) := by
  unfold contrib
  simp only [neg_inj]
  split_ifs <;> simp [hp, mir, mir_zero'] <;> (try ring) <;> rfl

section sym
variable {k : ℕ} (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k)
include hk hn

/-- **The strip is symmetric:** `σ(ρ_i) = ρ_{n−2−i}`. -/
theorem rung_refl (i : ℕ) (hi : i < 16 * k - 1) :
    ((Strip.R n k (16 * k - 2 - i)).1 = -(Strip.R n k i).2 ∧ (Strip.R n k (16 * k - 2 - i)).2 = -(Strip.R n k i).1)
    ∨ (i = 8 * k - 1 ∧ Strip.R n k (16 * k - 2 - i) = Strip.R n k i) := by
  rcases eq_or_ne i (8 * k - 1) with h | h
  · right; exact ⟨h, by rw [h, show 16 * k - 2 - (8 * k - 1) = 8 * k - 1 by omega]⟩
  left
  have hS : Strip.Sj k (16 * k - 2 - i) = 16 * k - Strip.Sj k i := by
    unfold Strip.Sj; split_ifs <;> omega
  obtain ⟨hlt, hne⟩ := Strip.Sj_lt k i hi
  have hS1 : 1 ≤ Strip.Sj k i := by unfold Strip.Sj; split_ifs <;> omega
  obtain ⟨e1, e2⟩ := P_refl (Strip.Sj k i) k hS1 (by omega)
  have hPt : Strip.Pt (Strip.Sj k i) ≤ 8 * k := by omega
  have hPa : Strip.Pa (Strip.Sj k i) ≤ 8 * k := by omega
  simp only [Strip.R, Strip.ver, hS]
  constructor
  · apply Fin.ext
    rw [neg_val]
    simp only
    subst hn
    rcases Nat.lt_or_ge (Strip.Pt (Strip.Sj k i)) (8 * k) with h3 | h3
    · rw [Nat.mod_eq_of_lt (by omega : 8 * k + Strip.Pt (Strip.Sj k i) < 16 * k), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [show 8 * k + Strip.Pt (Strip.Sj k i) = 16 * k by omega, Nat.mod_self, Nat.sub_zero, Nat.mod_self,
        Nat.mod_eq_of_lt (by omega)]
      omega
  · apply Fin.ext
    rw [neg_val]
    simp only
    subst hn
    rw [Nat.mod_eq_of_lt (by omega : Strip.Pa (Strip.Sj k i) < 16 * k)]
    rcases Nat.eq_zero_or_pos (Strip.Pa (Strip.Sj k i)) with h3 | h3
    · rw [h3, Nat.sub_zero, Nat.mod_self, show 8 * k + Strip.Pt (16 * k - Strip.Sj k i) = 16 * k by omega,
        Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

end sym

/-! ## The stress is symmetric -/

lemma lamR_sym (k : ℕ) (z ag : ℝ) (i : ℕ) (hi : i ≤ 16 * k - 2) (hk : 1 ≤ k) :
    lamR k z ag (16 * k - 2 - i) = lamR k z ag i := by
  unfold lamR
  by_cases h : i ≤ 8 * k - 1
  · rw [if_pos h]
    by_cases h' : 16 * k - 2 - i ≤ 8 * k - 1
    · rw [if_pos h', show 16 * k - 2 - i = i by omega]
    · rw [if_neg h', show 16 * k - 2 - (16 * k - 2 - i) = i by omega]
  · rw [if_neg h, if_pos (by omega)]

lemma sigS_sym (k : ℕ) (z ag : ℝ) (s : ℕ) (hs : s ≤ 16 * k - 1) (hk : 1 ≤ k) :
    sigS k z ag (16 * k - 1 - s) = sigS k z ag s := by
  unfold sigS
  have hfs : firstSide k (16 * k - 1 - s) ↔ ¬ firstSide k s ∧ s ≠ 4 * k - 1 ∧ s ≠ 12 * k := by
    unfold firstSide; omega
  by_cases hc : s = 4 * k - 1 ∨ s = 12 * k
  · rw [if_pos hc, if_pos (by omega)]
  · rw [if_neg hc, if_neg (by omega)]
    by_cases hf : firstSide k s
    · rw [if_pos hf, if_neg (by rw [hfs]; tauto), show 16 * k - 1 - (16 * k - 1 - s) = s by omega]
    · rw [if_neg hf, if_pos (hfs.mpr ⟨hf, by omega, by omega⟩)]

/-! ## The force is symmetric -/

lemma neg_sub_one_val {n : ℕ} [NeZero n] (s : Fin n) (hn : 2 ≤ n) : (-s - 1).val = n - 1 - s.val := by
  have hs := s.isLt
  rw [show -s - 1 = -(s + 1) by abel, neg_val, fin_add_one_val]
  rcases Nat.lt_or_ge (s.val + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show s.val + 1 = n by omega, Nat.mod_self, Nat.sub_zero, Nat.mod_self]; omega

section forceSym
variable {k : ℕ} (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ} (ag : ℝ) (hc : cos (2 * z) ≠ 0)
  (hw : sin (z / 2) ≠ 0) (hcw : cos (z / 2) ≠ 0)
include hk hn hc hw hcw

lemma rung_ne (i : ℕ) (hi : i < 16 * k - 1) : (Strip.R n k i).1 ≠ (Strip.R n k i).2 := by
  intro h
  have hv := congrArg Fin.val h
  have := R_snd_range hk hn hc hw hcw i hi
  rcases Nat.lt_or_ge (i + 1) (8 * k) with h' | h'
  · have h1 := (R_first hk hn i h').1
    have h2 := Strip.Pa_lt k (8 * k + 1 + i) (by omega)
    obtain ⟨h3, -⟩ := Pa_Pt_hi k (8 * k + 1 + i) (by omega) (by omega)
    omega
  · have := R_second hk hn i h' hi; omega

/-- **`force(−x) = mir(force x)`.** -/
theorem force_neg (x : Fin n) : force k z ag (-x) = mir (force k z ag x) := by
  have hn2 : 2 ≤ n := by omega
  have hp : ∀ y : Fin n, Qc n z (-y) = mir (Qc n z y) := Qc_neg k hk hn z
  unfold force
  rw [mir_add', mir_sum', mir_sum']
  congr 1
  · -- sides: reindex `s ↦ −s − 1`
    let e : Fin n ≃ Fin n := ⟨fun s => -s - 1, fun s => -s - 1, fun s => by simp only; rw [neg_sub, sub_neg_eq_add, add_sub_cancel_left],
      fun s => by simp only; rw [neg_sub, sub_neg_eq_add, add_sub_cancel_left]⟩
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [e, Equiv.coe_fn_mk]
    have hv := neg_sub_one_val s hn2
    rw [hv, show n - 1 - s.val = 16 * k - 1 - s.val by omega, sigS_sym k z ag s.val (by omega) hk,
      mir_smul', show -s - 1 + 1 = -s by abel, show -s - 1 = -(s + 1) by abel, contrib_neg _ hp,
      contrib_swap _ _ _ _ (by intro h; have := congrArg (· - s) h; simp at this; omega)]
  · -- rungs: reindex `i ↦ n − 2 − i`
    rw [← Equiv.sum_comp (Fin.revPerm)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have hi := i.isLt
    have e1 : n - 1 - (i.val + 1) = 16 * k - 2 - i.val := by omega
    rw [e1, lamR_sym k z ag i.val (by omega) hk, mir_smul']
    congr 1
    rcases rung_refl hk hn i.val (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [show Strip.R n k (16 * k - 2 - i.val) = (-(Strip.R n k i.val).2, -(Strip.R n k i.val).1) from
          Prod.ext h1 h2, contrib_neg _ hp, contrib_swap _ _ _ _ (rung_ne hk hn hc hw hcw i.val (by omega)).symm]
    · rw [h2]
      -- the middle rung `{0, 8k}` is fixed by `σ` itself
      have hs : Strip.Sj k i.val = 0 := by unfold Strip.Sj; rw [h1, if_neg (by omega)]; omega
      have hR : Strip.R n k i.val = (-(Strip.R n k i.val).1, -(Strip.R n k i.val).2) := by
        apply Prod.ext <;> apply Fin.ext <;> simp only [Strip.R, Strip.ver, hs, neg_val] <;>
          simp only [show Strip.Pa 0 = 0 from rfl, show Strip.Pt 0 = 0 from rfl, Nat.zero_mod, Nat.sub_zero,
            Nat.mod_self, add_zero]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      conv_lhs => rw [hR]
      rw [contrib_neg _ hp]

end forceSym

end Chiquipoli.Family.Trig.P3
