/-
# Problem 3: equilibrium at every vertex, for every `n = 16k`

The first half is `Multipliers/Vertices.lean` (interior `a`-ends and `t`-ends) plus three special
vertices:
* the gap vertex `A = p_{4k}`, which carries the closing side;
* the gap vertex `C = p_{12k+1}`, which carries the other closing side;
* the vertex `h = 8k` on the axis.

These use the gap geometry `A − B = (a, sin φ)`, `C − D = (a, −sin φ)`
(`gap_AB`, `gap_CD`), with `a = ag` the horizontal width of the gap. The second
half follows by symmetry (`force_neg`), and the vertex `0` by global
equilibrium (`sum_force`).
-/
import ChiquipoliFamily.AllN.Multipliers.Symmetry

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Chiquipoli.Family.Trig.P3

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Chiquipoli.Family.Trig.RungVec

/-! ## Global equilibrium -/

lemma sum_contrib {n : ℕ} (p : Cfg n) (a b : Fin n) (hab : a ≠ b) : ∑ x, contrib p (a, b) x = 0 := by
  have h : ∀ x, contrib p (a, b) x = (if a = x then p b - p a else 0) + (if b = x then p a - p b else 0) :=
    fun x => contrib_split p a b x
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  abel

/-- The forces of any stress sum to zero. -/
lemma sum_force (k : ℕ) (z ag : ℝ) {n : ℕ} [NeZero n] (hn3 : 2 ≤ n)
    (hne : ∀ i : Fin (n - 1), (Strip.R n k i.val).1 ≠ (Strip.R n k i.val).2) :
    ∑ x : Fin n, force k z ag x = 0 := by
  unfold force
  rw [Finset.sum_add_distrib]
  have hs : ∀ s : Fin n, s ≠ s + 1 := by
    intro s h; have := congrArg (· - s) h; simp at this; omega
  have h1 : ∑ x : Fin n, ∑ s : Fin n, sigS k z ag s.val • contrib (Qc n z) (s, s + 1) x = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← Finset.smul_sum, sum_contrib _ _ _ (hs s), smul_zero]
  have h2 : ∑ x : Fin n, ∑ i : Fin (n - 1), lamR k z ag i.val • contrib (Qc n z) (Strip.R n k i.val) x = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.smul_sum, show Strip.R n k i.val = ((Strip.R n k i.val).1, (Strip.R n k i.val).2) from rfl,
      sum_contrib _ _ _ (hne i), smul_zero]
  rw [h1, h2, add_zero]

section special
variable {k : ℕ} (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ} (hc : cos (2 * z) ≠ 0)
  (hw : sin (z / 2) ≠ 0) (hcw : cos (z / 2) ≠ 0)
include hk hn hc hw hcw

/-- The gap vertices. -/
def vA : Fin n := ⟨4 * k, by omega⟩
def vB : Fin n := ⟨4 * k - 1, by omega⟩
def vC : Fin n := ⟨12 * k + 1, by omega⟩
def vD : Fin n := ⟨12 * k, by omega⟩

lemma R0 : Strip.R n k 0 = (vA hk hn, vC hk hn) := by
  have r := R_first hk hn 0 (by omega)
  have h1 := (Strip.PaPt k 1 (by norm_num))
  rw [show 8 * k + 1 + 0 = 8 * k + 1 by ring] at r
  have e : Strip.Pa (8 * k + 1) = 4 * k ∧ Strip.Pt (8 * k + 1) = 4 * k + 1 := by
    have := Strip.PaPt k 1 (by norm_num); simp only [Strip.da, Strip.dt] at this; omega
  apply Prod.ext <;> apply Fin.ext
  · rw [r.1, e.1]; rfl
  · rw [r.2, e.2, Nat.mod_eq_of_lt (by omega)]; simp only [vC]; omega

lemma B_neg : vB hk hn = -vC hk hn := by
  apply Fin.ext; rw [neg_val]; simp only [vB, vC]; rw [Nat.mod_eq_of_lt (by omega)]; omega

lemma D_neg : vD hk hn = -vA hk hn := by
  apply Fin.ext; rw [neg_val]; simp only [vA, vD]; rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `C − A = −e(φ)`: the first rung. -/
lemma gap_CA : Qc n z (vC hk hn) - Qc n z (vA hk hn) = -e (φ k z) := by
  have := rung_e k hk hn z hc 0 (by omega)
  rw [R0 hk hn hc hw hcw] at this
  simpa [θ] using this

/-- `A − B = (a, sin φ)` with `a = A_x − B_x`. -/
lemma gap_AB : (Qc n z (vA hk hn)).2 - (Qc n z (vB hk hn)).2 = sin (φ k z) := by
  have h := gap_CA hk hn hc hw hcw
  rw [B_neg hk hn hc hw hcw, Qc_neg k hk hn z]
  simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, e] at h
  simp only [mir]; linarith [h.2]

/-- `C − D = (a, −sin φ)`. -/
lemma gap_CD :
    Qc n z (vC hk hn) - Qc n z (vD hk hn) =
      ((Qc n z (vA hk hn)).1 - (Qc n z (vB hk hn)).1, -sin (φ k z)) := by
  have h := gap_CA hk hn hc hw hcw
  rw [D_neg hk hn hc hw hcw, B_neg hk hn hc hw hcw, Qc_neg k hk hn z, Qc_neg k hk hn z]
  simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, e] at h
  simp only [mir, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
  constructor <;> linarith [h.1, h.2]

end special

/-! ## The vertex `A`, the vertex `C`, the vertex `h` -/

/-- The equation of `A`, as an identity in `φ`, `w = z/2` and `a`. -/
lemma A_identity (φ' w a : ℝ) (hw : sin w ≠ 0) (hcw : cos w ≠ 0) :
    let tau0 := sin φ' * (cos φ' - a) / sin (2 * w)
    let lam0 := tau0 * sin w + (a * cos φ' + sin φ' ^ 2) / (2 * sin w)
    S tau0 φ' w + (-1 / (2 * sin w)) • ((-a, -sin φ') : ℝ × ℝ) + lam0 • (-e φ') = 0 := by
  intro tau0 lam0
  rw [S_eq _ _ _ hw]
  have h2 : sin (2 * w) = 2 * sin w * cos w := sin_two_mul w
  simp only [tau0, lam0, e, h2, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero, sin_add, cos_add]
  have hs := sin_sq_add_cos_sq φ'
  constructor
  · field_simp; linear_combination (-(a * cos w)) * hs
  · field_simp; linear_combination (-(sin φ' * cos w)) * hs

section special2
variable {k : ℕ} (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ} (hc : cos (2 * z) ≠ 0)
  (hw : sin (z / 2) ≠ 0) (hcw : cos (z / 2) ≠ 0)
include hk hn hc hw hcw

/-- The width of the gap: `a = A_x − B_x`. -/
noncomputable def gapA : ℝ := (Qc n z (vA hk hn)).1 - (Qc n z (vB hk hn)).1

/-- Rungs `1`, `2`, `3` of the strip. -/
lemma R123 : (Strip.R n k 1).1.val = 4 * k + 1 ∧ (Strip.R n k 1).2 = vC hk hn ∧
    (Strip.R n k 2).1.val = 4 * k + 2 ∧ (Strip.R n k 2).2 = vC hk hn ∧
    (Strip.R n k 3).1 = (Strip.R n k 2).1 ∧ (Strip.R n k 3).2.val = 12 * k + 2 := by
  have r1 := R_first hk hn 1 (by omega)
  have r2 := R_first hk hn 2 (by omega)
  have r3 := R_first hk hn 3 (by omega)
  have p2 := Strip.PaPt k 2 (by norm_num)
  have p3 := Strip.PaPt k 3 (by norm_num)
  have p4 := Strip.PaPt k 4 (by norm_num)
  simp only [Strip.da, Strip.dt] at p2 p3 p4
  rw [show 8 * k + 1 + 1 = 8 * k + 2 by ring, p2.1, p2.2] at r1
  rw [show 8 * k + 1 + 2 = 8 * k + 3 by ring, p3.1, p3.2] at r2
  rw [show 8 * k + 1 + 3 = 8 * k + 4 by ring, p4.1, p4.2] at r3
  refine ⟨by rw [r1.1], Fin.ext ?_, by rw [r2.1], Fin.ext ?_, Fin.ext ?_, ?_⟩
  · rw [r1.2, Nat.mod_eq_of_lt (by omega)]; simp only [vC]; omega
  · rw [r2.2, Nat.mod_eq_of_lt (by omega)]; simp only [vC]; omega
  · rw [r3.1, r2.1]
  · rw [r3.2, Nat.mod_eq_of_lt (by omega)]; omega

theorem force_vA : force k z (gapA hk hn (z := z)) (vA hk hn) = 0 := by
  set ag := gapA hk hn (z := z) with hag
  have hn3 : 3 ≤ n := by omega
  unfold force
  rw [side_part hn3 (Qc n z) (fun s => sigS k z ag s.val) (vA hk hn)]
  have hAm : vA hk hn - 1 = vB hk hn := by
    apply Fin.ext; rw [fin_sub_one_val _ (by simp only [vA]; omega) (by omega)]; simp only [vA, vB]
  have hs0 : sigS k z ag (vA hk hn).val = -tau k z ag 0 / ell z := by
    rw [show (vA hk hn).val = 4 * k from rfl]
    unfold sigS
    rw [if_neg (by omega), if_pos (show firstSide k (4 * k) from Or.inl ⟨le_rfl, by omega⟩),
      stepOf_A k (4 * k) le_rfl (by omega), (JA_vals (4 * k)).1 (by omega) |>.2]
    congr 3; omega
  have hsB : sigS k z ag (vB hk hn).val = -1 / ell z := by
    rw [show (vB hk hn).val = 4 * k - 1 from rfl]
    unfold sigS; rw [if_pos (Or.inl rfl)]
  rw [hAm, hs0, hsB]
  -- the side `A → A + 1`
  obtain ⟨h1a, h1b, -, -, -, -⟩ := R123 hk hn hc hw hcw
  have e1 : (Strip.R n k 1).1 = vA hk hn + 1 := by
    apply Fin.ext; rw [h1a, fin_add_one_val' _ (by simp only [vA]; omega)]; simp only [vA]
  have v0 := rung_e k hk hn z hc 0 (by omega)
  have v1 := rung_e k hk hn z hc 1 (by omega)
  rw [R0 hk hn hc hw hcw] at v0
  rw [e1, h1b] at v1
  simp only at v0
  have hvA : Qc n z (vA hk hn + 1) - Qc n z (vA hk hn) = e (θ k z (0 + 1)) - e (θ k z 0) := by
    rw [show Qc n z (vA hk hn + 1) - Qc n z (vA hk hn) = (Qc n z (vC hk hn) - Qc n z (vA hk hn))
      - (Qc n z (vC hk hn) - Qc n z (vA hk hn + 1)) by abel, v0, v1]
    simp only [zero_add]; abel
  rw [hvA, ← S_side]
  -- the rungs: only `ρ_0`
  rw [sum_fin_Icc (fun i => lamR k z ag i • contrib (Qc n z) (Strip.R n k i) (vA hk hn)) 0 0 (by omega)]
  swap
  · intro i hiN hout
    have hne1 : (Strip.R n k i).1 ≠ vA hk hn := by
      intro h
      have hv := congrArg Fin.val h
      simp only [vA] at hv
      rcases Nat.lt_or_ge (i + 1) (8 * k) with h' | h'
      · rw [(R_first hk hn i h').1] at hv
        have := (Pa_eq_iff (4 * k) _).mp hv
        rw [(JA_vals (4 * k)).1 (by omega) |>.1, (JA_vals (4 * k)).1 (by omega) |>.2] at this; omega
      · have := (R_second hk hn i h' (by omega)).1; omega
    have hne2 : (Strip.R n k i).2 ≠ vA hk hn := by
      intro h
      have := R_snd_range hk hn hc hw hcw i (by omega)
      rw [h] at this; simp only [vA] at this; omega
    simp only [contrib, hne1, hne2, if_false, smul_zero]
  rw [sum_Icc_1]
  simp only [R0 hk hn hc hw hcw, contrib, if_true]
  rw [v0]
  -- the identity
  have hB : Qc n z (vB hk hn) - Qc n z (vA hk hn) = ((-ag, -sin (φ k z)) : ℝ × ℝ) := by
    have := gap_AB hk hn hc hw hcw
    apply Prod.ext
    · simp only [Prod.fst_sub, hag, gapA]; ring
    · simp only [Prod.snd_sub]; linarith
  rw [hB]
  have hl0 : lamR k z ag 0 = tau k z ag 0 * sin (z / 2) + (ag * cos (φ k z) + sin (φ k z) ^ 2) / ell z := by
    unfold lamR lamF; rw [if_pos (by omega), if_pos rfl]
  have ht0 : tau k z ag 0 = sin (φ k z) * (cos (φ k z) - ag) / sin (2 * (z / 2)) := by
    rw [tau, show 2 * (z / 2) = z by ring]
  have hθ0 : θ k z 0 = φ k z := by simp [θ]
  rw [hl0, hθ0, ht0]
  have := A_identity (φ k z) (z / 2) ag hw hcw
  simp only at this
  unfold ell
  rw [← this]

theorem force_vC : force k z (gapA hk hn (z := z)) (vC hk hn) = 0 := by
  set ag := gapA hk hn (z := z) with hag
  have hn3 : 3 ≤ n := by omega
  obtain ⟨h1a, h1b, h2a, h2b, h3a, h3b⟩ := R123 hk hn hc hw hcw
  unfold force
  rw [side_part hn3 (Qc n z) (fun s => sigS k z ag s.val) (vC hk hn)]
  have hCm : vC hk hn - 1 = vD hk hn := by
    apply Fin.ext; rw [fin_sub_one_val _ (by simp only [vC]; omega) (by omega)]; simp only [vC, vD]; omega
  have hs2 : sigS k z ag (vC hk hn).val = -tau k z ag 2 / ell z := by
    rw [show (vC hk hn).val = 8 * k + (4 * k + 1) by simp only [vC]; ring]
    unfold sigS
    rw [if_neg (by omega), if_pos (show firstSide k (8 * k + (4 * k + 1)) from Or.inr ⟨by omega, by omega⟩),
      stepOf_T k (4 * k + 1) hk le_rfl (by omega), (JT_vals (4 * k + 1)).2.1 (by omega) |>.2]
    congr 3; omega
  have hsD : sigS k z ag (vD hk hn).val = -1 / ell z := by
    rw [show (vD hk hn).val = 12 * k from rfl]
    unfold sigS; rw [if_pos (Or.inr rfl)]
  rw [hCm, hs2, hsD]
  -- the side `C → C + 1`
  have v2 := rung_e k hk hn z hc 2 (by omega)
  have v3 := rung_e k hk hn z hc 3 (by omega)
  have e3 : (Strip.R n k 3).2 = vC hk hn + 1 := by
    apply Fin.ext; rw [h3b, fin_add_one_val' _ (by simp only [vC]; omega)]; simp only [vC]
  rw [h2b] at v2
  rw [e3, h3a] at v3
  have hvC : Qc n z (vC hk hn + 1) - Qc n z (vC hk hn) = -(e (θ k z (2 + 1)) - e (θ k z 2)) := by
    rw [show Qc n z (vC hk hn + 1) - Qc n z (vC hk hn) = (Qc n z (vC hk hn + 1) - Qc n z (Strip.R n k 2).1)
      - (Qc n z (vC hk hn) - Qc n z (Strip.R n k 2).1) by abel, v2, v3]
    abel
  rw [hvC, smul_neg, ← S_side]
  -- the rungs `ρ_0, ρ_1, ρ_2`
  rw [sum_fin_Icc (fun i => lamR k z ag i • contrib (Qc n z) (Strip.R n k i) (vC hk hn)) 0 2 (by omega)]
  swap
  · intro i hiN hout
    have hne2 : (Strip.R n k i).2 ≠ vC hk hn := by
      intro h
      have hv := congrArg Fin.val h
      simp only [vC] at hv
      rcases Nat.lt_or_ge (i + 1) (8 * k) with h' | h'
      · rw [(R_first hk hn i h').2] at hv
        have hPt : Strip.Pt (8 * k + 1 + i) ≤ 8 * k := by
          rcases Nat.lt_or_ge (8 * k + 1 + i) (16 * k - 1) with h'' | h''
          · exact (Strip.Pt_lt k _ h'').le
          · rw [show 8 * k + 1 + i = 16 * k - 1 by omega]; exact (Strip.P_last k hk).2.le
        rcases Nat.lt_or_ge (Strip.Pt (8 * k + 1 + i)) (8 * k) with h3 | h3
        · rw [Nat.mod_eq_of_lt (by omega)] at hv
          have := (Pt_eq_iff (4 * k + 1) (8 * k + 1 + i) (Or.inl (by omega))).mp (by omega)
          rw [(JT_vals (4 * k + 1)).2.1 (by omega) |>.1, (JT_vals (4 * k + 1)).2.1 (by omega) |>.2] at this
          omega
        · rw [show 8 * k + Strip.Pt (8 * k + 1 + i) = n by omega, Nat.mod_self] at hv; omega
      · have := (R_second hk hn i h' (by omega)).2.2; omega
    have hne1 : (Strip.R n k i).1 ≠ vC hk hn := by
      intro h
      have hv := congrArg Fin.val h
      simp only [vC] at hv
      rcases Nat.lt_or_ge (i + 1) (8 * k) with h' | h'
      · rw [(R_first hk hn i h').1] at hv
        have := Strip.Pa_lt k (8 * k + 1 + i) (by omega); omega
      · have := (R_second hk hn i h' (by omega)).1; omega
    simp only [contrib, hne1, hne2, if_false, smul_zero]
  rw [show (2 : ℕ) = 0 + 2 by rfl, sum_Icc_3]
  have hr : ∀ i, i ≤ 2 → (Strip.R n k i).2 = vC hk hn → (Strip.R n k i).1 ≠ vC hk hn →
      lamR k z ag i • contrib (Qc n z) (Strip.R n k i) (vC hk hn) = lamR k z ag i • e (θ k z i) := by
    intro i hi h2 h1
    simp only [contrib, h1, h2, if_false, if_true]
    have := rung_e k hk hn z hc i (by omega)
    rw [h2] at this
    rw [show Qc n z (Strip.R n k i).1 - Qc n z (vC hk hn) = -(Qc n z (vC hk hn) - Qc n z (Strip.R n k i).1) by abel,
      this, neg_neg]
  have n1 : ∀ i, i ≤ 2 → (Strip.R n k i).1 ≠ vC hk hn := by
    intro i hi h
    have hv := congrArg Fin.val h
    simp only [vC] at hv
    rw [(R_first hk hn i (by omega)).1] at hv
    have := Strip.Pa_lt k (8 * k + 1 + i) (by omega); omega
  simp only [zero_add]
  rw [hr 0 (by omega) (by rw [R0 hk hn hc hw hcw]) (n1 0 (by omega)), hr 1 (by omega) h1b (n1 1 (by omega)),
    hr 2 (by omega) h2b (n1 2 (by omega))]
  -- the identity
  have hG1 := rung_G k z ag hw hcw 1 le_rfl (by omega)
  have hG2 := rung_G k z ag hw hcw 2 (by omega) (by omega)
  rw [eps_val 1 le_rfl, if_neg (by omega), if_neg (by omega)] at hG1
  rw [eps_val 2 (by omega), if_pos (by omega)] at hG2
  have hA := A_identity (φ k z) (z / 2) ag hw hcw
  simp only at hA
  have hθ0 : θ k z 0 = φ k z := by simp [θ]
  have hl0 : lamR k z ag 0 = tau k z ag 0 * sin (z / 2) + (ag * cos (φ k z) + sin (φ k z) ^ 2) / ell z := by
    unfold lamR lamF; rw [if_pos (by omega), if_pos rfl]
  have ht0 : tau k z ag 0 = sin (φ k z) * (cos (φ k z) - ag) / sin (2 * (z / 2)) := by
    rw [tau, show 2 * (z / 2) = z by ring]
  rw [← ht0] at hA
  have hD : Qc n z (vD hk hn) - Qc n z (vC hk hn) = ((-ag, sin (φ k z)) : ℝ × ℝ) := by
    have := gap_CD hk hn hc hw hcw
    rw [show Qc n z (vD hk hn) - Qc n z (vC hk hn) = -(Qc n z (vC hk hn) - Qc n z (vD hk hn)) by abel, this]
    simp [hag, gapA]
  rw [hD, hl0, hθ0]
  simp only [show (2 - 1 : ℕ) = 1 by rfl, show (1 - 1 : ℕ) = 0 by rfl, hθ0] at hG1 hG2
  unfold ell
  unfold κ ell at hG2
  apply Prod.ext
  · have a1 := congrArg Prod.fst hA
    have g1 := congrArg Prod.fst hG1
    have g2 := congrArg Prod.fst hG2
    simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, Prod.fst_neg, smul_eq_mul, Prod.fst_zero] at a1 g1 g2 ⊢
    linear_combination -a1 - g1 - g2
  · have a1 := congrArg Prod.snd hA
    have g1 := congrArg Prod.snd hG1
    have g2 := congrArg Prod.snd hG2
    simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, Prod.snd_neg, smul_eq_mul, Prod.snd_zero] at a1 g1 g2 ⊢
    linear_combination -a1 - g1 - g2

def vH : Fin n := ⟨8 * k, by omega⟩

theorem force_vH (ag : ℝ) : force k z ag (vH hk hn) = 0 := by
  have hn3 : 3 ≤ n := by omega
  have hs : Strip.Sj k (8 * k - 1) = 0 := by unfold Strip.Sj; rw [if_neg (by omega)]; omega
  have hR1 : (Strip.R n k (8 * k - 1)).1.val = 0 := by
    simp only [Strip.R, Strip.ver, hs, show Strip.Pa 0 = 0 from rfl, Nat.zero_mod]
  have hR2 : (Strip.R n k (8 * k - 1)).2 = vH hk hn := by
    apply Fin.ext
    simp only [Strip.R, Strip.ver, hs, show Strip.Pt 0 = 0 from rfl, add_zero, vH]
    exact Nat.mod_eq_of_lt (by omega)
  unfold force
  rw [side_part hn3 (Qc n z) (fun s => sigS k z ag s.val) (vH hk hn)]
  have hHm : (vH hk hn - 1).val = 8 * k - 1 := by
    rw [fin_sub_one_val _ (by simp only [vH]; omega) (by omega)]; simp only [vH]
  have hHp : (vH hk hn + 1).val = 8 * k + 1 := by
    rw [fin_add_one_val' _ (by simp only [vH]; omega)]; simp only [vH]
  have hsm : sigS k z ag (vH hk hn - 1).val = -tau k z ag (8 * k - 2) / ell z := by
    rw [hHm]; unfold sigS
    rw [if_neg (by omega), if_pos (show firstSide k (8 * k - 1) from Or.inl ⟨by omega, le_rfl⟩)]
    unfold stepOf; rw [if_neg (by omega), if_pos rfl]
  have hsp : sigS k z ag (vH hk hn).val = -tau k z ag (8 * k - 2) / ell z := by
    rw [show (vH hk hn).val = 8 * k from rfl]; unfold sigS
    rw [if_neg (by omega), if_neg (show ¬ firstSide k (8 * k) by unfold firstSide; omega),
      show 16 * k - 1 - 8 * k = 8 * k - 1 by omega]
    unfold stepOf; rw [if_neg (by omega), if_pos rfl]
  rw [hsp, hsm]
  rw [sum_fin_Icc (fun i => lamR k z ag i • contrib (Qc n z) (Strip.R n k i) (vH hk hn)) (8 * k - 1) (8 * k - 1)
    (by omega)]
  swap
  · intro i hiN hout
    have hne1 : (Strip.R n k i).1 ≠ vH hk hn := by
      intro h
      have hv := congrArg Fin.val h
      simp only [vH] at hv
      rcases Nat.lt_or_ge (i + 1) (8 * k) with h' | h'
      · rw [(R_first hk hn i h').1] at hv
        have := Strip.Pa_lt k (8 * k + 1 + i) (by omega); omega
      · have := (R_second hk hn i h' (by omega)).1; omega
    have hne2 : (Strip.R n k i).2 ≠ vH hk hn := by
      intro h
      have hv := congrArg Fin.val h
      simp only [vH] at hv
      rcases Nat.lt_or_ge (i + 1) (8 * k) with h' | h'
      · rw [(R_first hk hn i h').2] at hv
        obtain ⟨-, h4⟩ := Pa_Pt_hi k (8 * k + 1 + i) (by omega) (by omega)
        have hPt : Strip.Pt (8 * k + 1 + i) ≤ 8 * k := by
          rcases Nat.lt_or_ge (8 * k + 1 + i) (16 * k - 1) with h'' | h''
          · exact (Strip.Pt_lt k _ h'').le
          · rw [show 8 * k + 1 + i = 16 * k - 1 by omega]; exact (Strip.P_last k hk).2.le
        rcases Nat.lt_or_ge (Strip.Pt (8 * k + 1 + i)) (8 * k) with h3 | h3
        · rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
        · rw [show 8 * k + Strip.Pt (8 * k + 1 + i) = n by omega, Nat.mod_self] at hv; omega
      · have hs' : Strip.Sj k i = i + 1 - 8 * k := by unfold Strip.Sj; rw [if_neg (by omega)]
        obtain ⟨-, h5, h6⟩ := Pa_Pt_lo k (i + 1 - 8 * k) hk (by omega)
        simp only [Strip.R, Strip.ver, hs'] at hv
        rw [Nat.mod_eq_of_lt (by omega)] at hv
        have := h6 (by omega); omega
    simp only [contrib, hne1, hne2, if_false, smul_zero]
  rw [sum_Icc_1]
  have hne : (Strip.R n k (8 * k - 1)).1 ≠ vH hk hn := by
    intro h; have := congrArg Fin.val h; rw [hR1] at this; simp only [vH] at this; omega
  simp only [contrib, hne, hR2, if_false, if_true]
  -- the positions
  have q0 : Qc n z (Strip.R n k (8 * k - 1)).1 = ((0 : ℝ), (0 : ℝ)) := by
    rw [ConstructorAll.Qc_eq z k hk hn, hR1, P_low z k 0 (by omega), lowRole_zero, mir_origin]
    simp [ev, tOrigin, Tm.eval]
  have qH : Qc n z (vH hk hn) = ((0 : ℝ), (1 : ℝ)) := by
    rw [ConstructorAll.Qc_eq z k hk hn, show (vH hk hn).val = 8 * k from rfl, P_top]
    simp [ev, tTop, Tm.eval]
  have qm : Qc n z (vH hk hn - 1) = (sin z, cos z) := by
    rw [ConstructorAll.Qc_eq z k hk hn, hHm, P_mid z k _ (by omega) (by omega),
      show 8 * k - 1 - (8 * k - 1) = 0 by omega, midRole_zero]
    simp [ev, tq0, Tm.eval]
  have qp : Qc n z (vH hk hn + 1) = (-sin z, cos z) := by
    rw [ConstructorAll.Qc_eq z k hk hn, hHp, P_hi_mid z k _ (by omega) (by omega),
      show 8 * k - 1 - (16 * k - (8 * k + 1)) = 0 by omega, midRole_zero]
    simp [ev, tq0, Tm.eval, mir]
  rw [q0, qH, qm, qp]
  have hl : lamR k z ag (8 * k - 1) = tau k z ag (8 * k - 2) * ell z := by
    unfold lamR lamF; rw [if_pos le_rfl, if_neg (by omega), if_pos rfl]
  rw [hl]
  have hℓ : ell z ≠ 0 := by unfold ell; exact mul_ne_zero two_ne_zero hw
  have hsq := sq_two_sin_half' z
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul, Prod.fst_zero]; ring
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul, Prod.snd_zero]
    unfold ell at hℓ ⊢
    field_simp
    linear_combination (-(tau k z ag (8 * k - 2))) * hsq

/-- **Equilibrium at every vertex**, for every `n = 16k` and every `z` with
`cos 2z ≠ 0`, `sin(z/2), cos(z/2) ≠ 0`. -/
theorem force_all (x : Fin n) : force k z (gapA hk hn (z := z)) x = 0 := by
  set ag := gapA hk hn (z := z)
  have hxn := x.isLt
  -- the first half
  have first : ∀ y : Fin n, (4 * k ≤ y.val ∧ y.val ≤ 8 * k) ∨ 12 * k + 1 ≤ y.val → force k z ag y = 0 := by
    intro y hy
    rcases hy with ⟨h1, h2⟩ | h1
    · rcases Nat.eq_or_lt_of_le h1 with h3 | h3
      · have : y = vA hk hn := Fin.ext (by simp only [vA]; omega)
        rw [this]; exact force_vA hk hn hc hw hcw
      rcases Nat.eq_or_lt_of_le h2 with h4 | h4
      · have : y = vH hk hn := Fin.ext (by simp only [vH]; omega)
        rw [this]; exact force_vH hk hn hc hw hcw ag
      · exact force_A_interior hk hn ag hc hw hcw y (by omega) (by omega)
    · rcases Nat.eq_or_lt_of_le h1 with h3 | h3
      · have : y = vC hk hn := Fin.ext (by simp only [vC]; omega)
        rw [this]; exact force_vC hk hn hc hw hcw
      · exact force_T_interior hk hn ag hc hw hcw y (by omega)
  -- the second half, by symmetry
  have second : ∀ y : Fin n, y.val ≠ 0 → force k z ag y = 0 := by
    intro y hy0
    by_cases hf : (4 * k ≤ y.val ∧ y.val ≤ 8 * k) ∨ 12 * k + 1 ≤ y.val
    · exact first y hf
    · have hy' : -(-y) = y := neg_neg y
      rw [← hy', force_neg hk hn ag hc hw hcw, first (-y) ?_, mir_zero']
      rw [neg_val, Nat.mod_eq_of_lt (by omega)]
      omega
  rcases Nat.eq_zero_or_pos x.val with h0 | h0
  · -- the vertex `0`: global equilibrium
    have hsum := sum_force k z ag (n := n) (by omega) (fun i => rung_ne hk hn hc hw hcw i.val (by omega))
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)] at hsum
    rw [Finset.sum_eq_zero (fun y hy => second y (by
      intro h; apply (Finset.mem_erase.mp hy).1; exact Fin.ext (by omega)))] at hsum
    simpa using hsum
  · exact second x (by omega)

end special2

end Chiquipoli.Family.Trig.P3
