/-
# Problem 3 ⇒ strict local maximality, for every `n = 16k`

`local_max_of_positive`: at a zero `z ∈ (0, π/4)` of `F_n`, `n = 16k`, suppose the
closed-form stress of `P3Stress` has positive rung multipliers and a negative
side sum. Then the published polygon is a strict local maximiser of the side
length among equilateral small `n`-gons, modulo Euclidean motions.

Theorem 3.5 is applied with:
* the rungs of the strip as the active diameters (`Strip.R`);
* the multipliers of the stress, whose equilibrium is `P3Balance.force_all`;
* the rigidity of the strip (`Strip.strip_rigid`).
-/
import ChiquipoliFamily.Trig.P3Balance

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Chiquipoli.Family.Trig.P3

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Chiquipoli.Family.Trig.RungVec

lemma ip_add_left'' (a b c : ℝ × ℝ) : ip (a + b) c = ip a c + ip b c := by
  simp only [ip, Prod.fst_add, Prod.snd_add]; ring

section main
variable {k : ℕ} (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ}
  (hz0 : 0 < z) (hz1 : z < π / 4) (hF : Optigon.F n z = 0)
include hk hn hz0 hz1 hF

lemma trig_facts : cos (2 * z) ≠ 0 ∧ sin (z / 2) ≠ 0 ∧ cos (z / 2) ≠ 0 ∧ 0 < 2 * sin (z / 2) ∧
    2 * sin (z / 2) < 2 := by
  have hpi := pi_pos
  have hc : 0 < cos (2 * z) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin (z / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcw : 0 < cos (z / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs1 : sin (z / 2) < 1 := by
    have := sin_le (show 0 ≤ z / 2 by linarith); linarith [pi_lt_four]
  exact ⟨hc.ne', hs.ne', hcw.ne', by linarith, by linarith⟩

/-- **Stationarity**, from equilibrium at every vertex. -/
theorem stationary (v : Cfg n) :
    (∑ i : Fin n, sigS k z (gapA hk hn (z := z)) i.val * ip (Qc n z (i + 1) - Qc n z i) (v (i + 1) - v i))
      + ∑ e : Fin (n - 1), lamR k z (gapA hk hn (z := z)) e.val *
          ip (Qc n z (Strip.R n k e.val).2 - Qc n z (Strip.R n k e.val).1)
            (v (Strip.R n k e.val).2 - v (Strip.R n k e.val).1) = 0 := by
  obtain ⟨hc, hw, hcw, -, -⟩ := trig_facts hk hn hz0 hz1 hF
  set ag := gapA hk hn (z := z)
  have hbal := force_all hk hn hc hw hcw
  have hs : ∀ s : Fin n, s ≠ s + 1 := by
    intro s h; have := congrArg (· - s) h; simp at this; omega
  -- `Σ_x ⟨force x, v x⟩ = −(the stationarity sum)`
  have key : ∑ x : Fin n, ip (force k z ag x) (v x) =
      -((∑ i : Fin n, sigS k z ag i.val * ip (Qc n z (i + 1) - Qc n z i) (v (i + 1) - v i))
        + ∑ e : Fin (n - 1), lamR k z ag e.val *
          ip (Qc n z (Strip.R n k e.val).2 - Qc n z (Strip.R n k e.val).1)
            (v (Strip.R n k e.val).2 - v (Strip.R n k e.val).1)) := by
    unfold force
    simp only [ip_add_left'', ip_sum_left, ip_smul_left', Finset.sum_add_distrib]
    have e1 : ∑ x : Fin n, ∑ s : Fin n, sigS k z ag s.val * ip (contrib (Qc n z) (s, s + 1) x) (v x)
        = -∑ i : Fin n, sigS k z ag i.val * ip (Qc n z (i + 1) - Qc n z i) (v (i + 1) - v i) := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.mul_sum, contrib_sum_ip _ _ _ _ (hs s)]; ring
    have e2 : ∑ x : Fin n, ∑ e : Fin (n - 1), lamR k z ag e.val * ip (contrib (Qc n z) (Strip.R n k e.val) x) (v x)
        = -∑ e : Fin (n - 1), lamR k z ag e.val *
          ip (Qc n z (Strip.R n k e.val).2 - Qc n z (Strip.R n k e.val).1)
            (v (Strip.R n k e.val).2 - v (Strip.R n k e.val).1) := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.mul_sum, show Strip.R n k e.val = ((Strip.R n k e.val).1, (Strip.R n k e.val).2) from rfl,
        contrib_sum_ip _ _ _ _ (rung_ne hk hn hc hw hcw e.val (by omega))]; ring
    rw [e1, e2]; ring
  have h0 : ∑ x : Fin n, ip (force k z ag x) (v x) = 0 := by
    have hb : ∀ x, force k z ag x = 0 := hbal
    simp only [hb]; simp [ip]
  linarith

/-- The published polygon at a root: all sides `ℓ`, all rungs `1`. -/
lemma sides_eq_root (s : Fin n) : nsq (Qc n z (s + 1) - Qc n z s) = (2 * sin (z / 2)) ^ 2 := by
  obtain ⟨hc, -, -, -, -⟩ := trig_facts hk hn hz0 hz1 hF
  by_cases h1 : s.val = 4 * k - 1
  · rw [closing_all z k hk hn s h1, hF, zero_add]
  by_cases h2 : s.val = 12 * k
  · rw [closing'_all z k hk hn s h2, hF, zero_add]
  exact sides_all z k hk hn hc s h1 h2

lemma rungs_eq_root (e : ℕ) (he : e < 16 * k - 1) :
    nsq (Qc n z (Strip.R n k e).2 - Qc n z (Strip.R n k e).1) = 1 := by
  obtain ⟨hc, -, -, -, -⟩ := trig_facts hk hn hz0 hz1 hF
  exact chords_all z k hk hn hc _ _ (Strip.strip_edge hn hk e he)

/-- **Problem 3 ⇒ strict local maximality.** If the rung multipliers are positive
and the side multipliers sum to a negative number, the published polygon is a
strict local maximiser of the side length, modulo Euclidean motions. -/
theorem local_max_of_positive
    (hlam : ∀ e : Fin (n - 1), 0 < lamR k z (gapA hk hn (z := z)) e.val)
    (hsum : ∑ i : Fin n, sigS k z (gapA hk hn (z := z)) i.val < 0) :
    ∀ᶠ y in nhds ((Qc n z, 2 * sin (z / 2)) : Amb n), IsFeasible y → 2 * sin (z / 2) ≤ y.2 →
      Feasible.Congruent y.1 (Qc n z) ∧ y.2 = 2 * sin (z / 2) := by
  obtain ⟨hc, hw, hcw, hl, hl2⟩ := trig_facts hk hn hz0 hz1 hF
  set ag := gapA hk hn (z := z)
  set l := 2 * sin (z / 2) with hldef
  let a : Fin (n - 1) → Fin n := fun e => (Strip.R n k e.val).1
  let b : Fin (n - 1) → Fin n := fun e => (Strip.R n k e.val).2
  have hmult := mult_of_stationary' hl.ne' a b (fun i => sigS k z ag i.val) (fun e => lamR k z ag e.val) _
    (stationary hk hn hz0 hz1 hF) rfl
  have hkap : 0 < -(l * ∑ i : Fin n, sigS k z ag i.val) := by
    have := mul_neg_of_pos_of_neg hl hsum; linarith
  have h01 : Qc n z 0 ≠ Qc n z 1 := by
    intro h
    have := sides_eq_root hk hn hz0 hz1 hF 0
    rw [zero_add, ← h, sub_self] at this
    have h0 : nsq (0 : ℝ × ℝ) = 0 := by simp [nsq, ip]
    rw [h0] at this
    nlinarith
  have hIR : ∀ w : Cfg n, (dataOf (Qc n z) l a b).Ieq w 0 → (dataOf (Qc n z) l a b).R w := by
    intro w hw'
    obtain ⟨hs, hd⟩ := bars_of_Ieq hl.ne' hw'
    obtain ⟨t, ω, htw⟩ := Strip.strip_rigid hn hk (Qc n z) w (L := l ^ 2) (by positivity) (by nlinarith)
      (fun i hi => ⟨rungs_eq_root hk hn hz0 hz1 hF i hi, hd ⟨i, by omega⟩⟩)
      (fun s _ _ => ⟨sides_eq_root hk hn hz0 hz1 hF s, hs s⟩)
    exact ⟨t, ω, fun i => by simpa [dataOf] using htw i⟩
  have hpeq : ∀ i : Fin n, eC i (Qc n z, l) = 0 := by
    intro i; unfold eC; simp only; rw [sides_eq_root hk hn hz0 hz1 hF i]; ring
  have hpact : ∀ e : Fin (n - 1), dC (a e) (b e) (Qc n z) = 0 := by
    intro e; unfold dC; rw [rungs_eq_root hk hn hz0 hz1 hF e.val (by omega)]; ring
  exact thm_3_5 hl h01 hkap hmult hlam hIR hpeq hpact

end main

end Chiquipoli.Family.Trig.P3
