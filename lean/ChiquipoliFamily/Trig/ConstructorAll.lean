/-
# The published polygon, for every `n = 16k`: sides and chords

With the layout of `Layout.lean` (`vertexS_eq`), the exact identities of
`Shapes.lean` and `FSide.lean` apply at every index, for a symbolic `k`:

* `chords_all`: every pair of `G_n` (`gnAct`) is at distance exactly `1`;
* `sides_all`: every side other than the two closing sides has length
  `2 sin (z/2)`;
* `closing_all`, `closing'_all`: the two closing sides `{4k−1, 4k}` and
  `{12k, 12k+1}` have squared length `F_n(z) + (2 sin(z/2))²`.

These hold for every `z` with `cos 2z ≠ 0`; at a zero of `F_n` all sides are
equal. `published_rigid_all` combines them with `Strip.gn_rigid`: at every zero
of `F_n` in `(0, π/4)`, the published polygon, with its sides and the pairs of
`G_n` as bars, is infinitesimally rigid.
-/
import ChiquipoliFamily.Trig.Layout
import ChiquipoliFamily.Trig.Strip
import ChiquipoliFamily.Trig.RootAll

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig.ConstructorAll

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Tm

/-! ## The roles, block by block -/

lemma lowRole0 (s : ℕ) : lowRole (4 * s) = T (2 * s) := by
  have h1 : (4 * s) % 4 = 0 := by omega
  have h2 : (4 * s) / 4 = s := by omega
  simp [lowRole, h1, h2]
lemma lowRole1 (s : ℕ) : lowRole (4 * s + 1) = Rr (2 * s) := by
  have h1 : (4 * s + 1) % 4 = 1 := by omega
  have h2 : (4 * s + 1) / 4 = s := by omega
  simp [lowRole, h1, h2]
lemma lowRole2 (s : ℕ) : lowRole (4 * s + 2) = U (2 * s) := by
  have h1 : (4 * s + 2) % 4 = 2 := by omega
  have h2 : (4 * s + 2) / 4 = s := by omega
  simp [lowRole, h1, h2]
lemma lowRole3 (s : ℕ) : lowRole (4 * s + 3) = Q (2 * s + 1) := by
  have h1 : (4 * s + 3) % 4 = 3 := by omega
  have h2 : (4 * s + 3) / 4 = s := by omega
  simp [lowRole, h1, h2]

lemma midRole0 (s : ℕ) : midRole (4 * s) = Q (2 * s) := by
  have h1 : (4 * s) % 4 = 0 := by omega
  have h2 : (4 * s) / 4 = s := by omega
  simp [midRole, h1, h2]
lemma midRole1 (s : ℕ) : midRole (4 * s + 1) = T (2 * s + 1) := by
  have h1 : (4 * s + 1) % 4 = 1 := by omega
  have h2 : (4 * s + 1) / 4 = s := by omega
  simp [midRole, h1, h2]
lemma midRole2 (s : ℕ) : midRole (4 * s + 2) = Rr (2 * s + 1) := by
  have h1 : (4 * s + 2) % 4 = 2 := by omega
  have h2 : (4 * s + 2) / 4 = s := by omega
  simp [midRole, h1, h2]
lemma midRole3 (s : ℕ) : midRole (4 * s + 3) = U (2 * s + 1) := by
  have h1 : (4 * s + 3) % 4 = 3 := by omega
  have h2 : (4 * s + 3) / 4 = s := by omega
  simp [midRole, h1, h2]

lemma Q0 : Q 0 = tq0 := rfl
lemma Rr0 : Rr 0 = tr0 := rfl
lemma U0 : U 0 = tu0 := rfl
lemma T0 : T 0 = tOrigin := rfl
lemma lowRole_zero : lowRole 0 = tOrigin := rfl
lemma lowRole_one : lowRole 1 = tr0 := rfl
lemma midRole_zero : midRole 0 = tq0 := rfl

/-- Split `y` as `4s + c`. -/
lemma split4 (y : ℕ) : ∃ s c, c < 4 ∧ y = 4 * s + c := ⟨y / 4, y % 4, Nat.mod_lt _ (by norm_num), by omega⟩

/-! ## Sides and chords between roles -/

variable (z : ℝ)

/-- Consecutive indices in `[0, 4k)`. -/
theorem lowSide (hc : cos (2 * z) ≠ 0) (y : ℕ) :
    nsq (ev z (lowRole (y + 1)) - ev z (lowRole y)) = (2 * sin (z / 2)) ^ 2 := by
  obtain ⟨s, c, hc4, rfl⟩ := split4 y
  interval_cases c
  · rw [show 4 * s + 0 + 1 = 4 * s + 1 by ring, lowRole1, show 4 * s + 0 = 4 * s by ring, lowRole0, nsq_comm]
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact side0_rt z
    · rw [Rr_pos (by omega), T_pos (by omega)]; exact side_rt z _
  · rw [show 4 * s + 1 + 1 = 4 * s + 2 by ring, lowRole2, lowRole1, nsq_comm]
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact side0_ur z
    · rw [U_pos (by omega), Rr_pos (by omega)]; exact side_ur z _
  · rw [show 4 * s + 2 + 1 = 4 * s + 3 by ring, lowRole3, lowRole2, Q_pos (by omega)]
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact side0_uq z hc
    · rw [U_pos (by omega)]; exact side_uq z _ hc
  · rw [show 4 * s + 3 + 1 = 4 * (s + 1) by ring, lowRole0, lowRole3, T_pos (by omega), Q_pos (by omega),
      show 2 * (s + 1) = 2 * s + 1 + 1 by ring]
    exact side_qt z _ hc

/-- Consecutive indices in `[4k, 8k)`, counted from `8k − 1` down. -/
theorem midSide (hc : cos (2 * z) ≠ 0) (d : ℕ) :
    nsq (ev z (midRole d) - ev z (midRole (d + 1))) = (2 * sin (z / 2)) ^ 2 := by
  obtain ⟨s, c, hc4, rfl⟩ := split4 d
  interval_cases c
  · rw [show 4 * s + 0 + 1 = 4 * s + 1 by ring, midRole1, show 4 * s + 0 = 4 * s by ring, midRole0,
      T_pos (by omega), nsq_comm]
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact side0_qt z hc
    · rw [Q_pos (by omega)]; exact side_qt z _ hc
  · rw [show 4 * s + 1 + 1 = 4 * s + 2 by ring, midRole2, midRole1, T_pos (by omega), Rr_pos (by omega)]
    exact side_rt z _
  · rw [show 4 * s + 2 + 1 = 4 * s + 3 by ring, midRole3, midRole2, Rr_pos (by omega), U_pos (by omega)]
    exact side_ur z _
  · rw [show 4 * s + 3 + 1 = 4 * (s + 1) by ring, midRole0, midRole3, U_pos (by omega), Q_pos (by omega),
      nsq_comm, show 2 * (s + 1) = 2 * s + 1 + 1 by ring]
    exact side_uq z _ hc

/-- **The chords.** `lowRole y` and `midRole d` are at distance `1` when
`y − d − 1 ∈ Δ`, the same pattern for both halves of `G_n`. -/
theorem chordLM (hc : cos (2 * z) ≠ 0) (d y : ℕ)
    (h : (y = d + 2 ∧ (d % 4 = 0 ∨ d % 4 = 1)) ∨ y = d + 1 ∨ (y = d ∧ (d % 4 = 0 ∨ d % 4 = 3))) :
    nsq (ev z (lowRole y) - ev z (midRole d)) = 1 := by
  obtain ⟨s, c, hc4, rfl⟩ := split4 d
  interval_cases c
  · rw [show 4 * s + 0 = 4 * s by ring, midRole0] at *
    rcases h with ⟨rfl, -⟩ | rfl | ⟨rfl, -⟩
    · rw [lowRole2]
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · exact fan0_qu z
      · rw [U_pos (by omega), Q_pos (by omega)]; exact fan_qu z _
    · rw [lowRole1]
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · exact fan0_qr z
      · rw [Rr_pos (by omega), Q_pos (by omega)]; exact fan_qr z _
    · rw [lowRole0]
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · exact fan0_qt z
      · rw [T_pos (by omega), Q_pos (by omega)]; exact fan_qt z _
  · rw [midRole1, T_pos (by omega)]
    rcases h with ⟨rfl, -⟩ | rfl | ⟨rfl, h⟩
    · rw [show 4 * s + 1 + 2 = 4 * s + 3 by ring, lowRole3, Q_pos (by omega), nsq_comm]; exact fan_qt z _
    · rw [show 4 * s + 1 + 1 = 4 * s + 2 by ring, lowRole2, nsq_comm]
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · exact cross0_ut z hc
      · rw [U_pos (by omega)]; exact cross_ut z _ hc
    · omega
  · rw [midRole2, Rr_pos (by omega)]
    rcases h with ⟨rfl, h⟩ | rfl | ⟨rfl, h⟩
    · omega
    · rw [show 4 * s + 2 + 1 = 4 * s + 3 by ring, lowRole3, Q_pos (by omega), nsq_comm]; exact fan_qr z _
    · omega
  · rw [midRole3, U_pos (by omega)]
    rcases h with ⟨rfl, h⟩ | rfl | ⟨rfl, -⟩
    · omega
    · rw [show 4 * s + 3 + 1 = 4 * (s + 1) by ring, lowRole0, T_pos (by omega),
        show 2 * (s + 1) = 2 * s + 1 + 1 by ring]
      exact cross_ut z _ hc
    · rw [lowRole3, Q_pos (by omega), nsq_comm]; exact fan_qu z _

/-! ## The published points -/

/-- Mirror image in the second coordinate axis, on real points. -/
def mir (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, p.2)

lemma ev_tM (p : Tm × Tm) : ev z (tM p) = mir (ev z p) := by simp [ev, tM, mir, Tm.eval]

lemma nsq_mir (p q : ℝ × ℝ) : nsq (mir p - mir q) = nsq (p - q) := by
  simp only [nsq_eq, mir]; ring

lemma mir_origin : mir (ev z tOrigin) = ev z tOrigin := by simp [mir, ev, tOrigin, Tm.eval]
lemma mir_top : mir (ev z tTop) = ev z tTop := by simp [mir, ev, tTop, Tm.eval]

/-- The published vertex `x`, `n = 16k`. -/
theorem Qc_eq (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) (x : Fin n) :
    Qc n z x = ev z (spec k x.val) := by
  subst hn
  unfold Qc
  rw [vertex_eval]
  by_cases h0 : x.val = 0
  · rw [h0, spec_low k 0 (by omega), lowRole_zero, ev_tM, mir_origin]
    simp [vertexS, ev, tOrigin, Tm.eval]
  · rw [vertexS_eq k hk x.val h0 (by omega)]; rfl

lemma P_low (k x : ℕ) (h : x < 4 * k) : ev z (spec k x) = mir (ev z (lowRole x)) := by
  rw [spec_low k x h, ev_tM]
lemma P_mid (k x : ℕ) (h1 : 4 * k ≤ x) (h2 : x < 8 * k) : ev z (spec k x) = ev z (midRole (8 * k - 1 - x)) := by
  rw [spec_mid k x h1 h2]
lemma P_top (k : ℕ) : ev z (spec k (8 * k)) = ev z tTop := by
  unfold spec; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
lemma P_hi_low (k x : ℕ) (h1 : 8 * k < x) (h2 : 16 * k - x < 4 * k) :
    ev z (spec k x) = ev z (lowRole (16 * k - x)) := by
  rw [spec_up_low k x h1 h2]
lemma P_hi_mid (k x : ℕ) (h1 : 8 * k < x) (h2 : 4 * k ≤ 16 * k - x) :
    ev z (spec k x) = mir (ev z (midRole (8 * k - 1 - (16 * k - x)))) := by
  rw [spec_up_mid k x h1 h2, ev_tM]

/-! ## Every side, every chord -/

/-- **Every non-closing side has length `2 sin(z/2)`**, for every `n = 16k`. -/
theorem sides_all (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) (hc : cos (2 * z) ≠ 0)
    (x : Fin n) (h1 : x.val ≠ 4 * k - 1) (h2 : x.val ≠ 12 * k) :
    nsq (Qc n z (x + 1) - Qc n z x) = (2 * sin (z / 2)) ^ 2 := by
  rw [Qc_eq z k hk hn, Qc_eq z k hk hn, fin_add_one_val]
  subst hn
  have hx := x.isLt
  set v := x.val
  rcases Nat.lt_or_ge (v + 1) (16 * k) with hv | hv
  · rw [Nat.mod_eq_of_lt hv]
    rcases Nat.lt_or_ge v (4 * k - 1) with r1 | r1
    · rw [P_low z k _ (by omega), P_low z k _ (by omega), nsq_mir]; exact lowSide z hc v
    rcases Nat.lt_or_ge v (8 * k - 1) with r2 | r2
    · rw [P_mid z k _ (by omega) (by omega), P_mid z k _ (by omega) (by omega),
        show 8 * k - 1 - v = 8 * k - 1 - (v + 1) + 1 by omega]
      exact midSide z hc _
    rcases Nat.eq_or_lt_of_le r2 with r3 | r3
    · rw [← r3, show 8 * k - 1 + 1 = 8 * k by omega, P_top, P_mid z k _ (by omega) (by omega),
        show 8 * k - 1 - (8 * k - 1) = 0 by omega, midRole_zero]
      exact side0_top z
    rcases Nat.eq_or_lt_of_le (show 8 * k ≤ v by omega) with r4 | r4
    · rw [← r4, P_top, P_hi_mid z k _ (by omega) (by omega),
        show 8 * k - 1 - (16 * k - (8 * k + 1)) = 0 by omega, midRole_zero, ← mir_top, nsq_mir, nsq_comm]
      exact side0_top z
    rcases Nat.lt_or_ge v (12 * k) with r5 | r5
    · rw [P_hi_mid z k _ (by omega) (by omega), P_hi_mid z k _ (by omega) (by omega), nsq_mir, nsq_comm,
        show 8 * k - 1 - (16 * k - (v + 1)) = 8 * k - 1 - (16 * k - v) + 1 by omega]
      exact midSide z hc _
    · rw [P_hi_low z k _ (by omega) (by omega), P_hi_low z k _ (by omega) (by omega), nsq_comm,
        show 16 * k - v = 16 * k - (v + 1) + 1 by omega]
      exact lowSide z hc _
  · -- the side `16k − 1 → 0`
    have hv' : v = 16 * k - 1 := by omega
    rw [show v + 1 = 16 * k by omega, Nat.mod_self, P_low z k 0 (by omega), lowRole_zero, mir_origin, hv', P_hi_low z k _ (by omega) (by omega),
      show 16 * k - (16 * k - 1) = 1 by omega, lowRole_one]
    exact side0_rt z

/-- **The closing side `{4k − 1, 4k}`.** -/
theorem closing_all (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) (x : Fin n) (hx : x.val = 4 * k - 1) :
    nsq (Qc n z (x + 1) - Qc n z x) = Optigon.F n z + (2 * sin (z / 2)) ^ 2 := by
  rw [Qc_eq z k hk hn, Qc_eq z k hk hn, fin_add_one_val, hx, Nat.mod_eq_of_lt (by omega),
    P_mid z k _ (by omega) (by omega), P_low z k _ (by omega),
    show 8 * k - 1 - (4 * k - 1 + 1) = 4 * (k - 1) + 3 by omega, midRole3,
    show 4 * k - 1 = 4 * (k - 1) + 3 by omega, lowRole3, show 2 * (k - 1) + 1 = 2 * k - 1 by omega,
    U_pos (by omega), Q_pos (by omega), ← ev_tM, hn, show 16 * k = 8 * (2 * k) by ring]
  exact closing z k hk

/-- **The closing side `{12k, 12k + 1}`.** -/
theorem closing'_all (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) (x : Fin n) (hx : x.val = 12 * k) :
    nsq (Qc n z (x + 1) - Qc n z x) = Optigon.F n z + (2 * sin (z / 2)) ^ 2 := by
  rw [Qc_eq z k hk hn, Qc_eq z k hk hn, fin_add_one_val, hx, Nat.mod_eq_of_lt (by omega),
    P_hi_low z k _ (by omega) (by omega), P_hi_mid z k _ (by omega) (by omega),
    show 16 * k - (12 * k + 1) = 4 * (k - 1) + 3 by omega, lowRole3,
    show 8 * k - 1 - (16 * k - 12 * k) = 4 * (k - 1) + 3 by omega, midRole3,
    show 2 * (k - 1) + 1 = 2 * k - 1 by omega, U_pos (by omega), Q_pos (by omega), ← ev_tM, hn,
    show 16 * k = 8 * (2 * k) by ring]
  exact closing' z k hk

/-- One orientation of a pair of `G_n`: `a < h` and `b − a ≡ h + δ`. -/
theorem chord_dir (k : ℕ) (hk : 1 ≤ k) (hc : cos (2 * z) ≠ 0) (a b : ℕ) (ha : a < 8 * k) (hb : b < 16 * k)
    (hD : ((b + 16 * k - a) % (16 * k) = 8 * k ∧ a ≠ 4 * k) ∨
      ((b + 16 * k - a) % (16 * k) = 8 * k - 1 ∧ (a % 4 = 2 ∨ a % 4 = 3)) ∨
      ((b + 16 * k - a) % (16 * k) = 8 * k + 1 ∧ (a % 4 = 0 ∨ a % 4 = 3))) :
    nsq (ev z (spec k b) - ev z (spec k a)) = 1 := by
  -- `b = a + h + δ`, or the wrap `a = h − 1`, `b = 0`
  have hdec : (b = a + 8 * k ∧ a ≠ 4 * k) ∨ (b + 1 = a + 8 * k ∧ (a % 4 = 2 ∨ a % 4 = 3)) ∨
      (b = a + 8 * k + 1 ∧ (a % 4 = 0 ∨ a % 4 = 3)) ∨ (a = 8 * k - 1 ∧ b = 0) := by
    rcases Nat.lt_or_ge b a with hba | hba
    · rw [Nat.mod_eq_of_lt (by omega)] at hD; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hD; omega
  rcases Nat.lt_or_ge a (4 * k) with hlo | hhi
  · -- `a` in the lower quarter: both points mirrored
    rcases eq_or_ne b (8 * k) with hb8 | hb8
    · have ha0 : a = 0 := by omega
      rw [hb8, P_top, ha0, P_low z k 0 (by omega), lowRole_zero, mir_origin]
      exact origin_top z
    · rw [P_low z k a hlo, P_hi_mid z k b (by omega) (by omega), nsq_mir, nsq_comm]
      apply chordLM z hc
      omega
  · -- `a` in the upper quarter of the first half
    rcases eq_or_ne b 0 with hb0 | hb0
    · rw [hb0, P_low z k 0 (by omega), lowRole_zero, mir_origin,
        P_mid z k a (by omega) (by omega), show 8 * k - 1 - a = 0 by omega, midRole_zero]
      exact fan0_qt z
    · rw [P_hi_low z k b (by omega) (by omega), P_mid z k a hhi ha]
      apply chordLM z hc
      omega

/-- **Every pair of `G_n` is at distance `1`**, for every `n = 16k`. -/
theorem chords_all (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) (hc : cos (2 * z) ≠ 0)
    (a b : Fin n) (hab : gnAct n a.val b.val = true) : nsq (Qc n z b - Qc n z a) = 1 := by
  rw [Qc_eq z k hk hn, Qc_eq z k hk hn]
  subst hn
  have ha := a.isLt
  have hb := b.isLt
  unfold gnAct at hab
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab
  have e : 16 * k / 2 = 8 * k := by omega
  rw [e] at hab
  rcases hab with ⟨ha', hD⟩ | ⟨hb', hD⟩
  · exact chord_dir z k hk hc a.val b.val ha' hb (by omega)
  · rw [nsq_comm]; exact chord_dir z k hk hc b.val a.val hb' ha (by omega)

/-! ## Rigidity of the published polygon, for every `n = 16k` -/

/-- **Infinitesimal rigidity for every `n = 16k`.** At every zero `z` of `F_n` with
`0 < z < π/4`, a displacement that keeps every side and every pair of `G_n` of
the published polygon stationary is an infinitesimal rigid motion. -/
theorem published_rigid_all (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < π / 4) (w : Cfg n)
    (hside : ∀ s : Fin n, ip (Qc n z (s + 1) - Qc n z s) (w (s + 1) - w s) = 0)
    (hact : ∀ a b : Fin n, gnAct n a.val b.val = true → ip (Qc n z b - Qc n z a) (w b - w a) = 0) :
    ∃ (t : ℝ × ℝ) (ω : ℝ), ∀ x, w x = t + ω • J (Qc n z x) := by
  have hc : cos (2 * z) ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
  have hs : 0 < sin (z / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hs2 : sin (z / 2) < 1 := by
    have := sin_le (show 0 ≤ z / 2 by linarith); linarith [pi_lt_four]
  apply Strip.gn_rigid hn hk (Qc n z) w (L := (2 * sin (z / 2)) ^ 2) (by positivity) (by nlinarith)
  · exact fun a b h => ⟨chords_all z k hk hn hc a b h, hact a b h⟩
  · exact fun s h1 h2 => ⟨sides_all z k hk hn hc s h1 h2, hside s⟩


/-- **The published polygon at its root, for every `n = 16k`.** `F_n` has exactly
one zero `z` in `(0, π/n)`, and it is simple. At `z`, the polygon upstream builds
is equilateral with side `2 sin(z/2)`, every pair of `G_n` is at distance `1`,
and the framework of its sides and the pairs of `G_n` is infinitesimally rigid. -/
theorem published_all (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) :
    ∃ z : ℝ, z ∈ Set.Ioo (π / ((n : ℝ) + 2)) (π / n) ∧ Optigon.F n z = 0 ∧ Fd n z < 0 ∧
      (∀ z' ∈ Set.Ioo 0 (π / n), Optigon.F n z' = 0 → z' = z) ∧
      (∀ s : Fin n, nsq (Qc n z (s + 1) - Qc n z s) = (2 * sin (z / 2)) ^ 2) ∧
      (∀ a b : Fin n, gnAct n a.val b.val = true → nsq (Qc n z b - Qc n z a) = 1) ∧
      (∀ w : Cfg n, (∀ s : Fin n, ip (Qc n z (s + 1) - Qc n z s) (w (s + 1) - w s) = 0) →
        (∀ a b : Fin n, gnAct n a.val b.val = true → ip (Qc n z b - Qc n z a) (w b - w a) = 0) →
        ∃ (t : ℝ × ℝ) (ω : ℝ), ∀ x, w x = t + ω • J (Qc n z x)) := by
  have hn16 : 16 ≤ n := by omega
  obtain ⟨z, hz, hF, hFd, huniq⟩ := root_all n hn16
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hz0 : 0 < z := lt_trans (by positivity) hz.1
  have hz1 : z < π / 4 := by
    have : π / n ≤ π / 16 := div_le_div_of_nonneg_left pi_pos.le (by norm_num) hN
    linarith [hz.2, pi_pos]
  have hc : cos (2 * z) ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
  refine ⟨z, hz, hF, hFd, huniq, fun s => ?_, fun a b h => chords_all z k hk hn hc a b h,
    fun w hs ha => published_rigid_all k hk hn hz0 hz1 w hs ha⟩
  by_cases h1 : s.val = 4 * k - 1
  · rw [closing_all z k hk hn s h1, hF, zero_add]
  by_cases h2 : s.val = 12 * k
  · rw [closing'_all z k hk hn s h2, hF, zero_add]
  exact sides_all z k hk hn hc s h1 h2

end Chiquipoli.Family.Trig.ConstructorAll
