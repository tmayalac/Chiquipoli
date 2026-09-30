/-
# The triangulated strip of `G_n`, and infinitesimal rigidity, for every `n = 16k`

The sides and the chords of `G_n` form a triangulated strip that leaves out only
the two closing sides `{2m−1, 2m}` and `{6m, 6m+1}` (`m = n/8`). A *rung*
`r(a, t)` is the chord `{a, [h + t]}` (`h = n/2`). The rungs are visited by the
lattice path `P`, which in block `q` passes through

    (4q,4q) (4q,4q+1) (4q+1,4q+1) (4q+2,4q+1) (4q+2,4q+2) (4q+3,4q+2) (4q+3,4q+3) (4q+3,4q+4).

The strip `S = (ρ_0, …, ρ_{n−2})` starts right after the point `(h/2, h/2)`,
which is not a chord. It runs to the end `(h−1, h)` of `P`, then continues from
`(0,0)` and ends at `(h/2 − 1, h/2)`.

* `strip_edge`: every rung of `S` is a pair of `G_n` (`gnAct`).
* `strip_step`: consecutive rungs share one endpoint. Their other endpoints are
  joined by a side that is not a closing side.
* `strip_cover`: every vertex is an endpoint of some rung.
* `strip_rigid`: if the rungs have length `1`, the non-closing sides have
  length `ℓ` with `0 < ℓ < 2`, and `w` keeps all these bars stationary to first
  order, then `w` is an infinitesimal rigid motion. Each step adds a triangle
  with sides `1, 1, ℓ`, and such a triangle is never flat.
* `problem2`: **Problem 2 (angular rigidity), for every `n = 16k`**, with the
  constructor's direction `(ṗ, ℓ')` as a hypothesis. At a simple zero the
  closing side's derivative is `F_n'(z) ≠ 0`, and then every `(v, η)` in the
  equality space has `η = 0` and `v` rigid.

No per-`n` data and no kernel checks are involved: the combinatorics are
proved by `omega` for a symbolic `k`.
-/
import ChiquipoliFamily.Interval.Assemble

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig.Strip

open Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig

/-! ## The lattice path -/

/-- The offsets of the eight points of a block. -/
def da : ℕ → ℕ
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 3 | 6 => 3 | _ => 3

def dt : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 3 | _ => 4

/-- The point `j` of the path `P`: `(Pa j, Pt j)`. -/
def Pa (j : ℕ) : ℕ := 4 * (j / 8) + da (j % 8)
def Pt (j : ℕ) : ℕ := 4 * (j / 8) + dt (j % 8)

lemma PaPt (q r : ℕ) (hr : r < 8) : Pa (8 * q + r) = 4 * q + da r ∧ Pt (8 * q + r) = 4 * q + dt r := by
  have h1 : (8 * q + r) / 8 = q := by omega
  have h2 : (8 * q + r) % 8 = r := by omega
  simp [Pa, Pt, h1, h2]

/-- One step of `P` adds `1` to one coordinate. Only the removed point `j = 8k`
steps along the side `4k − 1`, and only `j = 8k + 1` along the side `12k`. -/
lemma P_step (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    (Pa j = Pa (j - 1) + 1 ∧ Pt j = Pt (j - 1) ∧ (j ≠ 8 * k → Pa (j - 1) ≠ 4 * k - 1)) ∨
    (Pa j = Pa (j - 1) ∧ Pt j = Pt (j - 1) + 1 ∧ (j ≠ 8 * k + 1 → Pt (j - 1) ≠ 4 * k)) := by
  have hq := Nat.div_add_mod j 8
  have hr := Nat.mod_lt j (show 8 > 0 by norm_num)
  simp only [Pa, Pt]
  rcases Nat.eq_zero_or_pos (j % 8) with h0 | hpos
  · have e1 : (j - 1) / 8 = j / 8 - 1 := by omega
    have e2 : (j - 1) % 8 = 7 := by omega
    rw [e1, e2, h0]
    simp only [da, dt]
    omega
  · have e1 : (j - 1) / 8 = j / 8 := by omega
    have e2 : (j - 1) % 8 = j % 8 - 1 := by omega
    rw [e1, e2]
    generalize hR : j % 8 = r at *
    interval_cases r <;> simp only [da, dt, Nat.reduceSub, add_zero, true_and, and_true, true_or, or_true] <;> omega

lemma da_le (r : ℕ) : da r ≤ 3 := by unfold da; split <;> omega
lemma dt_le (r : ℕ) : dt r ≤ 4 := by unfold dt; split <;> omega
lemma dt_le' (r : ℕ) (hr : r < 7) : dt r ≤ 3 := by interval_cases r <;> simp [dt]

lemma Pa_lt (k j : ℕ) (hj : j < 16 * k) : Pa j < 8 * k := by
  have := da_le (j % 8); unfold Pa; omega

lemma Pt_lt (k j : ℕ) (hj : j < 16 * k - 1) : Pt j < 8 * k := by
  unfold Pt
  rcases Nat.lt_or_ge (j / 8) (2 * k - 1) with h | h
  · have := dt_le (j % 8); omega
  · have := dt_le' (j % 8) (by omega); omega

lemma P_last (k : ℕ) (hk : 1 ≤ k) : Pa (16 * k - 1) = 8 * k - 1 ∧ Pt (16 * k - 1) = 8 * k := by
  have := PaPt (2 * k - 1) 7 (by norm_num)
  rw [show 8 * (2 * k - 1) + 7 = 16 * k - 1 by omega] at this
  simp only [da, dt] at this
  omega

/-- Each point of `P` other than `(4k, 4k)` is a chord of `G_n`: `t − a ∈ Δ(a mod 4)`. -/
lemma P_delta (k j : ℕ) (hj : j < 16 * k) (hne : j ≠ 8 * k) :
    (Pt j = Pa j ∧ Pa j ≠ 4 * k) ∨ (Pt j = Pa j + 1 ∧ (Pa j % 4 = 0 ∨ Pa j % 4 = 3)) ∨
      (Pt j + 1 = Pa j ∧ (Pa j % 4 = 2 ∨ Pa j % 4 = 3)) := by
  have hq := Nat.div_add_mod j 8
  have hr := Nat.mod_lt j (show 8 > 0 by norm_num)
  simp only [Pa, Pt]
  generalize hR : j % 8 = r at *
  interval_cases r <;> simp only [da, dt, Nat.reduceSub, add_zero, true_and, and_true, true_or, or_true] <;> omega

/-! ## The strip -/

/-- The index in `P` of the rung `ρ_i` (`n = 16k`, `0 ≤ i ≤ n − 2`). -/
def Sj (k i : ℕ) : ℕ := if i + 1 < 8 * k then 8 * k + 1 + i else i + 1 - 8 * k

lemma Sj_lt (k i : ℕ) (hi : i < 16 * k - 1) : Sj k i < 16 * k ∧ Sj k i ≠ 8 * k := by
  unfold Sj; split_ifs <;> omega

lemma exists_Sj (k j : ℕ) (hj : j < 16 * k) (hne : j ≠ 8 * k) : ∃ i < 16 * k - 1, Sj k i = j := by
  rcases Nat.lt_or_ge (8 * k) j with h | h
  · exact ⟨j - 8 * k - 1, by omega, by unfold Sj; split_ifs <;> omega⟩
  · exact ⟨j + 8 * k - 1, by omega, by unfold Sj; split_ifs <;> omega⟩

variable {n : ℕ} [NeZero n]

/-- The vertex `x mod n`. -/
def ver (n : ℕ) [NeZero n] (x : ℕ) : Fin n := ⟨x % n, Nat.mod_lt _ (NeZero.pos n)⟩

lemma ver_val (x : Fin n) : ver n x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

lemma ver_succ (x : ℕ) : ver n x + 1 = ver n (x + 1) := by
  apply Fin.ext
  rw [fin_add_one_val]
  simp only [ver]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ver_val_of_lt {x : ℕ} (h : x < n) : (ver n x).val = x := Nat.mod_eq_of_lt h

/-- The rung `ρ_i = {a, [h + t]}`, as the pair `(a, [h + t])`. -/
def R (n : ℕ) [NeZero n] (k i : ℕ) : Fin n × Fin n :=
  (ver n (Pa (Sj k i)), ver n (8 * k + Pt (Sj k i)))

/-- **Consecutive rungs.** `ρ_{i−1} = {y₁, y₂}` and `ρ_i = {y₁, u}`, and `y₂ → u` is
the side `s → s + 1`, which is not a closing side. -/
theorem strip_step (hn : n = 16 * k) (hk : 1 ≤ k) (i : ℕ) (hi1 : 1 ≤ i) (hi : i < 16 * k - 1) :
    ∃ y1 y2 u s : Fin n, (R n k (i - 1) = (y1, y2) ∨ R n k (i - 1) = (y2, y1)) ∧
      (R n k i = (y1, u) ∨ R n k i = (u, y1)) ∧ y2 = s ∧ u = s + 1 ∧
      s.val ≠ 4 * k - 1 ∧ s.val ≠ 12 * k := by
  rcases eq_or_ne i (8 * k - 1) with hJ | hJ
  · -- the junction: `(h−1, h) = {h−1, 0}` → `(0, 0) = {0, h}`
    have e1 : Sj k (i - 1) = 16 * k - 1 := by unfold Sj; split_ifs <;> omega
    have e2 : Sj k i = 0 := by unfold Sj; split_ifs <;> omega
    obtain ⟨l1, l2⟩ := P_last k hk
    have z1 : Pa 0 = 0 := rfl
    have z2 : Pt 0 = 0 := rfl
    refine ⟨ver n 0, ver n (8 * k - 1), ver n (8 * k), ver n (8 * k - 1), Or.inr ?_, Or.inl ?_, rfl,
      ?_, ?_, ?_⟩
    · simp only [R, e1, l1, l2, Prod.mk.injEq, true_and]
      apply Fin.ext; simp only [ver]; rw [show 8 * k + 8 * k = n by omega, Nat.mod_self, Nat.zero_mod]
    · simp only [R, e2, z1, z2, add_zero]
    · rw [ver_succ, show 8 * k - 1 + 1 = 8 * k by omega]
    · rw [ver_val_of_lt (by omega)]; omega
    · rw [ver_val_of_lt (by omega)]; omega
  · obtain ⟨hlt, hne⟩ := Sj_lt k i hi
    have e : Sj k (i - 1) = Sj k i - 1 := by unfold Sj; split_ifs <;> omega
    have hj1 : 1 ≤ Sj k i := by unfold Sj; split_ifs <;> omega
    have hj2 : Sj k i ≠ 8 * k + 1 := by unfold Sj; split_ifs <;> omega
    set j := Sj k i
    have hPa := Pa_lt k (j - 1) (by omega)
    have hPt := Pt_lt k (j - 1) (by omega)
    rcases P_step k j hk hj1 with ⟨ha, ht, hs⟩ | ⟨ha, ht, hs⟩
    · -- a step in `a`: shared `[h + t]`, side `{a − 1, a}`
      refine ⟨ver n (8 * k + Pt j), ver n (Pa (j - 1)), ver n (Pa j), ver n (Pa (j - 1)),
        Or.inr ?_, Or.inr ?_, rfl, ?_, ?_, ?_⟩
      · simp only [R, e, ht]
      · simp only [R, j]
      · rw [ver_succ, ha]
      · rw [ver_val_of_lt (by omega)]; exact hs hne
      · rw [ver_val_of_lt (by omega)]; omega
    · -- a step in `t`: shared `a`, side `{h + t − 1, h + t}`
      refine ⟨ver n (Pa j), ver n (8 * k + Pt (j - 1)), ver n (8 * k + Pt j), ver n (8 * k + Pt (j - 1)),
        Or.inl ?_, Or.inl ?_, rfl, ?_, ?_, ?_⟩
      · simp only [R, e, ha]
      · simp only [R, j]
      · rw [ver_succ, ht, add_assoc]
      · rw [ver_val_of_lt (by omega)]; omega
      · rw [ver_val_of_lt (by omega)]; have := hs hj2; omega

/-- **Every vertex is on the strip.** -/
theorem strip_cover (hn : n = 16 * k) (hk : 1 ≤ k) (x : Fin n) :
    ∃ i < 16 * k - 1, (R n k i).1 = x ∨ (R n k i).2 = x := by
  have hx := x.isLt
  -- a point `j ≠ 8k` of `P` with `x` as an endpoint
  have hj : ∃ j < 16 * k, j ≠ 8 * k ∧ (Pa j = x.val ∨ 8 * k + Pt j = x.val) := by
    have hq := Nat.div_add_mod x.val 4
    have h4 := Nat.mod_lt x.val (show 4 > 0 by norm_num)
    rcases Nat.lt_or_ge x.val (8 * k) with hlo | hhi
    · generalize hs : x.val % 4 = s at *
      interval_cases s
      · refine ⟨8 * (x.val / 4) + 1, by omega, by omega, Or.inl ?_⟩
        rw [(PaPt _ 1 (by norm_num)).1]; simp only [da]; omega
      · refine ⟨8 * (x.val / 4) + 2, by omega, by omega, Or.inl ?_⟩
        rw [(PaPt _ 2 (by norm_num)).1]; simp only [da]; omega
      · refine ⟨8 * (x.val / 4) + 3, by omega, by omega, Or.inl ?_⟩
        rw [(PaPt _ 3 (by norm_num)).1]; simp only [da]; omega
      · refine ⟨8 * (x.val / 4) + 5, by omega, by omega, Or.inl ?_⟩
        rw [(PaPt _ 5 (by norm_num)).1]; simp only [da]; omega
    · have hq' := Nat.div_add_mod (x.val - 8 * k) 4
      have h4' := Nat.mod_lt (x.val - 8 * k) (show 4 > 0 by norm_num)
      generalize hs : (x.val - 8 * k) % 4 = s at *
      interval_cases s
      · rcases eq_or_ne ((x.val - 8 * k) / 4) k with hq0 | hq0
        · refine ⟨8 * (k - 1) + 7, by omega, by omega, Or.inr ?_⟩
          rw [(PaPt _ 7 (by norm_num)).2]; simp only [dt]; omega
        · refine ⟨8 * ((x.val - 8 * k) / 4), by omega, by omega, Or.inr ?_⟩
          have := (PaPt ((x.val - 8 * k) / 4) 0 (by norm_num)).2
          rw [add_zero] at this; rw [this]; simp only [dt]; omega
      · refine ⟨8 * ((x.val - 8 * k) / 4) + 1, by omega, by omega, Or.inr ?_⟩
        rw [(PaPt _ 1 (by norm_num)).2]; simp only [dt]; omega
      · refine ⟨8 * ((x.val - 8 * k) / 4) + 4, by omega, by omega, Or.inr ?_⟩
        rw [(PaPt _ 4 (by norm_num)).2]; simp only [dt]; omega
      · refine ⟨8 * ((x.val - 8 * k) / 4) + 6, by omega, by omega, Or.inr ?_⟩
        rw [(PaPt _ 6 (by norm_num)).2]; simp only [dt]; omega
  obtain ⟨j, hj, hne, hx'⟩ := hj
  obtain ⟨i, hi, rfl⟩ := exists_Sj k j hj hne
  refine ⟨i, hi, ?_⟩
  rcases hx' with h | h
  · left; simp only [R, h, ver_val]
  · right; simp only [R, h, ver_val]

/-- **Every rung of the strip is a pair of `G_n`.** -/
theorem strip_edge (hn : n = 16 * k) (hk : 1 ≤ k) (i : ℕ) (hi : i < 16 * k - 1) :
    gnAct n (R n k i).1.val (R n k i).2.val = true := by
  obtain ⟨hlt, hne⟩ := Sj_lt k i hi
  have hΔ := P_delta k _ hlt hne
  have ha := Pa_lt k _ hlt
  have ht : Pt (Sj k i) ≤ 8 * k := by
    rcases Nat.lt_or_ge (Sj k i) (16 * k - 1) with h | h
    · exact (Pt_lt k _ h).le
    · rw [show Sj k i = 16 * k - 1 by omega]; exact (P_last k hk).2.le
  simp only [R, ver]
  set a := Pa (Sj k i)
  set t := Pt (Sj k i)
  subst hn
  rw [Nat.mod_eq_of_lt (by omega : a < 16 * k)]
  have hd : ((8 * k + t) % (16 * k) + 16 * k - a) % (16 * k) = 8 * k + t - a := by
    rcases Nat.lt_or_ge t (8 * k) with h | h
    · rw [Nat.mod_eq_of_lt (by omega : 8 * k + t < 16 * k),
        Nat.mod_eq_sub_mod (by omega : 16 * k ≤ 8 * k + t + 16 * k - a), Nat.mod_eq_of_lt (by omega)]
      omega
    · have : t = 8 * k := by omega
      rw [this, show 8 * k + 8 * k = 16 * k by ring, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
      omega
  unfold gnAct
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, hd]
  left
  omega

/-! ## Rigidity along the strip -/

/-- A triangle with sides `1, 1, ℓ` (`0 < ℓ < 2`) is not flat. -/
lemma tri_det {a b : ℝ × ℝ} {L : ℝ} (ha : nsq a = 1) (hb : nsq b = L) (hab : nsq (b - a) = 1)
    (hL0 : 0 < L) (hL4 : L < 4) : a.1 * b.2 - a.2 * b.1 ≠ 0 := by
  intro h
  simp only [nsq, ip, Prod.fst_sub, Prod.snd_sub] at ha hb hab
  have hdot : a.1 * b.1 + a.2 * b.2 = L / 2 := by nlinarith
  have hlag : (a.1 * b.2 - a.2 * b.1) ^ 2 + (a.1 * b.1 + a.2 * b.2) ^ 2
      = (a.1 ^ 2 + a.2 ^ 2) * (b.1 ^ 2 + b.2 ^ 2) := by ring
  rw [h, hdot] at hlag
  nlinarith

omit [NeZero n] in
/-- The two endpoints of a rung, with the bar and the length in either orientation. -/
lemma rung_facts {p w : Cfg n} {y1 y2 : Fin n} {r : Fin n × Fin n}
    (hr : r = (y1, y2) ∨ r = (y2, y1))
    (h : nsq (p r.2 - p r.1) = 1 ∧ ip (p r.2 - p r.1) (w r.2 - w r.1) = 0) :
    nsq (p y2 - p y1) = 1 ∧ ip (p y2 - p y1) (w y2 - w y1) = 0 := by
  rcases hr with rfl | rfl
  · exact h
  · exact ⟨by rw [nsq_comm]; exact h.1, bar_flip h.2⟩

/-- **Rigidity of the strip.** If every rung has length `1` and is stationary, and
every non-closing side has squared length `L ∈ (0, 4)` and is stationary, then
`w` is an infinitesimal rigid motion. The two closing sides are not used. -/
theorem strip_rigid (hn : n = 16 * k) (hk : 1 ≤ k) (p w : Cfg n) {L : ℝ} (hL0 : 0 < L) (hL4 : L < 4)
    (hrung : ∀ i < 16 * k - 1, nsq (p (R n k i).2 - p (R n k i).1) = 1 ∧
      ip (p (R n k i).2 - p (R n k i).1) (w (R n k i).2 - w (R n k i).1) = 0)
    (hside : ∀ s : Fin n, s.val ≠ 4 * k - 1 → s.val ≠ 12 * k →
      nsq (p (s + 1) - p s) = L ∧ ip (p (s + 1) - p s) (w (s + 1) - w s) = 0) :
    ∃ (t : ℝ × ℝ) (ω : ℝ), ∀ x, w x = t + ω • J (p x) := by
  -- pin the first rung
  obtain ⟨h0n, h0b⟩ := hrung 0 (by omega)
  have hne : p (R n k 0).1 ≠ p (R n k 0).2 := by
    intro h; rw [h, sub_self] at h0n; simp [nsq, ip] at h0n
  obtain ⟨t, ω, ht1, ht2⟩ := pin_bar hne h0b
  set w' : Cfg n := fun x => w x - (t + ω • J (p x)) with hw'
  have z1 : w' (R n k 0).1 = 0 := by simp only [hw', ← ht1, sub_self]
  have z2 : w' (R n k 0).2 = 0 := by simp only [hw', ← ht2, sub_self]
  have hrung' : ∀ i < 16 * k - 1, nsq (p (R n k i).2 - p (R n k i).1) = 1 ∧
      ip (p (R n k i).2 - p (R n k i).1) (w' (R n k i).2 - w' (R n k i).1) = 0 :=
    fun i hi => ⟨(hrung i hi).1, bar_sub_rigid (hrung i hi).2⟩
  -- walk along the strip
  have key : ∀ i, i < 16 * k - 1 → w' (R n k i).1 = 0 ∧ w' (R n k i).2 = 0 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨z1, z2⟩
    | succ i ih =>
      intro hi
      obtain ⟨y1, y2, u, s, hprev, hcur, hs1, hs2, hsa, hsb⟩ := strip_step hn hk (i + 1) (by omega) hi
      rw [Nat.add_sub_cancel] at hprev
      obtain ⟨zi1, zi2⟩ := ih (by omega)
      have hy : w' y1 = 0 ∧ w' y2 = 0 := by
        rcases hprev with h | h <;> rw [h] at zi1 zi2 <;> simp only at zi1 zi2
        · exact ⟨zi1, zi2⟩
        · exact ⟨zi2, zi1⟩
      have hprevF := rung_facts hprev (hrung' i (by omega))
      have hcurF := rung_facts (y1 := y1) (y2 := u) (by rcases hcur with h | h <;> simp [h])
        (hrung' (i + 1) hi)
      obtain ⟨hsn, hsb'⟩ := hside s hsa hsb
      rw [← hs2, ← hs1] at hsn hsb'
      have hsb'' := bar_sub_rigid (t := t) (ω := ω) hsb'
      have hu : w' u = 0 := by
        apply henneberg_step (Pi := p y1) (Pj := p y2) (wi := w' y1) (wj := w' y2) hcurF.2 hsb'' hy.1 hy.2
        apply tri_det hcurF.1 hsn _ hL0 hL4
        rw [sub_sub_sub_cancel_left, nsq_comm]; exact hprevF.1
      rcases hcur with h | h <;> rw [h]
      · exact ⟨hy.1, hu⟩
      · exact ⟨hu, hy.1⟩
  refine ⟨t, ω, fun x => ?_⟩
  obtain ⟨i, hi, hx⟩ := strip_cover hn hk x
  have hz : w' x = 0 := by
    rcases hx with h | h
    · rw [← h]; exact (key i hi).1
    · rw [← h]; exact (key i hi).2
  simpa [hw', sub_eq_zero] using hz

/-- **Rigidity of `G_n` without its closing sides**, stated on the pairs of `G_n`. -/
theorem gn_rigid (hn : n = 16 * k) (hk : 1 ≤ k) (p w : Cfg n) {L : ℝ} (hL0 : 0 < L) (hL4 : L < 4)
    (hact : ∀ a b : Fin n, gnAct n a.val b.val = true →
      nsq (p b - p a) = 1 ∧ ip (p b - p a) (w b - w a) = 0)
    (hside : ∀ s : Fin n, s.val ≠ 4 * k - 1 → s.val ≠ 12 * k →
      nsq (p (s + 1) - p s) = L ∧ ip (p (s + 1) - p s) (w (s + 1) - w s) = 0) :
    ∃ (t : ℝ × ℝ) (ω : ℝ), ∀ x, w x = t + ω • J (p x) :=
  strip_rigid hn hk p w hL0 hL4 (fun i hi => hact _ _ (strip_edge hn hk i hi)) hside

/-! ## Problem 2 -/

/-- **Problem 2 (angular rigidity), for every `n = 16k`.** Let `p` have unit
distance on the pairs of `G_n` and side `ℓ ∈ (0, 2)` off the closing sides.
Let `(ṗ, ℓ')` be a direction (the constructor's derivative at the root) that
keeps the pairs of `G_n` and the non-closing sides stationary, with `ℓ' ≠ 0`,
and that moves the closing side `4k − 1`. Then every `(v, η)` that keeps all
sides and all pairs of `G_n` stationary has `η = 0`, and `v` is an
infinitesimal rigid motion.

For the constructor, `eD p ℓ ṗ ℓ' (4k − 1)` is `F_n'(z)`, the derivative of the
closing side's squared length `F_n + ℓ²` minus that of `ℓ²`. `root_all` proves
that it is nonzero. -/
theorem problem2 (hn : n = 16 * k) (hk : 1 ≤ k) (p : Cfg n) {l : ℝ} (hl0 : 0 < l) (hl2 : l < 2)
    (hact : ∀ a b : Fin n, gnAct n a.val b.val = true → nsq (p b - p a) = 1)
    (hside : ∀ s : Fin n, s.val ≠ 4 * k - 1 → s.val ≠ 12 * k → nsq (p (s + 1) - p s) = l ^ 2)
    (pd : Cfg n) (ld : ℝ) (hld : ld ≠ 0)
    (hpd_act : ∀ a b : Fin n, gnAct n a.val b.val = true → dD p pd a b = 0)
    (hpd_side : ∀ s : Fin n, s.val ≠ 4 * k - 1 → s.val ≠ 12 * k → eD p l pd ld s = 0)
    (hpd_close : eD p l pd ld (ver n (4 * k - 1)) ≠ 0)
    (v : Cfg n) (η : ℝ)
    (hv_act : ∀ a b : Fin n, gnAct n a.val b.val = true → dD p v a b = 0)
    (hv_side : ∀ s : Fin n, eD p l v η s = 0) :
    η = 0 ∧ ∃ (t : ℝ × ℝ) (ω : ℝ), ∀ x, v x = t + ω • J (p x) := by
  set c := η / ld with hc
  set w : Cfg n := fun x => v x - c • pd x with hw
  -- `(w, 0) = (v, η) − c (ṗ, ℓ')` keeps the strip stationary
  have lin_e : ∀ s : Fin n, eD p l w 0 s = eD p l v η s - c * eD p l pd ld s := by
    intro s
    simp only [eD, hw, hc, ip, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring
  have lin_d : ∀ a b : Fin n, dD p w a b = dD p v a b - c * dD p pd a b := by
    intro a b
    simp only [dD, hw, ip, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hL0 : 0 < l ^ 2 := by positivity
  have hL4 : l ^ 2 < 4 := by nlinarith
  obtain ⟨t, ω, hrig⟩ := gn_rigid hn hk p w hL0 hL4
    (fun a b h => ⟨hact a b h, by
      have := lin_d a b; rw [hv_act a b h, hpd_act a b h] at this
      simp only [dD] at this; linarith⟩)
    (fun s h1 h2 => ⟨hside s h1 h2, by
      have := lin_e s; rw [hv_side s, hpd_side s h1 h2] at this
      simp only [eD] at this; linarith⟩)
  -- on the closing side, the rigid part contributes nothing
  set s0 := ver n (4 * k - 1)
  have hw0 : eD p l w 0 s0 = 0 := by
    simp only [eD, hrig, mul_zero, sub_zero]
    rw [rigid_bar]; ring
  have := lin_e s0
  rw [hw0, hv_side s0, zero_sub] at this
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp (neg_eq_zero.mp this.symm) with h | h
    · exact h
    · exact absurd h hpd_close
  have hη : η = 0 := by
    rw [hc] at hc0
    rcases div_eq_zero_iff.mp hc0 with h | h
    · exact h
    · exact absurd h hld
  refine ⟨hη, t, ω, fun x => ?_⟩
  have := hrig x
  simp only [hw, hc0, zero_smul, sub_zero] at this
  exact this

end Chiquipoli.Family.Trig.Strip
