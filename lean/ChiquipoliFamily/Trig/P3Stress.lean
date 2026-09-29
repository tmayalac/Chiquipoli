/-
# Problem 3: the stress, in closed form, for every `n = 16k`

The multipliers of the note on Problem 3, as a stress on the bars of the
published polygon: side `s` carries `sigS s`, rung `ρ_i` of the strip carries
`lamR i`. On the first half of the strip (`i ≤ 8k − 1`) they are given in closed
form by the recursion `tau` and by `lamF`; the second half is the mirror image
(`σ(x) = n − x`).

Normalisation: the closing sides carry `−1/ℓ`, i.e. `α_c = −1` in the notation of
the note, so that `α_j = −τ_j` and the raw weight of a side is `α/ℓ`.
-/
import ChiquipoliFamily.Trig.RungVec
import ChiquipoliFamily.Trig.P3Core

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig.P3

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Chiquipoli.Family.Trig.RungVec

/-! ## The parameters -/

section defs
variable (k : ℕ) (z ag : ℝ)

/-- `φ = π/2 − (8k − 1) z`: the first rung is `−e(φ)`. -/
noncomputable def φ : ℝ := π / 2 - (8 * (k : ℝ) - 1) * z
/-- The side length. -/
noncomputable def ell : ℝ := 2 * sin (z / 2)
/-- `κ = 2a/ℓ`, `a` the horizontal width of the gap (`ag`). -/
noncomputable def κ : ℝ := 2 * ag / ell z
/-- The angle of rung `i`: `u_i = −e(θ_i)` on the first half. -/
noncomputable def θ (i : ℕ) : ℝ := φ k z + i * z

/-- Step `i` (from `ρ_i` to `ρ_{i+1}`) moves the `a`-end: the pattern `a a t a t t a t`. -/
def typA (i : ℕ) : Bool := decide (i % 8 = 0) || decide (i % 8 = 1) || decide (i % 8 = 3) || decide (i % 8 = 6)

/-- `+1` at a switch `a → t`, `−1` at a switch `t → a`, `0` otherwise. -/
noncomputable def eps (i : ℕ) : ℝ :=
  if typA (i - 1) = true ∧ typA i = false then 1
  else if typA (i - 1) = false ∧ typA i = true then -1 else 0

/-- `τ_i = −α_i`, the side multipliers along the first half. -/
noncomputable def tau : ℕ → ℝ
  | 0 => sin (φ k z) * (cos (φ k z) - ag) / sin z
  | i + 1 => tau i + eps (i + 1) * κ z ag * sin (θ k z (i + 1)) / cos (z / 2)

/-- The rung multipliers on the first half, `0 ≤ i ≤ 8k − 1`. -/
noncomputable def lamF (i : ℕ) : ℝ :=
  if i = 0 then tau k z ag 0 * sin (z / 2) + (ag * cos (φ k z) + sin (φ k z) ^ 2) / ell z
  else if i = 8 * k - 1 then tau k z ag (8 * k - 2) * ell z
  else (tau k z ag (i - 1) + tau k z ag i) * sin (z / 2) - eps i * κ z ag * cos (θ k z i)

/-- All rung multipliers: the second half mirrors the first. -/
noncomputable def lamR (i : ℕ) : ℝ := if i ≤ 8 * k - 1 then lamF k z ag i else lamF k z ag (16 * k - 2 - i)

/-- The step of the strip that creates side `s` of the first half. -/
def stepOf (s : ℕ) : ℕ :=
  if 4 * k ≤ s ∧ s ≤ 8 * k - 2 then
    8 * (s / 4) + (if s % 4 = 0 then 2 else if s % 4 = 1 then 3 else if s % 4 = 2 then 5 else 8) - 8 * k - 2
  else if s = 8 * k - 1 then 8 * k - 2
  else 8 * ((s - 8 * k) / 4) + (if (s - 8 * k) % 4 = 0 then 1 else if (s - 8 * k) % 4 = 1 then 4
    else if (s - 8 * k) % 4 = 2 then 6 else 7) - 8 * k - 2

/-- Side `s` is created in the first half of the strip. -/
def firstSide (s : ℕ) : Prop := (4 * k ≤ s ∧ s ≤ 8 * k - 1) ∨ (12 * k + 1 ≤ s ∧ s ≤ 16 * k - 1)

instance (s : ℕ) : Decidable (firstSide k s) := by unfold firstSide; infer_instance

/-- The side weights: `−τ/ℓ` on the strip, `−1/ℓ` on the closing sides, mirrored. -/
noncomputable def sigS (s : ℕ) : ℝ :=
  if s = 4 * k - 1 ∨ s = 12 * k then -1 / ell z
  else if firstSide k s then -tau k z ag (stepOf k s) / ell z
  else -tau k z ag (stepOf k (16 * k - 1 - s)) / ell z

end defs

/-! ## Lemma R, as `−e(θ_i)` -/

lemma e_eq_Φ (k : ℕ) (z : ℝ) (i : ℕ) :
    e (θ k z i) = Φ z (8 * (k : ℝ) - 1 - i) := by
  unfold e θ φ Φ
  have h : (8 * (k : ℝ) - 1 - i) * z = π / 2 - (π / 2 - (8 * (k : ℝ) - 1) * z + i * z) := by ring
  rw [h, sin_pi_div_two_sub, cos_pi_div_two_sub]

/-- The rungs of the first half are `−e(θ_i)`; the middle rung is `+e(θ_{8k−1}) = (0, 1)`. -/
theorem rung_e (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) (z : ℝ) (hc : cos (2 * z) ≠ 0)
    (i : ℕ) (hi : i + 1 < 8 * k) :
    Qc n z (Strip.R n k i).2 - Qc n z (Strip.R n k i).1 = -e (θ k z i) := by
  rw [rung_vec z k hk hn hc i (by omega), if_pos hi, e_eq_Φ, neg_one_smul]

theorem rung_mid (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) (z : ℝ) (hc : cos (2 * z) ≠ 0) :
    Qc n z (Strip.R n k (8 * k - 1)).2 - Qc n z (Strip.R n k (8 * k - 1)).1 = e (θ k z (8 * k - 1)) := by
  rw [rung_vec z k hk hn hc _ (by omega), if_neg (by omega), e_eq_Φ, one_smul]

/-! ## Sums of forces -/

/-- Only the two sides at `x` pull on `x`. -/
lemma side_part {n : ℕ} [NeZero n] (hn : 3 ≤ n) (p : Cfg n) (w : Fin n → ℝ) (x : Fin n) :
    ∑ s : Fin n, w s • contrib p (s, s + 1) x
      = w x • (p (x + 1) - p x) + w (x - 1) • (p (x - 1) - p x) := by
  have hne : x ≠ x - 1 := by
    intro h
    have : (1 : Fin n) = 0 := by
      have := congrArg (fun y => y - (x - 1)) h
      simp only [sub_self] at this
      rw [sub_sub_cancel] at this; exact this
    have h1 : (1 : Fin n).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [this] at h1; simp at h1
  rw [Fintype.sum_eq_add x (x - 1) hne]
  · congr 1
    · simp [contrib]
    · have h1 : (x - 1 : Fin n) ≠ x := fun h => hne h.symm
      simp [contrib, h1]
  · rintro s ⟨h1, h2⟩
    have h3 : s + 1 ≠ x := fun h => h2 (by rw [← h]; simp)
    simp [contrib, h1, h3]

/-- A sum over `Fin N` whose terms vanish outside `[lo, hi]`. -/
lemma sum_fin_Icc {V : Type*} [AddCommMonoid V] {N : ℕ} (g : ℕ → V) (lo hi : ℕ) (hhi : hi < N)
    (h0 : ∀ i < N, (i < lo ∨ hi < i) → g i = 0) :
    ∑ i : Fin N, g i = ∑ i ∈ Finset.Icc lo hi, g i := by
  rw [Fin.sum_univ_eq_sum_range g N]
  symm
  apply Finset.sum_subset
  · intro i hi'; simp only [Finset.mem_Icc] at hi'; simp only [Finset.mem_range]; omega
  · intro i hiN hiI
    simp only [Finset.mem_Icc, not_and_or, not_le] at hiI
    simp only [Finset.mem_range] at hiN
    exact h0 i hiN (by omega)

/-- Telescoping over `[lo, hi]`, `1 ≤ lo ≤ hi + 1`. -/
lemma sum_Icc_telescope {V : Type*} [AddCommGroup V] (T : ℕ → V) (lo : ℕ) (hlo : 1 ≤ lo) :
    ∀ d hi, hi + 1 = lo + d → ∑ i ∈ Finset.Icc lo hi, (T i - T (i - 1)) = T hi - T (lo - 1) := by
  intro d
  induction d with
  | zero =>
    intro hi hd
    have : hi = lo - 1 := by omega
    subst this
    rw [Finset.Icc_eq_empty (by omega)]; simp
  | succ d ih =>
    intro hi hd
    have e : hi = (hi - 1) + 1 := by omega
    rw [e, Finset.sum_Icc_succ_top (by omega), ih (hi - 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    abel

/-! ## The first half of the strip, combinatorially -/

open Strip in
/-- A step of `P` at `J ≡ 1, 2, 4, 7 (mod 8)` advances the `a`-end. -/
lemma P_succ_a (J : ℕ) (h : J % 8 = 1 ∨ J % 8 = 2 ∨ J % 8 = 4 ∨ J % 8 = 7) :
    Pa (J + 1) = Pa J + 1 ∧ Pt (J + 1) = Pt J := by
  have hq := Nat.div_add_mod J 8
  simp only [Pa, Pt]
  rcases h with h | h | h | h
  · rw [show (J + 1) / 8 = J / 8 by omega, show (J + 1) % 8 = 2 by omega, h]; simp only [da, dt]; (first | trivial | omega | (constructor <;> (first | trivial | omega)))
  · rw [show (J + 1) / 8 = J / 8 by omega, show (J + 1) % 8 = 3 by omega, h]; simp only [da, dt]; (first | trivial | omega | (constructor <;> (first | trivial | omega)))
  · rw [show (J + 1) / 8 = J / 8 by omega, show (J + 1) % 8 = 5 by omega, h]; simp only [da, dt]; (first | trivial | omega | (constructor <;> (first | trivial | omega)))
  · rw [show (J + 1) / 8 = J / 8 + 1 by omega, show (J + 1) % 8 = 0 by omega, h]; simp only [da, dt]; (first | trivial | omega | (constructor <;> (first | trivial | omega)))

open Strip in
/-- A step of `P` at `J ≡ 0, 3, 5, 6 (mod 8)` advances the `t`-end. -/
lemma P_succ_t (J : ℕ) (h : J % 8 = 0 ∨ J % 8 = 3 ∨ J % 8 = 5 ∨ J % 8 = 6) :
    Pa (J + 1) = Pa J ∧ Pt (J + 1) = Pt J + 1 := by
  have hq := Nat.div_add_mod J 8
  simp only [Pa, Pt]
  rcases h with h | h | h | h
  · rw [show (J + 1) / 8 = J / 8 by omega, show (J + 1) % 8 = 1 by omega, h]; simp only [da, dt]; (first | trivial | omega | (constructor <;> (first | trivial | omega)))
  · rw [show (J + 1) / 8 = J / 8 by omega, show (J + 1) % 8 = 4 by omega, h]; simp only [da, dt]; (first | trivial | omega | (constructor <;> (first | trivial | omega)))
  · rw [show (J + 1) / 8 = J / 8 by omega, show (J + 1) % 8 = 6 by omega, h]; simp only [da, dt]; (first | trivial | omega | (constructor <;> (first | trivial | omega)))
  · rw [show (J + 1) / 8 = J / 8 by omega, show (J + 1) % 8 = 7 by omega, h]; simp only [da, dt]; (first | trivial | omega | (constructor <;> (first | trivial | omega)))

/-- `typA i` in terms of the residue. -/
lemma typA_iff (i : ℕ) : typA i = true ↔ (i % 8 = 0 ∨ i % 8 = 1 ∨ i % 8 = 3 ∨ i % 8 = 6) := by
  simp [typA, or_assoc]

lemma typA_false_iff (i : ℕ) : typA i = false ↔ (i % 8 = 2 ∨ i % 8 = 4 ∨ i % 8 = 5 ∨ i % 8 = 7) := by
  have := Nat.mod_lt i (show 8 > 0 by norm_num)
  simp only [typA, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

section half
variable {k : ℕ} (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k)
include hk hn

/-- The rungs of the first half, read off `P`. -/
lemma R_first (i : ℕ) (hi : i + 1 < 8 * k) :
    (Strip.R n k i).1.val = Strip.Pa (8 * k + 1 + i) ∧
    (Strip.R n k i).2.val = (8 * k + Strip.Pt (8 * k + 1 + i)) % n := by
  have hs : Strip.Sj k i = 8 * k + 1 + i := by unfold Strip.Sj; rw [if_pos hi]
  have ha := Strip.Pa_lt k (8 * k + 1 + i) (by omega)
  simp only [Strip.R, Strip.ver, hs]
  exact ⟨Nat.mod_eq_of_lt (by omega), trivial⟩

/-- The rungs of the second half have their `a`-end in `[0, 4k)` and their
`t`-end in `[8k, 12k]`. -/
lemma R_second (i : ℕ) (hi1 : 8 * k ≤ i + 1) (hi : i < 16 * k - 1) :
    (Strip.R n k i).1.val < 4 * k ∧ 8 * k ≤ (Strip.R n k i).2.val ∧ (Strip.R n k i).2.val ≤ 12 * k := by
  have hs : Strip.Sj k i = i + 1 - 8 * k := by unfold Strip.Sj; rw [if_neg (by omega)]
  obtain ⟨h1, h2, -⟩ := Pa_Pt_lo k (i + 1 - 8 * k) hk (by omega)
  simp only [Strip.R, Strip.ver, hs]
  subst hn
  refine ⟨by rw [Nat.mod_eq_of_lt (by omega)]; exact h1, ?_, ?_⟩ <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega

end half

/-! ## The force at a vertex -/

/-- The net force of the stress at vertex `x` of the published polygon. -/
noncomputable def force (k : ℕ) (z ag : ℝ) {n : ℕ} [NeZero n] (x : Fin n) : ℝ × ℝ :=
  (∑ s : Fin n, sigS k z ag s.val • contrib (Qc n z) (s, s + 1) x)
    + ∑ i : Fin (n - 1), lamR k z ag i.val • contrib (Qc n z) (Strip.R n k i.val) x

lemma θ_succ (k : ℕ) (z : ℝ) (i : ℕ) : θ k z i + 2 * (z / 2) = θ k z (i + 1) := by
  unfold θ; push_cast; ring

lemma S_side (k : ℕ) (z ag : ℝ) (i : ℕ) :
    S (tau k z ag i) (θ k z i) (z / 2) = (-tau k z ag i / ell z) • (e (θ k z (i + 1)) - e (θ k z i)) := by
  unfold S ell
  rw [θ_succ]
  congr 1
  abel

/-- **One rung**, for `1 ≤ i ≤ 8k − 2`. -/
theorem rung_G (k : ℕ) (z ag : ℝ) (hw : sin (z / 2) ≠ 0) (hcw : cos (z / 2) ≠ 0) (i : ℕ)
    (hi1 : 1 ≤ i) (hi2 : i ≤ 8 * k - 2) :
    lamR k z ag i • (-e (θ k z i)) - S (tau k z ag (i - 1)) (θ k z (i - 1)) (z / 2)
      + S (tau k z ag i) (θ k z i) (z / 2) = ((eps i * κ z ag, 0) : ℝ × ℝ) := by
  have h := rung_core (θ k z i) (z / 2) (tau k z ag (i - 1)) (eps i) (κ z ag) hw hcw
  simp only at h
  have ei : i = (i - 1) + 1 := by omega
  have htau : tau k z ag i = tau k z ag (i - 1) + eps i * κ z ag * sin (θ k z i) / cos (z / 2) := by
    conv_lhs => rw [ei]
    rw [tau, ← ei]
  have hlam : lamR k z ag i = (tau k z ag (i - 1) + tau k z ag i) * sin (z / 2) - eps i * κ z ag * cos (θ k z i) := by
    unfold lamR lamF
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
  have hθ : θ k z i - 2 * (z / 2) = θ k z (i - 1) := by
    unfold θ; rw [Nat.cast_sub hi1]; push_cast; ring
  rw [hθ, ← htau] at h
  rw [hlam]
  exact h

section vertex
variable {k : ℕ} (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) {z : ℝ} (ag : ℝ)
  (hc : cos (2 * z) ≠ 0) (hw : sin (z / 2) ≠ 0) (hcw : cos (z / 2) ≠ 0)
include hk hn hc hw hcw

/-- **Equilibrium at an `a`-end** of the first half, with run of rungs `[lo, hi]`. -/
theorem force_L (x : Fin n) (lo hi : ℕ) (hlo : 1 ≤ lo) (hle : lo ≤ hi) (hhi : hi ≤ 8 * k - 2)
    (hinc1 : ∀ i < n - 1, ((Strip.R n k i).1 = x ↔ lo ≤ i ∧ i ≤ hi))
    (hinc2 : ∀ i < n - 1, (Strip.R n k i).2 ≠ x)
    (hsx : sigS k z ag x.val = -tau k z ag hi / ell z)
    (hsx1 : sigS k z ag (x - 1).val = -tau k z ag (lo - 1) / ell z)
    (hvx : Qc n z (x + 1) - Qc n z x = e (θ k z (hi + 1)) - e (θ k z hi))
    (hvx1 : Qc n z (x - 1) - Qc n z x = -(e (θ k z (lo - 1 + 1)) - e (θ k z (lo - 1))))
    (heps : ∑ i ∈ Finset.Icc lo hi, eps i = 0) :
    force k z ag x = 0 := by
  have hn3 : 3 ≤ n := by omega
  unfold force
  rw [side_part hn3 (Qc n z) (fun s => sigS k z ag s.val) x]
  rw [hsx, hsx1, hvx, hvx1]
  rw [sum_fin_Icc (fun i => lamR k z ag i • contrib (Qc n z) (Strip.R n k i) x) lo hi (by omega)]
  swap
  · intro i hiN hout
    have : (Strip.R n k i).1 ≠ x := fun h => by have := (hinc1 i hiN).mp h; omega
    simp only [contrib, this, hinc2 i hiN, if_false, smul_zero]
  have hrung : ∀ i ∈ Finset.Icc lo hi, lamR k z ag i • contrib (Qc n z) (Strip.R n k i) x
      = lamR k z ag i • (-e (θ k z i)) := by
    intro i hi'
    simp only [Finset.mem_Icc] at hi'
    have h1 : (Strip.R n k i).1 = x := (hinc1 i (by omega)).mpr hi'
    simp only [contrib, h1, if_true]
    rw [← h1, rung_e k hk hn z hc i (by omega)]
  rw [Finset.sum_congr rfl hrung]
  -- telescoping
  have hG : ∀ i ∈ Finset.Icc lo hi, lamR k z ag i • (-e (θ k z i))
      = ((eps i * κ z ag, 0) : ℝ × ℝ) + (S (tau k z ag (i - 1)) (θ k z (i - 1)) (z / 2)
          - S (tau k z ag i) (θ k z i) (z / 2)) := by
    intro i hi'
    simp only [Finset.mem_Icc] at hi'
    rw [← rung_G k z ag hw hcw i (by omega) (by omega)]; abel
  rw [Finset.sum_congr rfl hG, Finset.sum_add_distrib]
  have htel := sum_Icc_telescope (fun i => -S (tau k z ag i) (θ k z i) (z / 2)) lo hlo (hi + 1 - lo) hi (by omega)
  simp only [neg_sub_neg] at htel
  rw [show (∑ i ∈ Finset.Icc lo hi, (S (tau k z ag (i - 1)) (θ k z (i - 1)) (z / 2) - S (tau k z ag i) (θ k z i) (z / 2)))
      = S (tau k z ag (lo - 1)) (θ k z (lo - 1)) (z / 2) - S (tau k z ag hi) (θ k z hi) (z / 2) by
      rw [← htel]]
  have hsum : ∑ i ∈ Finset.Icc lo hi, ((eps i * κ z ag, 0) : ℝ × ℝ) = 0 := by
    rw [Prod.ext_iff]
    simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_const_zero, ← Finset.sum_mul, heps, zero_mul]
    exact ⟨rfl, rfl⟩
  rw [hsum, S_side, S_side, Nat.sub_add_cancel hlo]
  simp only [smul_neg, neg_smul]
  abel

/-- **Equilibrium at a `t`-end** of the first half, with run of rungs `[lo, hi]`. -/
theorem force_R (x : Fin n) (lo hi : ℕ) (hlo : 1 ≤ lo) (hle : lo ≤ hi) (hhi : hi ≤ 8 * k - 2)
    (hinc1 : ∀ i < n - 1, ((Strip.R n k i).2 = x ↔ lo ≤ i ∧ i ≤ hi))
    (hinc2 : ∀ i < n - 1, (Strip.R n k i).1 ≠ x)
    (hsx : sigS k z ag x.val = -tau k z ag hi / ell z)
    (hsx1 : sigS k z ag (x - 1).val = -tau k z ag (lo - 1) / ell z)
    (hvx : Qc n z (x + 1) - Qc n z x = -(e (θ k z (hi + 1)) - e (θ k z hi)))
    (hvx1 : Qc n z (x - 1) - Qc n z x = e (θ k z (lo - 1 + 1)) - e (θ k z (lo - 1)))
    (heps : ∑ i ∈ Finset.Icc lo hi, eps i = 0) :
    force k z ag x = 0 := by
  have hn3 : 3 ≤ n := by omega
  unfold force
  rw [side_part hn3 (Qc n z) (fun s => sigS k z ag s.val) x]
  rw [hsx, hsx1, hvx, hvx1]
  rw [sum_fin_Icc (fun i => lamR k z ag i • contrib (Qc n z) (Strip.R n k i) x) lo hi (by omega)]
  swap
  · intro i hiN hout
    have : (Strip.R n k i).2 ≠ x := fun h => by have := (hinc1 i hiN).mp h; omega
    simp only [contrib, this, hinc2 i hiN, if_false, smul_zero]
  have hrung : ∀ i ∈ Finset.Icc lo hi, lamR k z ag i • contrib (Qc n z) (Strip.R n k i) x
      = -(lamR k z ag i • (-e (θ k z i))) := by
    intro i hi'
    simp only [Finset.mem_Icc] at hi'
    have h2 : (Strip.R n k i).2 = x := (hinc1 i (by omega)).mpr hi'
    simp only [contrib, hinc2 i (by omega), h2, if_true, if_false]
    rw [← h2, show Qc n z (Strip.R n k i).1 - Qc n z (Strip.R n k i).2
        = -(Qc n z (Strip.R n k i).2 - Qc n z (Strip.R n k i).1) by abel,
      rung_e k hk hn z hc i (by omega), smul_neg]
  rw [Finset.sum_congr rfl hrung, Finset.sum_neg_distrib]
  have hG : ∀ i ∈ Finset.Icc lo hi, lamR k z ag i • (-e (θ k z i))
      = ((eps i * κ z ag, 0) : ℝ × ℝ) + (S (tau k z ag (i - 1)) (θ k z (i - 1)) (z / 2)
          - S (tau k z ag i) (θ k z i) (z / 2)) := by
    intro i hi'
    simp only [Finset.mem_Icc] at hi'
    rw [← rung_G k z ag hw hcw i (by omega) (by omega)]; abel
  rw [Finset.sum_congr rfl hG, Finset.sum_add_distrib]
  have htel := sum_Icc_telescope (fun i => -S (tau k z ag i) (θ k z i) (z / 2)) lo hlo (hi + 1 - lo) hi (by omega)
  simp only [neg_sub_neg] at htel
  rw [show (∑ i ∈ Finset.Icc lo hi, (S (tau k z ag (i - 1)) (θ k z (i - 1)) (z / 2) - S (tau k z ag i) (θ k z i) (z / 2)))
      = S (tau k z ag (lo - 1)) (θ k z (lo - 1)) (z / 2) - S (tau k z ag hi) (θ k z hi) (z / 2) by
      rw [← htel]]
  have hsum : ∑ i ∈ Finset.Icc lo hi, ((eps i * κ z ag, 0) : ℝ × ℝ) = 0 := by
    rw [Prod.ext_iff]
    simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_const_zero, ← Finset.sum_mul, heps, zero_mul]
    exact ⟨rfl, rfl⟩
  rw [hsum, S_side, S_side, Nat.sub_add_cancel hlo]
  simp only [smul_neg, neg_smul]
  abel

end vertex

end Chiquipoli.Family.Trig.P3
