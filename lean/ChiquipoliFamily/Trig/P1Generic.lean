/-
# Convexity and smallness of a polygon from the angles of its sides

Generic facts, with no reference to the constructor:

* `convex_of_angles`: a closed polygon whose sides are `ℓ e(α_x)`, with `α`
  strictly increasing along the labels and spanning less than `2π`, is
  `ConvexOrdered`. The proof: `cross(q_i, q_{i+1}, q_j)` is `ℓ²` times a partial
  sum of `sin β_m`, where `β` increases in `(0, 2π)` and the full sum vanishes.
  Such partial sums are positive (`partial_sin_pos`).
* `supp_of_cone`: a vertex supports every direction of its normal cone.
* `small_of_antipodal`: if every direction `ψ` has support vertices for `ψ` and
  `ψ + π` at distance `≤ 1`, the polygon is small.
-/
import ChiquipoliFamily.Trig.P3Core
import ChiquipoliLean.Theory.Feasible
import ChiquipoliFamily.Trig.Strip

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig.P1

open Real Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family.Trig.P3

lemma ip_sum_left'' {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ) (y : ℝ × ℝ) :
    ip y (∑ i ∈ s, f i) = ∑ i ∈ s, ip y (f i) := by
  unfold ip
  simp only [Prod.fst_sum, Prod.snd_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-! ## Partial sums of `sin` along an increasing sequence -/

/-- If `β` increases on `[0, N]` from `β 0 = 0` and stays below `2π`, and the
sines sum to `0` over `[0, N]`, then every partial sum over `[0, d)`, `2 ≤ d ≤ N`,
is positive. -/
theorem partial_sin_pos (β : ℕ → ℝ) (N : ℕ) (h0 : β 0 = 0)
    (hmono : ∀ i j, i < j → j ≤ N → β i < β j) (htop : β N < 2 * π)
    (hsum : ∑ m ∈ Finset.range (N + 1), sin (β m) = 0) (d : ℕ) (hd1 : 2 ≤ d) (hd2 : d ≤ N) :
    0 < ∑ m ∈ Finset.range d, sin (β m) := by
  have hpos : ∀ m, 1 ≤ m → m ≤ N → 0 < β m := fun m h1 h2 => h0 ▸ hmono 0 m (by omega) h2
  rcases lt_or_ge (β (d - 1)) π with hlt | hge
  · -- every term of the partial sum is `≥ 0`, and the term `m = 1` is `> 0`
    have e : d = (d - 1) + 1 := by omega
    rw [e, Finset.sum_range_succ', h0, sin_zero, add_zero]
    have hterm : ∀ m ∈ Finset.range (d - 1), 0 < sin (β (m + 1)) := by
      intro m hm
      rw [Finset.mem_range] at hm
      apply sin_pos_of_pos_of_lt_pi (hpos _ (by omega) (by omega))
      rcases eq_or_lt_of_le (show m + 1 ≤ d - 1 by omega) with h | h
      · rw [h]; exact hlt
      · exact lt_trans (hmono _ _ h (by omega)) hlt
    exact Finset.sum_pos hterm ⟨0, by simp; omega⟩
  · -- the rest of the sum is `< 0`
    have hsplit := Finset.sum_range_add_sum_Ico (fun m => sin (β m)) (show d ≤ N + 1 by omega)
    rw [hsum] at hsplit
    have hrest : ∑ m ∈ Finset.Ico d (N + 1), sin (β m) < 0 := by
      apply Finset.sum_neg
      · intro m hm
        rw [Finset.mem_Ico] at hm
        have h1 : π < β m := lt_of_le_of_lt hge (hmono _ _ (by omega) (by omega))
        have h2 : β m < 2 * π := by
          rcases eq_or_lt_of_le (show m ≤ N by omega) with h | h
          · rw [h]; exact htop
          · exact lt_trans (hmono _ _ h le_rfl) htop
        have := sin_pos_of_pos_of_lt_pi (show 0 < β m - π by linarith) (by linarith)
        rw [sin_sub_pi] at this; linarith
      · exact ⟨d, by simp; omega⟩
    linarith

/-! ## Convexity -/

lemma ip_J_e (a b : ℝ) : ip (J (e a)) (e b) = sin (b - a) := by
  simp only [ip, J, e, sin_sub]; ring

section conv
variable {n : ℕ} [NeZero n] (q : Cfg n) (ℓ : ℝ) (α : ℕ → ℝ)
  (hs : ∀ x : Fin n, q (x + 1) - q x = ℓ • e (α x.val))
include hs

/-- `q_{i+d} − q_i` is the sum of the sides in between. -/
lemma telescope (i : Fin n) (d : ℕ) :
    q (Strip.ver n (i.val + d)) - q i = ∑ m ∈ Finset.range d, ℓ • e (α ((i.val + m) % n)) := by
  induction d with
  | zero => simp [Strip.ver_val]
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih, show i.val + (d + 1) = i.val + d + 1 by ring, ← Strip.ver_succ]
    have := hs (Strip.ver n (i.val + d))
    rw [show (Strip.ver n (i.val + d)).val = (i.val + d) % n from rfl] at this
    rw [← this]; abel

/-- **Convexity from the angles of the sides.** -/
theorem convex_of_angles (hn : 3 ≤ n) (hℓ : 0 < ℓ) (hmono : ∀ i j, i < j → j < n → α i < α j)
    (hspan : α (n - 1) < α 0 + 2 * π) : ConvexOrdered q := by
  intro i j hji hji1
  have hi := i.isLt
  -- the angles seen from side `i`
  set β : ℕ → ℝ := fun m => α ((i.val + m) % n) - α i.val + (if i.val + m < n then 0 else 2 * π) with hβ
  have hsinβ : ∀ m, sin (β m) = sin (α ((i.val + m) % n) - α i.val) := by
    intro m; simp only [hβ]; split_ifs
    · rw [add_zero]
    · rw [sin_add_two_pi]
  have hβ0 : β 0 = 0 := by simp only [hβ, add_zero, Nat.mod_eq_of_lt hi, sub_self, if_pos hi]
  have hβmono : ∀ a b, a < b → b ≤ n - 1 → β a < β b := by
    intro a b hab hb
    simp only [hβ]
    by_cases h1 : i.val + b < n
    · have e1 : (i.val + b) % n = i.val + b := Nat.mod_eq_of_lt h1
      have e2 : (i.val + a) % n = i.val + a := Nat.mod_eq_of_lt (by omega)
      rw [if_pos h1, if_pos (by omega), e1, e2]
      have := hmono _ _ (show i.val + a < i.val + b by omega) h1; linarith
    · have e1 : (i.val + b) % n = i.val + b - n := by rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [if_neg h1, e1]
      by_cases h2 : i.val + a < n
      · have e2 : (i.val + a) % n = i.val + a := Nat.mod_eq_of_lt h2
        rw [if_pos h2, e2]
        have hA : α (i.val + a) ≤ α (n - 1) := by
          rcases eq_or_lt_of_le (show i.val + a ≤ n - 1 by omega) with h | h
          · rw [h]
          · exact (hmono _ _ h (by omega)).le
        have hB : α 0 ≤ α (i.val + b - n) := by
          rcases Nat.eq_zero_or_pos (i.val + b - n) with h | h
          · rw [h]
          · exact (hmono _ _ h (by omega)).le
        linarith
      · have e2 : (i.val + a) % n = i.val + a - n := by rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [if_neg h2, e2]
        have := hmono _ _ (show i.val + a - n < i.val + b - n by omega) (by omega); linarith
  have hβtop : β (n - 1) < 2 * π := by
    simp only [hβ]
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · rw [h0, zero_add, if_pos (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [add_zero]; linarith
    · rw [if_neg (by omega), Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have := hmono (i.val + (n - 1) - n) i.val (by omega) hi; linarith
  -- the sum over all sides vanishes
  have hcross : ∀ d, ip (J (q (i + 1) - q i)) (q (Strip.ver n (i.val + d)) - q i)
      = ℓ ^ 2 * ∑ m ∈ Finset.range d, sin (β m) := by
    intro d
    rw [telescope q ℓ α hs i d, hs i]
    simp only [ip_sum_left'', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hsinβ, ← ip_J_e]
    simp only [ip, J, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have htot : ∑ m ∈ Finset.range (n - 1 + 1), sin (β m) = 0 := by
    have h := hcross n
    rw [Nat.sub_add_cancel (by omega)]
    have hv : Strip.ver n (i.val + n) = i := by
      apply Fin.ext; simp only [Strip.ver]; rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    rw [hv, sub_self] at h
    simp only [ip, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] at h
    have hl2 : ℓ ^ 2 ≠ 0 := by positivity
    exact (mul_eq_zero.mp h.symm).resolve_left hl2
  -- `j = i + d` with `2 ≤ d ≤ n − 1`
  -- `j = i + d` with `2 ≤ d ≤ n − 1`
  obtain ⟨d, hd⟩ : ∃ d, d = (j.val + n - i.val) % n := ⟨_, rfl⟩
  have hdn : d < n := by rw [hd]; exact Nat.mod_lt _ (by omega)
  have hjd : j = Strip.ver n (i.val + d) := by
    have hj := j.isLt
    apply Fin.ext
    show j.val = (i.val + d) % n
    rcases Nat.lt_or_ge j.val i.val with h | h
    · have hd' : d = j.val + n - i.val := by rw [hd, Nat.mod_eq_of_lt (by omega)]
      rw [hd', show i.val + (j.val + n - i.val) = j.val + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    · have hd' : d = j.val - i.val := by
        rw [hd, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      rw [hd', show i.val + (j.val - i.val) = j.val by omega, Nat.mod_eq_of_lt hj]
  have hd0 : d ≠ 0 := by
    intro h; apply hji; rw [hjd, h, add_zero, Strip.ver_val]
  have hd1 : d ≠ 1 := by
    intro h; apply hji1; rw [hjd, h, ← Strip.ver_succ, Strip.ver_val]
  have := partial_sin_pos β (n - 1) hβ0 hβmono hβtop htot d (by omega) (by omega)
  unfold cross
  rw [hjd, hcross d]
  positivity

end conv

/-! ## Support and smallness -/

/-- `x` supports the direction `v`: no vertex goes further than `q_x` along `v`. -/
def Supp {n : ℕ} (q : Cfg n) (x : Fin n) (v : ℝ × ℝ) : Prop := ∀ m, ip (q m - q x) v ≤ 0

/-- `cross(a, b, c) = −ℓ ⟨c − a, e(α − π/2)⟩` when `b − a = ℓ e(α)`. -/
lemma cross_side (a b c : ℝ × ℝ) (ℓ α : ℝ) (h : b - a = ℓ • e α) :
    cross a b c = -(ℓ * ip (c - a) (e (α - π / 2))) := by
  unfold cross; rw [h]
  simp only [ip, J, e, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, cos_sub_pi_div_two, sin_sub_pi_div_two]
  ring

/-- The two sides at `x` support their outward normals; hence so does every
direction in between. -/
theorem supp_of_cone {n : ℕ} [NeZero n] (q : Cfg n) (hconv : ConvexOrdered q) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x : Fin n) (a1 a2 : ℝ) (he1 : q x - q (x - 1) = ℓ • e a1) (he2 : q (x + 1) - q x = ℓ • e a2)
    (h12 : 0 < a2 - a1) (h12' : a2 - a1 < π) (ψ : ℝ) (hψ1 : a1 - π / 2 ≤ ψ) (hψ2 : ψ ≤ a2 - π / 2) :
    Supp q x (e ψ) := by
  have hS2 : ∀ m, ip (q m - q x) (e (a2 - π / 2)) ≤ 0 := by
    intro m
    have hc : 0 ≤ cross (q x) (q (x + 1)) (q m) := by
      by_cases h1 : m = x
      · subst h1; simp [cross, ip]
      by_cases h2 : m = x + 1
      · subst h2; rw [cross_side _ _ _ ℓ a2 he2, he2]
        simp [ip, e, cos_sub_pi_div_two, sin_sub_pi_div_two]; ring_nf; exact le_refl _
      exact (hconv x m h1 h2).le
    rw [cross_side _ _ _ ℓ a2 he2] at hc
    nlinarith
  have hS1 : ∀ m, ip (q m - q x) (e (a1 - π / 2)) ≤ 0 := by
    intro m
    have hc : 0 ≤ cross (q (x - 1)) (q x) (q m) := by
      by_cases h1 : m = x - 1
      · subst h1; simp [cross, ip]
      by_cases h2 : m = x
      · subst h2; rw [cross_side _ _ _ ℓ a1 he1, he1]
        simp [ip, e, cos_sub_pi_div_two, sin_sub_pi_div_two]; ring_nf; exact le_refl _
      have := hconv (x - 1) m h1 (by rw [sub_add_cancel]; exact h2)
      rw [sub_add_cancel] at this; exact this.le
    rw [cross_side _ _ _ ℓ a1 he1] at hc
    have h0 : ip (q x - q (x - 1)) (e (a1 - π / 2)) = 0 := by
      rw [he1]; simp [ip, e, cos_sub_pi_div_two, sin_sub_pi_div_two]; ring
    have hsplit : ip (q m - q x) (e (a1 - π / 2))
        = ip (q m - q (x - 1)) (e (a1 - π / 2)) - ip (q x - q (x - 1)) (e (a1 - π / 2)) := by
      simp only [ip, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hsplit, h0]
    nlinarith
  set ν1 := a1 - π / 2 with hν1
  set ν2 := a2 - π / 2 with hν2
  have hd : ν2 - ν1 = a2 - a1 := by rw [hν1, hν2]; ring
  have hsd : 0 < sin (ν2 - ν1) := by rw [hd]; exact sin_pos_of_pos_of_lt_pi h12 h12'
  have c1 : 0 ≤ sin (ν2 - ψ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have c2 : 0 ≤ sin (ψ - ν1) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  intro m
  have h1 := hS1 m
  have h2 := hS2 m
  have hid : sin (ν2 - ν1) * ip (q m - q x) (e ψ)
      = sin (ν2 - ψ) * ip (q m - q x) (e ν1) + sin (ψ - ν1) * ip (q m - q x) (e ν2) := by
    simp only [ip, e, sin_sub]; ring
  have : sin (ν2 - ν1) * ip (q m - q x) (e ψ) ≤ 0 := by
    rw [hid]; nlinarith [mul_nonneg c1 (neg_nonneg.mpr h1), mul_nonneg c2 (neg_nonneg.mpr h2)]
  by_contra hcon
  push Not at hcon
  have := mul_pos hsd hcon
  linarith

/-- **Small from antipodal support pairs.** -/
theorem small_of_antipodal {n : ℕ} (q : Cfg n)
    (hanti : ∀ ψ : ℝ, ∃ x y : Fin n, Supp q x (e ψ) ∧ Supp q y (e (ψ + π)) ∧ nsq (q x - q y) ≤ 1) :
    Small q := by
  intro i j
  unfold dC
  set v := q j - q i with hvdef
  by_cases hv : v = 0
  · rw [hv]; simp [nsq, ip]
  set w : ℂ := ⟨v.1, v.2⟩ with hwdef
  have hw : w ≠ 0 := by
    intro h; apply hv
    have h1 : w.re = 0 := by rw [h]; rfl
    have h2 : w.im = 0 := by rw [h]; rfl
    exact Prod.ext h1 h2
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hr2 : ‖w‖ ^ 2 = nsq v := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [nsq, ip, hwdef]
  set ψ := Complex.arg w
  have hc : cos ψ = v.1 / ‖w‖ := Complex.cos_arg hw
  have hs : sin ψ = v.2 / ‖w‖ := Complex.sin_arg w
  have hvψ : ip v (e ψ) = ‖w‖ := by
    have hsq : v.1 ^ 2 + v.2 ^ 2 = ‖w‖ ^ 2 := by rw [hr2]; simp only [nsq, ip]; ring
    simp only [ip, e, hc, hs]; field_simp; linarith
  obtain ⟨x, y, hx, hy, hxy⟩ := hanti ψ
  have h1 := hx j
  have h2 := hy i
  have eπ : e (ψ + π) = -e ψ := by simp [e, cos_add_pi, sin_add_pi]
  rw [eπ] at h2
  have hsplit : ip v (e ψ) = ip (q j - q x) (e ψ) + ip (q x - q y) (e ψ) + ip (q i - q y) (-e ψ) := by
    simp only [hvdef, ip, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]; ring
  -- Cauchy–Schwarz: `⟨u, e ψ⟩ ≤ |u| ≤ 1`
  have hcs : ip (q x - q y) (e ψ) ≤ 1 := by
    have hu : ip (q x - q y) (e ψ) ^ 2 ≤ nsq (q x - q y) := by
      simp only [ip, nsq, e]
      nlinarith [sq_nonneg ((q x - q y).1 * sin ψ - (q x - q y).2 * cos ψ), sin_sq_add_cos_sq ψ]
    nlinarith
  have : ‖w‖ ≤ 1 := by linarith
  nlinarith

end Chiquipoli.Family.Trig.P1
