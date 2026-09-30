/-
# Problem 3: the multipliers are positive, for every `n = 16k ≥ 32`

With `w = z/2`, `s = sin w`, `c = cos w`, `ℓ = 2s` and `κ = 2a/ℓ`:
* `φ ∈ (z, 0.16]` and `θ_j = φ + jz ∈ (z, π/2]` for `j ≤ 8k − 1` (`phi_facts`);
* `τ₀ c ≥ cos(3z/2)` and `0 < κ ≤ 2s` (`tau0_ge`, `kappa_facts`);
* `τ_j ≥ τ₀ − (κ/c) z T(j)`, where `T(j)` counts the `t`-steps before `j`
  (`tau_lower`); hence `τ_j > 0`;
* `λ_j > 0` (`lamF_pos`). The only delicate case is a switch `a → t`, which
  reduces to `cos(3z/2) − cos((j + 3/2)z) > j z sin(z/2)`, proved by Jordan's
  inequality.
-/
import ChiquipoliFamily.AllN.Multipliers.Gap

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Chiquipoli.Family.Trig.P3

open Real Set Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.Layout Chiquipoli.Family.Trig.ConstructorAll Chiquipoli.Family.Trig.RungVec

/-- The number of `t`-steps among `0, …, j − 1`. -/
def Tc (j : ℕ) : ℕ :=
  4 * (j / 8) + (if j % 8 ≤ 2 then 0 else if j % 8 ≤ 4 then 1 else if j % 8 = 5 then 2 else 3)

section pos
variable {k : ℕ} (hk : 2 ≤ k) {z : ℝ} (hz0 : 0 < z) (hzn : z < π / (16 * k : ℕ))
  (hloc : π / (((16 * k : ℕ) : ℝ) - 2 + π) ≤ z) (ag : ℝ) (hag0 : 0 < ag) (hag : ag ≤ 2 * sin (z / 2) ^ 2)
include hk hz0 hzn hloc hag0 hag

lemma z_small : z < 0.0982 ∧ 16 * (k : ℝ) * z < π := by
  have hK : (32 : ℝ) ≤ ((16 * k : ℕ) : ℝ) := by
    push_cast; have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hpi := pi_pos
  have h1 : π / ((16 * k : ℕ) : ℝ) ≤ π / 32 := div_le_div_of_nonneg_left hpi.le (by norm_num) hK
  have hpi4 : π < 3.1416 := pi_lt_d4
  constructor
  · linarith
  · have := hzn; rw [lt_div_iff₀ (by linarith)] at this; push_cast at this; linarith

/-- `φ ∈ (z, 0.16]`. -/
lemma phi_facts : z < φ k z ∧ φ k z ≤ 0.16 := by
  obtain ⟨h1, h2⟩ := z_small hk hz0 hzn hloc ag hag0 hag
  have hpi := pi_pos
  have hpi3 := pi_gt_three
  have hpi4 : π < 3.1416 := pi_lt_d4
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold φ
  constructor
  · nlinarith
  · -- `(8k − 1) z ≥ (8k − 1) π / (16k − 2 + π)`
    push_cast at hloc
    rw [div_le_iff₀ (by linarith)] at hloc
    nlinarith

lemma ag_small : ag ≤ 0.005 := by
  obtain ⟨h1, -⟩ := z_small hk hz0 hzn hloc ag hag0 hag
  have := sin_le (show 0 ≤ z / 2 by linarith)
  have := (sin_pos_of_pos_of_lt_pi (show 0 < z / 2 by linarith) (by linarith [pi_gt_three])).le
  nlinarith

/-- `τ₀ cos(z/2) ≥ cos(3z/2)`. -/
lemma tau0_ge : cos (3 * z / 2) ≤ tau k z ag 0 * cos (z / 2) := by
  obtain ⟨hz1, -⟩ := z_small hk hz0 hzn hloc ag hag0 hag
  obtain ⟨hp1, hp2⟩ := phi_facts hk hz0 hzn hloc ag hag0 hag
  have ha := ag_small hk hz0 hzn hloc ag hag0 hag
  set φ' := φ k z
  have hpi3 := pi_gt_three
  -- `sin z (cos z − a) ≤ sin φ (cos φ − a)`
  have hmono : sin z * (cos z - ag) ≤ sin φ' * (cos φ' - ag) := by
    set d := φ' - z with hd
    have hd0 : 0 < d := by linarith
    have e1 : sin φ' * cos φ' - sin z * cos z = 2 * sin (d / 2) * cos (d / 2) * cos (φ' + z) := by
      have h1 : sin φ' * cos φ' - sin z * cos z = (sin (2 * φ') - sin (2 * z)) / 2 := by
        rw [sin_two_mul, sin_two_mul]; ring
      rw [h1, sin_sub_sin, show (2 * φ' - 2 * z) / 2 = d by ring, show (2 * φ' + 2 * z) / 2 = φ' + z by ring,
        show sin d = sin (2 * (d / 2)) by ring_nf, sin_two_mul]
      ring
    have e2 : sin φ' - sin z = 2 * sin (d / 2) * cos ((φ' + z) / 2) := by
      rw [sin_sub_sin]
    have hs : 0 ≤ sin (d / 2) := (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le
    have hcd : 0.99 ≤ cos (d / 2) := by
      have := one_sub_sq_div_two_le_cos (x := d / 2); nlinarith
    have hcs : 0.96 ≤ cos (φ' + z) := by
      have := one_sub_sq_div_two_le_cos (x := φ' + z); nlinarith
    have hcs2 := cos_le_one ((φ' + z) / 2)
    have : 0 ≤ 2 * sin (d / 2) * (cos (d / 2) * cos (φ' + z) - ag * cos ((φ' + z) / 2)) := by
      apply mul_nonneg (by linarith)
      nlinarith
    nlinarith
  have hsz : 0 < sin z := sin_pos_of_pos_of_lt_pi hz0 (by linarith)
  have hcz : cos z - ag ≥ 2 * cos z - 1 := by
    have h := sq_two_sin_half' z
    nlinarith
  have hτ : 2 * cos z - 1 ≤ tau k z ag 0 := by
    show 2 * cos z - 1 ≤ sin φ' * (cos φ' - ag) / sin z
    rw [le_div_iff₀ hsz]; nlinarith
  have hc : 0 < cos (z / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have e3 : cos (3 * z / 2) = (2 * cos z - 1) * cos (z / 2) := by
    have h1 : cos (3 * z / 2) = cos (3 * (z / 2)) := by ring_nf
    have h2 : cos z = cos (2 * (z / 2)) := by ring_nf
    rw [h1, h2, cos_three_mul, cos_two_mul]; ring
  rw [e3]
  exact mul_le_mul_of_nonneg_right hτ hc.le

/-- `0 < κ ≤ 2 sin(z/2)`. -/
lemma kappa_facts : 0 < κ z ag ∧ κ z ag ≤ 2 * sin (z / 2) := by
  obtain ⟨hz1, -⟩ := z_small hk hz0 hzn hloc ag hag0 hag
  have hs : 0 < sin (z / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_gt_three])
  unfold κ ell
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity)]; nlinarith

lemma theta_facts (j : ℕ) (hj : j ≤ 8 * k - 1) : 0 < θ k z j ∧ θ k z j ≤ π / 2 := by
  obtain ⟨hp1, -⟩ := phi_facts hk hz0 hzn hloc ag hag0 hag
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ 8 * k - 1 := by
    have : (j : ℝ) ≤ ((8 * k - 1 : ℕ) : ℝ) := by exact_mod_cast hj
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  unfold θ φ
  constructor
  · unfold φ at hp1; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  · nlinarith

lemma tau_succ (i : ℕ) (hi : 1 ≤ i) :
    tau k z ag i = tau k z ag (i - 1) + eps i * κ z ag * sin (θ k z i) / cos (z / 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [tau, Nat.add_sub_cancel]

/-- **The lower bound on `τ`.** -/
theorem tau_lower : ∀ j, j ≤ 8 * k - 2 →
    tau k z ag 0 - κ z ag / cos (z / 2) * z * (Tc j : ℝ) ≤ tau k z ag j := by
  obtain ⟨hz1, -⟩ := z_small hk hz0 hzn hloc ag hag0 hag
  obtain ⟨hκ0, hκ1⟩ := kappa_facts hk hz0 hzn hloc ag hag0 hag
  have hc : 0 < cos (z / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩
  set K := κ z ag / cos (z / 2) with hKdef
  have hK0 : 0 ≤ K := (div_pos hκ0 hc).le
  have hsin : ∀ i, i ≤ 8 * k - 1 → 0 ≤ κ z ag * sin (θ k z i) / cos (z / 2) := by
    intro i hi
    have := theta_facts hk hz0 hzn hloc ag hag0 hag i hi
    have : 0 ≤ sin (θ k z i) := sin_nonneg_of_nonneg_of_le_pi this.1.le (by linarith [this.2, pi_pos])
    positivity
  have hlip : ∀ a b : ℕ, a ≤ b →
      -(K * z * ((b : ℝ) - a)) ≤ κ z ag * sin (θ k z a) / cos (z / 2) - κ z ag * sin (θ k z b) / cos (z / 2) := by
    intro a b hab
    have h := abs_sin_sub_sin_le (θ k z a) (θ k z b)
    have e : θ k z a - θ k z b = -(((b : ℝ) - a) * z) := by unfold θ; ring
    have hba : (0 : ℝ) ≤ ((b : ℝ) - a) * z := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      exact mul_nonneg (by linarith) hz0.le
    rw [e, abs_neg, abs_of_nonneg hba] at h
    have h' := (abs_le.mp h).1
    rw [show κ z ag * sin (θ k z a) / cos (z / 2) - κ z ag * sin (θ k z b) / cos (z / 2)
        = K * (sin (θ k z a) - sin (θ k z b)) by rw [hKdef]; ring]
    have : -(((b : ℝ) - a) * z) * K ≤ (sin (θ k z a) - sin (θ k z b)) * K := mul_le_mul_of_nonneg_right h' hK0
    nlinarith
  have Tmono : ∀ j, 1 ≤ j → Tc (j - 1) ≤ Tc j := by
    intro j hj; unfold Tc; split_ifs <;> omega
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simp [Tc]
    have hrec := tau_succ hk hz0 hzn hloc ag hag0 hag j hpos
    rw [eps_val j hpos] at hrec
    have hr := Nat.mod_lt j (show 8 > 0 by norm_num)
    by_cases hA : j % 8 = 2 ∨ j % 8 = 4 ∨ j % 8 = 7
    · -- `a → t`: τ goes up
      rw [if_pos hA] at hrec
      have := ih (j - 1) (by omega) (by omega)
      have hT : ((Tc (j - 1) : ℕ) : ℝ) ≤ (Tc j : ℝ) := by exact_mod_cast Tmono j hpos
      have := hsin j (by omega)
      rw [one_mul] at hrec
      nlinarith [mul_le_mul_of_nonneg_left hT (mul_nonneg hK0 hz0.le)]
    rw [if_neg hA] at hrec
    by_cases hB : j % 8 = 0 ∨ j % 8 = 3 ∨ j % 8 = 6
    · rw [if_pos hB] at hrec
      rcases hB with hB | hB | hB
      · -- `j ≡ 0`: back over one `t`-step
        have h1 : 2 ≤ j := by omega
        have hrec' := tau_succ hk hz0 hzn hloc ag hag0 hag (j - 1) (by omega)
        rw [eps_val (j - 1) (by omega), if_pos (by omega), one_mul, show j - 1 - 1 = j - 2 by omega] at hrec'
        have ihj := ih (j - 2) (by omega) (by omega)
        have hT : Tc j = Tc (j - 2) + 1 := by unfold Tc; split_ifs <;> omega
        have hl := hlip (j - 1) j (by omega)
        rw [show ((j : ℝ) - ((j - 1 : ℕ) : ℝ)) = 1 by rw [Nat.cast_sub (by omega)]; push_cast; ring] at hl
        rw [hT]; push_cast
        have e1 : -1 * κ z ag * sin (θ k z j) / cos (z / 2) = -(κ z ag * sin (θ k z j) / cos (z / 2)) := by ring
        rw [e1] at hrec
        linarith
      · -- `j ≡ 3`: back over one `t`-step
        have hrec' := tau_succ hk hz0 hzn hloc ag hag0 hag (j - 1) (by omega)
        rw [eps_val (j - 1) (by omega), if_pos (by omega), one_mul, show j - 1 - 1 = j - 2 by omega] at hrec'
        have ihj := ih (j - 2) (by omega) (by omega)
        have hT : Tc j = Tc (j - 2) + 1 := by unfold Tc; split_ifs <;> omega
        have hl := hlip (j - 1) j (by omega)
        rw [show ((j : ℝ) - ((j - 1 : ℕ) : ℝ)) = 1 by rw [Nat.cast_sub (by omega)]; push_cast; ring] at hl
        rw [hT]; push_cast
        have e1 : -1 * κ z ag * sin (θ k z j) / cos (z / 2) = -(κ z ag * sin (θ k z j) / cos (z / 2)) := by ring
        rw [e1] at hrec
        linarith
      · -- `j ≡ 6`: back over two `t`-steps
        have hrec1 := tau_succ hk hz0 hzn hloc ag hag0 hag (j - 1) (by omega)
        rw [eps_val (j - 1) (by omega), if_neg (by omega), if_neg (by omega), zero_mul, zero_mul, zero_div,
          add_zero, show j - 1 - 1 = j - 2 by omega] at hrec1
        have hrec2 := tau_succ hk hz0 hzn hloc ag hag0 hag (j - 2) (by omega)
        rw [eps_val (j - 2) (by omega), if_pos (by omega), one_mul, show j - 2 - 1 = j - 3 by omega] at hrec2
        have ihj := ih (j - 3) (by omega) (by omega)
        have hT : Tc j = Tc (j - 3) + 2 := by unfold Tc; split_ifs <;> omega
        have hl := hlip (j - 2) j (by omega)
        rw [show ((j : ℝ) - ((j - 2 : ℕ) : ℝ)) = 2 by rw [Nat.cast_sub (by omega)]; push_cast; ring] at hl
        rw [hT]; push_cast
        have e1 : -1 * κ z ag * sin (θ k z j) / cos (z / 2) = -(κ z ag * sin (θ k z j) / cos (z / 2)) := by ring
        rw [e1] at hrec
        linarith
    · -- no switch: τ stays
      rw [if_neg hB, zero_mul, zero_mul, zero_div, add_zero] at hrec
      have := ih (j - 1) (by omega) (by omega)
      have hT : ((Tc (j - 1) : ℕ) : ℝ) ≤ (Tc j : ℝ) := by exact_mod_cast Tmono j hpos
      rw [hrec]
      nlinarith [mul_le_mul_of_nonneg_left hT (mul_nonneg hK0 hz0.le)]

lemma Tc_le (j : ℕ) (hj : j ≤ 8 * k - 2) : Tc j ≤ 4 * k := by
  unfold Tc; split_ifs <;> omega

/-- **`τ_j > 0`** along the first half. -/
theorem tau_pos (j : ℕ) (hj : j ≤ 8 * k - 2) : 0 < tau k z ag j := by
  obtain ⟨hz1, hkz⟩ := z_small hk hz0 hzn hloc ag hag0 hag
  obtain ⟨hκ0, hκ1⟩ := kappa_facts hk hz0 hzn hloc ag hag0 hag
  have hpi3 := pi_gt_three
  have hpi4 : π < 3.1416 := pi_lt_d4
  have hc : 0 < cos (z / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hlow := tau_lower hk hz0 hzn hloc ag hag0 hag j hj
  have h0 := tau0_ge hk hz0 hzn hloc ag hag0 hag
  have hT : (Tc j : ℝ) ≤ 4 * k := by exact_mod_cast Tc_le hk hz0 hzn hloc ag hag0 hag j hj
  have hT0 : (0 : ℝ) ≤ Tc j := Nat.cast_nonneg _
  have hs := sin_le (show 0 ≤ z / 2 by linarith)
  have hs0 := (sin_pos_of_pos_of_lt_pi (show 0 < z / 2 by linarith) (by linarith)).le
  have h3 : 0.98 ≤ cos (3 * z / 2) := by
    have := one_sub_sq_div_two_le_cos (x := 3 * z / 2); nlinarith
  -- `τ_j c ≥ cos(3z/2) − κ z T ≥ 0.98 − 2 s · π/4 > 0`
  have hmul : tau k z ag j * cos (z / 2) ≥ cos (3 * z / 2) - κ z ag * z * Tc j := by
    have := mul_le_mul_of_nonneg_right hlow hc.le
    have e : (tau k z ag 0 - κ z ag / cos (z / 2) * z * (Tc j : ℝ)) * cos (z / 2)
        = tau k z ag 0 * cos (z / 2) - κ z ag * z * Tc j := by field_simp
    linarith
  have hzT : z * (Tc j : ℝ) ≤ 0.8 := by
    have : z * (Tc j : ℝ) ≤ z * (4 * k) := mul_le_mul_of_nonneg_left hT hz0.le
    nlinarith
  have hkT : κ z ag * z * (Tc j : ℝ) ≤ 2 * sin (z / 2) * 0.8 := by
    rw [mul_assoc]
    exact mul_le_mul hκ1 hzT (by positivity) (by positivity)
  have : 0 < tau k z ag j * cos (z / 2) := by nlinarith
  exact pos_of_mul_pos_left this hc.le

/-- The key inequality at a switch `a → t`. -/
lemma switch_ineq (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ 8 * k - 2) :
    sin (z / 2) * z * j < cos (3 * z / 2) - cos ((j + 3 / 2) * z) := by
  obtain ⟨hz1, hkz⟩ := z_small hk hz0 hzn hloc ag hag0 hag
  have hpi := pi_pos
  have hpi4 : π < 3.1416 := pi_lt_d4
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjk : (j : ℝ) ≤ 8 * k - 2 := by
    have : (j : ℝ) ≤ ((8 * k - 2 : ℕ) : ℝ) := by exact_mod_cast hj
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  rw [cos_sub_cos, show (3 * z / 2 + (j + 3 / 2) * z) / 2 = (j + 3) * z / 2 by ring,
    show (3 * z / 2 - (j + 3 / 2) * z) / 2 = -(j * z / 2) by ring, sin_neg]
  have hA : (j + 3) * z / 2 ≤ π / 2 := by nlinarith
  have j1 := mul_le_sin (show 0 ≤ (j + 3) * z / 2 by positivity) hA
  have j2 := mul_le_sin (show 0 ≤ j * z / 2 by positivity) (by nlinarith)
  have hs := sin_le (show 0 ≤ z / 2 by linarith)
  have hs0 := (sin_pos_of_pos_of_lt_pi (show 0 < z / 2 by linarith) (by linarith [pi_gt_three])).le
  -- `2 sin((j+3)z/2) sin(jz/2) ≥ 2 (j+3) j z² / π²  >  j z² / 2 ≥ s z j`
  have p1 : 0 ≤ 2 / π * ((j + 3) * z / 2) := by positivity
  have p2 : 0 ≤ 2 / π * (j * z / 2) := by positivity
  have hprod := mul_le_mul j1 j2 p2 (le_trans p1 j1)
  have e : 2 / π * ((j + 3) * z / 2) * (2 / π * (j * z / 2)) = (j + 3) * j * z ^ 2 / π ^ 2 := by
    field_simp
  rw [e] at hprod
  have hpi2 : π ^ 2 < 9.87 := by nlinarith
  have hbig : (j : ℝ) * z ^ 2 / 2 < 2 * ((j + 3) * j * z ^ 2 / π ^ 2) := by
    have hz2 : 0 < (j : ℝ) * z ^ 2 := by positivity
    rw [show 2 * ((j + 3) * j * z ^ 2 / π ^ 2) = (j * z ^ 2) * (2 * (j + 3) / π ^ 2) by ring]
    have : 1 / 2 < 2 * ((j : ℝ) + 3) / π ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hsz : sin (z / 2) * z * j ≤ (j : ℝ) * z ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_right hs (show 0 ≤ z * (j : ℝ) by positivity)
    nlinarith
  linarith

/-- **`λ_j > 0`** on the first half. -/
theorem lamF_pos (j : ℕ) (hj : j ≤ 8 * k - 1) : 0 < lamF k z ag j := by
  obtain ⟨hz1, hkz⟩ := z_small hk hz0 hzn hloc ag hag0 hag
  obtain ⟨hκ0, hκ1⟩ := kappa_facts hk hz0 hzn hloc ag hag0 hag
  obtain ⟨hp1, hp2⟩ := phi_facts hk hz0 hzn hloc ag hag0 hag
  have hpi3 := pi_gt_three
  have hc : 0 < cos (z / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin (z / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hℓ : 0 < ell z := by unfold ell; linarith
  unfold lamF
  split_ifs with h0 h8
  · -- `j = 0`
    have ht0 := tau_pos hk hz0 hzn hloc ag hag0 hag 0 (by omega)
    have hcp : 0 < cos (φ k z) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have : 0 ≤ ag * cos (φ k z) + sin (φ k z) ^ 2 := by positivity
    positivity
  · -- `j = 8k − 1`
    have := tau_pos hk hz0 hzn hloc ag hag0 hag (8 * k - 2) le_rfl
    positivity
  · have hj1 : 1 ≤ j := by omega
    have hj2 : j ≤ 8 * k - 2 := by omega
    have ta := tau_pos hk hz0 hzn hloc ag hag0 hag (j - 1) (by omega)
    have tb := tau_pos hk hz0 hzn hloc ag hag0 hag j hj2
    have hθ := theta_facts hk hz0 hzn hloc ag hag0 hag j (by omega)
    have hcθ : 0 ≤ cos (θ k z j) := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩
    rw [eps_val j hj1]
    split_ifs with hA hB
    · -- a switch `a → t`
      have hrec := tau_succ hk hz0 hzn hloc ag hag0 hag j hj1
      rw [eps_val j hj1, if_pos hA, one_mul] at hrec
      have hlow := tau_lower hk hz0 hzn hloc ag hag0 hag (j - 1) (by omega)
      have h0' := tau0_ge hk hz0 hzn hloc ag hag0 hag
      have hT : 2 * (Tc (j - 1) : ℝ) ≤ j := by
        have : 2 * Tc (j - 1) ≤ j := by unfold Tc; split_ifs <;> omega
        exact_mod_cast this
      have hT0 : (0 : ℝ) ≤ Tc (j - 1) := Nat.cast_nonneg _
      have hkey := switch_ineq hk hz0 hzn hloc ag hag0 hag j hj1 hj2
      have hjk : (j : ℝ) ≤ 8 * k - 2 := by
        have : (j : ℝ) ≤ ((8 * k - 2 : ℕ) : ℝ) := by exact_mod_cast hj2
        rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
      -- `cos(θ_j + z/2) ≤ cos((j + 3/2) z)`, both in `[0, π]`
      have hθlow : ((j : ℝ) + 3 / 2) * z ≤ θ k z j + z / 2 := by unfold θ; nlinarith
      have hCs0 : 0 ≤ cos (((j : ℝ) + 3 / 2) * z) := cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
      have hcs : cos (θ k z j + z / 2) ≤ cos (((j : ℝ) + 3 / 2) * z) :=
        cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [hθ.2]) hθlow
      -- `c · λ = 2 s (τ_{j−1} c) − κ cos(θ_j + z/2)`
      have hid : ((tau k z ag (j - 1) + tau k z ag j) * sin (z / 2) - 1 * κ z ag * cos (θ k z j)) * cos (z / 2)
          = 2 * sin (z / 2) * (tau k z ag (j - 1) * cos (z / 2)) - κ z ag * cos (θ k z j + z / 2) := by
        rw [hrec, cos_add]; field_simp; ring
      have hTc : tau k z ag (j - 1) * cos (z / 2) ≥ cos (3 * z / 2) - κ z ag * z * Tc (j - 1) := by
        have := mul_le_mul_of_nonneg_right hlow hc.le
        have e : (tau k z ag 0 - κ z ag / cos (z / 2) * z * (Tc (j - 1) : ℝ)) * cos (z / 2)
            = tau k z ag 0 * cos (z / 2) - κ z ag * z * Tc (j - 1) := by field_simp
        linarith
      have p1 : 2 * sin (z / 2) * (cos (3 * z / 2) - κ z ag * z * Tc (j - 1))
          ≤ 2 * sin (z / 2) * (tau k z ag (j - 1) * cos (z / 2)) := mul_le_mul_of_nonneg_left hTc (by positivity)
      have p2 : κ z ag * cos (θ k z j + z / 2) ≤ κ z ag * cos (((j : ℝ) + 3 / 2) * z) :=
        mul_le_mul_of_nonneg_left hcs hκ0.le
      have p3 : sin (z / 2) * κ z ag * z * (2 * Tc (j - 1)) ≤ sin (z / 2) * κ z ag * z * j :=
        mul_le_mul_of_nonneg_left hT (by positivity)
      have p4 : κ z ag * (sin (z / 2) * z * j + cos (((j : ℝ) + 3 / 2) * z))
          ≤ 2 * sin (z / 2) * (sin (z / 2) * z * j + cos (((j : ℝ) + 3 / 2) * z)) :=
        mul_le_mul_of_nonneg_right hκ1 (by positivity)
      have p5 : 0 < 2 * sin (z / 2) * (cos (3 * z / 2) - cos (((j : ℝ) + 3 / 2) * z) - sin (z / 2) * z * j) := by
        apply mul_pos (by positivity); linarith
      have hpos : 0 < ((tau k z ag (j - 1) + tau k z ag j) * sin (z / 2) - 1 * κ z ag * cos (θ k z j))
          * cos (z / 2) := by
        rw [hid]; nlinarith
      exact pos_of_mul_pos_left hpos hc.le
    · -- a switch `t → a`
      have h1 : 0 ≤ κ z ag * cos (θ k z j) := mul_nonneg hκ0.le hcθ
      have h2 : 0 < (tau k z ag (j - 1) + tau k z ag j) * sin (z / 2) := by positivity
      have e : -1 * κ z ag * cos (θ k z j) = -(κ z ag * cos (θ k z j)) := by ring
      rw [e]; linarith
    · -- no switch
      have h2 : 0 < (tau k z ag (j - 1) + tau k z ag j) * sin (z / 2) := by positivity
      rw [zero_mul, zero_mul, sub_zero]; exact h2

/-- **All rung multipliers are positive.** -/
theorem lamR_pos (e : ℕ) (he : e < 16 * k - 1) : 0 < lamR k z ag e := by
  unfold lamR
  split_ifs with h
  · exact lamF_pos hk hz0 hzn hloc ag hag0 hag e h
  · exact lamF_pos hk hz0 hzn hloc ag hag0 hag _ (by omega)

lemma stepOf_le (s : ℕ) (hs : firstSide k s) : stepOf k s ≤ 8 * k - 2 := by
  unfold firstSide at hs
  unfold stepOf
  split_ifs <;> omega

/-- **All side multipliers are negative.** -/
theorem sigS_neg (s : ℕ) (hs : s < 16 * k) : sigS k z ag s < 0 := by
  obtain ⟨hz1, -⟩ := z_small hk hz0 hzn hloc ag hag0 hag
  have hℓ : 0 < ell z := by
    unfold ell; have := sin_pos_of_pos_of_lt_pi (show 0 < z / 2 by linarith) (by linarith [pi_gt_three])
    linarith
  unfold sigS
  split_ifs with h1 h2
  · exact div_neg_of_neg_of_pos (by norm_num) hℓ
  · have := tau_pos hk hz0 hzn hloc ag hag0 hag _ (stepOf_le hk hz0 hzn hloc ag hag0 hag s h2)
    exact div_neg_of_neg_of_pos (by linarith) hℓ
  · have h3 : firstSide k (16 * k - 1 - s) := by unfold firstSide at h2 ⊢; omega
    have := tau_pos hk hz0 hzn hloc ag hag0 hag _ (stepOf_le hk hz0 hzn hloc ag hag0 hag _ h3)
    exact div_neg_of_neg_of_pos (by linarith) hℓ

end pos

end Chiquipoli.Family.Trig.P3
