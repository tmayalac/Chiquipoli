/-
# The Bingane–Audet polygon is a strict local maximiser, for every `n = 16k`

`strict_local_max_all`: for every `n = 16k` (`k ≥ 1`), `F_n` has exactly one zero
`z` in `(0, π/n)`, it lies in `(π/(n+2), π/n)`, and the polygon upstream's code
builds there is a strict local maximiser of the side length (hence of the
perimeter) among equilateral small `n`-gons, modulo Euclidean motions.

* `n ≥ 32`: `P3Main.local_max_of_positive` with the positivity of `P3Pos`. The
  width of the gap is positive by `P3Gap.yy_pos`.
* `n = 16`: the per-case certificate `T16.published_locally_maximal`. Its zero is
  the one of `root_all`, by uniqueness.

Not yet proved for every `n`: that the published polygon itself is small (no
pair outside `G_n` at distance `> 1`) and convex. These are Problem 1; they are
certified per case for `n ≤ 256` (`published_of_checks`).
-/
import ChiquipoliFamily.Trig.P3Pos
import ChiquipoliFamily.T16.Main

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig.P3

open Real Set Filter Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig

/-- **Strict local maximality, for every `n = 16k`.** -/
theorem strict_local_max_all (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) :
    ∃ z : ℝ, z ∈ Ioo (π / ((n : ℝ) + 2)) (π / n) ∧ Optigon.F n z = 0 ∧
      (∀ z' ∈ Ioo 0 (π / n), Optigon.F n z' = 0 → z' = z) ∧ 0 < 2 * sin (z / 2) ∧
      ∀ᶠ y in nhds ((Qc n z, 2 * sin (z / 2)) : Amb n), IsFeasible y → 2 * sin (z / 2) ≤ y.2 →
        Feasible.Congruent y.1 (Qc n z) ∧ y.2 = 2 * sin (z / 2) := by
  have hn16 : 16 ≤ n := by omega
  obtain ⟨z, hz, hF, -, huniq⟩ := root_all n hn16
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hpi := pi_pos
  have hz0 : 0 < z := lt_trans (by positivity) hz.1
  have hz4 : z < π / 4 := by
    have : π / n ≤ π / 16 := div_le_div_of_nonneg_left hpi.le (by norm_num) hN
    linarith [hz.2]
  have hl : 0 < 2 * sin (z / 2) := by
    have := sin_pos_of_pos_of_lt_pi (show 0 < z / 2 by linarith) (by linarith); linarith
  refine ⟨z, hz, hF, huniq, hl, ?_⟩
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · -- `n = 16`: the per-case certificate
    have hk' : k = 1 := by omega
    subst hk'
    have h16 : n = 16 := by omega
    subst h16
    obtain ⟨z₁, hz₁, hF₁, -, -, -, hmax, -⟩ := T16.published_locally_maximal
    have hlo : 0 < Optigon.lo 16 := by
      unfold Optigon.lo
      have : 0 < sin (π / (16 : ℕ)) := sin_pos_of_pos_of_lt_pi (by positivity) (by
        push_cast; linarith)
      have := arcsin_pos.mpr (show 0 < sin (π / (16 : ℕ)) / 2 by positivity)
      linarith
    have hz₁z : z₁ = z := huniq z₁ ⟨lt_trans hlo hz₁.1, hz₁.2⟩ hF₁
    subst hz₁z
    exact hmax
  · -- `n ≥ 32`: Problem 3 in closed form
    obtain ⟨hloc, hy⟩ := loc n hn16 hz0 hz.2 hF
    have hag0 : 0 < gapA hk hn (z := z) := by
      rw [gapA_eq_yy k hk hn z]; exact yy_pos n (by omega) hz0 hz.2 hF
    have hag : gapA hk hn (z := z) ≤ 2 * sin (z / 2) ^ 2 := by
      rw [gapA_eq_yy k hk hn z]; exact le_trans (le_abs_self _) hy
    have hzn : z < π / ((16 * k : ℕ) : ℝ) := by rw [← hn]; exact hz.2
    have hloc' : π / (((16 * k : ℕ) : ℝ) - 2 + π) ≤ z := by rw [← hn]; exact hloc
    have hlam : ∀ e : Fin (n - 1), 0 < lamR k z (gapA hk hn (z := z)) e.val := fun e =>
      lamR_pos hk2 hz0 hzn hloc' _ hag0 hag e.val (by have := e.isLt; omega)
    have hsum : ∑ i : Fin n, sigS k z (gapA hk hn (z := z)) i.val < 0 := by
      have : 0 < ∑ i : Fin n, -sigS k z (gapA hk hn (z := z)) i.val := by
        apply Finset.sum_pos
        · intro i _
          have := sigS_neg hk2 hz0 hzn hloc' _ hag0 hag i.val (by have := i.isLt; omega)
          linarith
        · exact Finset.univ_nonempty
      rw [Finset.sum_neg_distrib] at this; linarith
    exact local_max_of_positive hk hn hz0 hz4 hF hlam hsum

end Chiquipoli.Family.Trig.P3
