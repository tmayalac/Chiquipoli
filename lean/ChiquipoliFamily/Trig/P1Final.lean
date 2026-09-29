/-
# The Bingane–Audet polygon, for every `n = 16k`: the complete statement

`published_all_n`: for every `n = 16k` (`k ≥ 1`), upstream's `F_n` has exactly one
zero `z` in `(0, π/n)`, and it lies in `(π/(n+2), π/n)`. The polygon upstream's
code builds there:
* is a strictly convex, equilateral, small `n`-gon (`IsFeasibleConvex`);
* is a strict local maximiser of the side length (hence of the perimeter) among
  equilateral small `n`-gons, modulo Euclidean motions.

This is the statement of `A<n>/Published.lean`, proved once for every `n = 16k`:
* `n ≥ 32`: `P1.convex_all`, `P1.small_all` (Problem 1) and
  `P3.strict_local_max_all` (Problem 3);
* `n = 16`: the per-case certificate `T16`.
-/
import ChiquipoliFamily.Trig.P1Small

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig.P1

open Real Set Filter Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family Chiquipoli.Family.Trig
  Chiquipoli.Family.Trig.P3

/-- **The published polygon is a strict local maximiser, for every `n = 16k`.** -/
theorem published_all_n (k : ℕ) (hk : 1 ≤ k) {n : ℕ} [NeZero n] (hn : n = 16 * k) :
    ∃ z : ℝ, z ∈ Ioo (π / ((n : ℝ) + 2)) (π / n) ∧ Optigon.F n z = 0 ∧
      (∀ z' ∈ Ioo 0 (π / n), Optigon.F n z' = 0 → z' = z) ∧
      0 < 2 * sin (z / 2) ∧ IsFeasibleConvex (Qc n z, 2 * sin (z / 2)) ∧
      (∀ᶠ y in nhds ((Qc n z, 2 * sin (z / 2)) : Amb n), IsFeasible y → 2 * sin (z / 2) ≤ y.2 →
          Feasible.Congruent y.1 (Qc n z) ∧ y.2 = 2 * sin (z / 2)) ∧
      (∀ᶠ y in nhds ((Qc n z, 2 * sin (z / 2)) : Amb n), IsFeasible y → y.2 ≤ 2 * sin (z / 2)) := by
  obtain ⟨z, hz, hF, huniq, hl, hmax⟩ := strict_local_max_all k hk hn
  have hle : ∀ᶠ y in nhds ((Qc n z, 2 * sin (z / 2)) : Amb n), IsFeasible y → y.2 ≤ 2 * sin (z / 2) := by
    filter_upwards [hmax] with y hy hfeas
    rcases le_or_gt (2 * sin (z / 2)) y.2 with h | h
    · exact (hy hfeas h).2.le
    · exact h.le
  refine ⟨z, hz, hF, huniq, hl, ?_, hmax, hle⟩
  have hN : (16 : ℝ) ≤ n := by exact_mod_cast (show 16 ≤ n by omega)
  have hz0 : 0 < z := lt_trans (by positivity) hz.1
  have hz4 : z < π / 4 := by
    have : π / n ≤ π / 16 := div_le_div_of_nonneg_left pi_pos.le (by norm_num) hN
    linarith [hz.2, pi_pos]
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · -- `n = 16`: the per-case certificate
    have hk' : k = 1 := by omega
    subst hk'
    have h16 : n = 16 := by omega
    subst h16
    obtain ⟨z₁, hz₁, hF₁, -, -, hfeas, -, -⟩ := T16.published_locally_maximal
    have hlo : 0 < Optigon.lo 16 := by
      unfold Optigon.lo
      have : 0 < sin (π / (16 : ℕ)) := sin_pos_of_pos_of_lt_pi (by positivity) (by
        push_cast; linarith [pi_pos])
      have := arcsin_pos.mpr (show 0 < sin (π / (16 : ℕ)) / 2 by positivity)
      linarith
    have hz₁z : z₁ = z := huniq z₁ ⟨lt_trans hlo hz₁.1, hz₁.2⟩ hF₁
    subst hz₁z
    exact hfeas
  · -- `n ≥ 32`: Problem 1
    refine ⟨convex_all hk2 hn hz0 hz.2 hF, small_all hk2 hn hz0 hz.2 hF, fun i => ?_, hl⟩
    unfold eC
    rw [sides_eq_root hk hn hz0 hz4 hF i]; ring

end Chiquipoli.Family.Trig.P1
