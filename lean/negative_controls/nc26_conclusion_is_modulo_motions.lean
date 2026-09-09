-- NEGATIVE CONTROL. Must FAIL to compile.
-- Theorem 3.5 concludes uniqueness MODULO orientation-preserving Euclidean
-- motions, and it cannot conclude more: translating or rotating A16 gives
-- another feasible configuration with the same side length, arbitrarily close
-- to it. Strengthening `Congruent y.1 p` to `y.1 = p` must not go through.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Chiquipoli.FirstOrder Filter Topology
theorem bad :
    ∃ z : ℝ, ∃ l : ℝ, 0 < l ∧
      ∀ᶠ y in 𝓝 ((A16p z, l) : Amb 16),
        IsFeasible y → l ≤ y.2 → y.1 = A16p z := by
  obtain ⟨z, l, hl, _, hev⟩ := A16_locally_maximal
  exact ⟨z, l, hl, hev.mono fun y hy hf hge => (hy hf hge).1⟩
end Chiquipoli.Feasible
