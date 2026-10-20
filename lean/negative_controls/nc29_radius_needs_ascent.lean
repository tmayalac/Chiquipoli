-- NEGATIVE CONTROL. Must FAIL to compile.
-- Theorem 6.4 compares A16 only with competitors of side length m ≥ ℓ, and it
-- cannot do without that hypothesis: shrinking A16 by a factor 1 - ε keeps it
-- equilateral with diameter below 1, puts it arbitrarily close to A16 modulo
-- motions, and is not congruent to it. Dropping `l ≤ m` must not go through.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Chiquipoli.FirstOrder
theorem bad :
    ∃ z : ℝ, ∃ l : ℝ, 0 < l ∧ IsFeasibleConvex (A16p z, l) ∧
      ∀ (q : Cfg 16) (m : ℝ),
        (∀ i, elen (q (i + 1) - q i) = m) → (∀ i j, elen (q j - q i) ≤ 1) →
        distMod q m (A16p z) l < 663 / 1000000 → m = l ∧ Congruent q (A16p z) := by
  obtain ⟨z, l, hl, _, _, _, hfeas, hrad⟩ := A16_radius
  exact ⟨z, l, hl, hfeas, fun q m hs hd hdist => hrad q m hs hd (by linarith) hdist⟩
end Chiquipoli.Feasible
