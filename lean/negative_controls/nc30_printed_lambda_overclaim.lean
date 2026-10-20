-- NEGATIVE CONTROL. Must FAIL to compile.
-- Proposition 6.2(5) prints λ_min > 0.09186 for the multipliers of Table S2;
-- the smallest of them, on the diameter {6,13}, is 0.0918668 (Table S2 prints
-- 0.09186678). Raising the bound to 0.09187 makes the statement false, and the
-- same proof, with the tight bracket, must not go through.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Chiquipoli.FirstOrder
theorem bad {z : ℝ} (hF : Ffun z = 0) (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (h0 : 0 < z) (hpi : z < Real.pi) : ∀ e, (9187 / 100000 : ℝ) < A16lamP z e := by
  intro e
  have := A16_lamP_gt hF hcb h0 hpi e
  linarith
end Chiquipoli.Feasible
