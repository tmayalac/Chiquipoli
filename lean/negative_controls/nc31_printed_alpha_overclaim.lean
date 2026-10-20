-- NEGATIVE CONTROL. Must FAIL to compile.
-- Proposition 6.2(5) prints ‖α‖₂ < 4.004 for the side multipliers of Table S2,
-- whose norm is 4.00356. The bound 4.003 is false.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Chiquipoli.FirstOrder
theorem bad {z : ℝ} (hF : Ffun z = 0) (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (h0 : 0 < z) (hpi : z < Real.pi) : (∑ i, A16alphaP z i ^ 2) < (4003 / 1000 : ℝ) ^ 2 := by
  have := A16_alphaP_sq hF hcb h0 hpi
  linarith
end Chiquipoli.Feasible
