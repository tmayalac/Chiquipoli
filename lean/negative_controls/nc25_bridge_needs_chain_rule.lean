-- NEGATIVE CONTROL. Must FAIL to compile.
-- FirstOrderA16 works in the SQUARED formulation: the scalar variable is
-- t = l^2, so its eta is d(l^2) = 2*l*dl, not dl. Identifying the two
-- normalisations without the chain-rule factor 2*l would be a silent unit
-- error that changes nothing syntactically and everything mathematically —
-- it would rescale every side multiplier against the diameter multipliers.
-- Dropping the factor must not go through.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Chiquipoli.FirstOrder
theorem bad (z l : ℝ) (v : Cfg 16) (eta : ℝ)
    (hs : ∀ i, eD (A16p z) l v eta i = 0)
    (hd : ∀ e, dD (A16p z) v (A16a e) (A16b e) ≤ 0) :
    (A16Data z).Keq v eta :=
  A16_bridge z l v eta hs hd
end Chiquipoli.Feasible
