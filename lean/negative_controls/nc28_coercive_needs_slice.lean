-- NEGATIVE CONTROL. Must FAIL to compile.
-- The coercivity bound behind Theorem 6.4 holds only on the slice v ⊥ R(p).
-- Without that hypothesis it is false, not merely unproved: a common
-- translation v_i = (1, 0) with dt = 0 annihilates every side and diameter
-- differential while cip v v = 16 > 0. Dropping `horth` must not go through.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Chiquipoli.FirstOrder
theorem bad {z : ℝ} (hsz : 0 < Real.sin z) (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (v : Cfg 16) (dt : ℝ) :
    (17 / 625 : ℝ) * (cip v v + dt ^ 2)
      ≤ (∑ i, ((A16Data z).sideD v dt i) ^ 2) + ∑ e, ((A16Data z).diamD v e) ^ 2 := by
  exact A16_coercive hsz hcb v dt (fun w _ => by simp [cip])
end Chiquipoli.Feasible
