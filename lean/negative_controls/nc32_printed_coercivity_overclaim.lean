-- NEGATIVE CONTROL. Must FAIL to compile.
-- Proposition 6.2(7) prints s₃₀(B)² ≥ 0.09119; the least nonzero singular value
-- of B = D(e,d) at A16 has s₃₀(B)² ≈ 0.09211 (floating point), so the
-- coercivity bound with 0.0922 is false.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Chiquipoli.FirstOrder
theorem bad {z : ℝ} (hsz : 0 < Real.sin z) (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (h0 : 0 < z) (hpi : z < Real.pi)
    (v : Cfg 16) (η : ℝ) (horth : ∀ w, (A16DataU z).R w → cip v w = 0) :
    (922 / 10000 : ℝ) * (cip v v + η ^ 2)
      ≤ (∑ i, ((A16DataU z).sideD v η i) ^ 2) + ∑ e, ((A16DataU z).diamD v e) ^ 2 := by
  have := A16_coercive_unit hsz hcb h0 hpi v η horth
  nlinarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => ip_self_nonneg (v i), sq_nonneg η]
end Chiquipoli.Feasible
