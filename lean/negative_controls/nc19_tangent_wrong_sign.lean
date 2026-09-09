-- NEGATIVE CONTROL. Must FAIL to compile.
-- The blow-up limit of an ACTIVE diameter constraint points weakly INWARD:
-- `dD q z.1 i j ≤ 0`. The direction of that inequality is the whole content of
-- the step — it is what makes `K_eq` a one-sided cone rather than a subspace,
-- and reversing it would make `no_ascent` vacuous. Asserting the opposite sign
-- from the same hypotheses must not go through.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Filter Topology
theorem bad {n : ℕ} {q : Cfg n} {u : ℕ → Amb n} {t : ℕ → ℝ} {z : Amb n}
    (ht : ∀ k, 0 < t k) (htz : Tendsto t atTop (𝓝 0))
    (hz : Tendsto (fun k => (t k)⁻¹ • u k) atTop (𝓝 z))
    (i j : Fin n) (hact : dC i j q = 0) (hle : ∀ k, dC i j (q + (u k).1) ≤ 0) :
    0 ≤ dD q z.1 i j :=
  dD_nonpos_of_blowup ht htz hz i j hact hle
end Chiquipoli.Feasible
