-- NEGATIVE CONTROL. Must FAIL to compile.
-- The limit inequality for a diameter needs the constraint to be ACTIVE at the
-- base point (`dC i j q = 0`). A merely feasible one (`dC i j q ≤ 0`) has slack,
-- so its first-order limit is unconstrained — this is exactly why `K_eq` is
-- built from the active edges alone (Remark 2.7). Dropping activity to mere
-- feasibility must not go through.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Filter Topology
theorem bad {n : ℕ} {q : Cfg n} {u : ℕ → Amb n} {t : ℕ → ℝ} {z : Amb n}
    (ht : ∀ k, 0 < t k) (htz : Tendsto t atTop (𝓝 0))
    (hz : Tendsto (fun k => (t k)⁻¹ • u k) atTop (𝓝 z))
    (i j : Fin n) (hact : dC i j q ≤ 0) (hle : ∀ k, dC i j (q + (u k).1) ≤ 0) :
    dD q z.1 i j ≤ 0 :=
  dD_nonpos_of_blowup ht htz hz i j hact hle
end Chiquipoli.Feasible
