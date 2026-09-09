-- NEGATIVE CONTROL. Must FAIL to compile.
-- The blow-up refutes competitors whose side length is at least l. The
-- direction of that inequality is what gives eta >= 0, which together with
-- n*eta <= 0 pins eta = 0. Competitors with SMALLER side length exist in every
-- neighbourhood of any feasible point — shrinking a polygon slightly stays
-- feasible — so from `(x k).2 <= l` no contradiction can follow. Reversing the
-- inequality must not go through.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Chiquipoli.FirstOrder Filter Topology
theorem bad {n : ℕ} [NeZero n] {iota : Type*} [Fintype iota] {p : Cfg n} {l : ℝ}
    (hl : 0 < l) {a b : iota → Fin n} {kap : ℝ} (hkap : 0 < kap)
    {al : Fin n → ℝ} {lam : iota → ℝ}
    (hm : (dataOf p l a b).MultiplierIdentity kap al lam)
    (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Cfg n, (dataOf p l a b).Ieq w 0 → (dataOf p l a b).R w)
    (hpeq : ∀ i : Fin n, eC i (p, l) = 0)
    (hpact : ∀ e : iota, dC (a e) (b e) p = 0)
    {x : ℕ → Amb n} (hfeas : ∀ k, IsFeasible (x k)) (hne : ∀ k, x k ≠ (p, l))
    (hconv : Tendsto x atTop (𝓝 (p, l))) (hge : ∀ k, (x k).2 ≤ l)
    (hslice : ∀ k, ∀ r : Cfg n, (dataOf p l a b).R r → cip ((x k).1 - p) r = 0) :
    False :=
  no_blowup_sequence hl hkap hm hlam hIR hpeq hpact hfeas hne hconv hge hslice
end Chiquipoli.Feasible
