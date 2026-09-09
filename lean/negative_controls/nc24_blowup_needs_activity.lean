-- NEGATIVE CONTROL. Must FAIL to compile.
-- K_eq is built from the diameters ACTIVE at p (`dC (a e) (b e) p = 0`). A
-- diameter with slack imposes no first-order condition (Remark 2.7), so a
-- multiplier attached to one carries no information and the identity would no
-- longer force anything. Weakening activity to mere feasibility must not go
-- through.
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
    (hpact : ∀ e : iota, dC (a e) (b e) p ≤ 0)
    {x : ℕ → Amb n} (hfeas : ∀ k, IsFeasible (x k)) (hne : ∀ k, x k ≠ (p, l))
    (hconv : Tendsto x atTop (𝓝 (p, l))) (hge : ∀ k, l ≤ (x k).2)
    (hslice : ∀ k, ∀ r : Cfg n, (dataOf p l a b).R r → cip ((x k).1 - p) r = 0) :
    False :=
  no_blowup_sequence hl hkap hm hlam hIR hpeq hpact hfeas hne hconv hge hslice
end Chiquipoli.Feasible
