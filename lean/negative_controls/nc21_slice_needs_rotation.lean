-- NEGATIVE CONTROL. Must FAIL to compile.
-- The slice condition is orthogonality to ALL THREE generators of R(p): two
-- translations and the rotation T3. Dropping T3 would leave the rotational
-- degree of freedom unconstrained, and the final step of Theorem 3.5 — v in
-- R(p) and v in R(p)-perp, hence v = 0 — would no longer close. Deriving the
-- full slice condition from the two translations alone must not go through.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Chiquipoli.FirstOrder
theorem bad {n : ℕ} {w p : Cfg n} {iota : Type*} [Fintype iota]
    {D : Data n iota} (hDp : D.p = p)
    (h1 : cip w (T1 n) = 0) (h2 : cip w (T2 n) = 0) :
    ∀ r, D.R r → cip w r = 0 :=
  slice_of_generators hDp h1 h2 (by trivial)
end Chiquipoli.Feasible
