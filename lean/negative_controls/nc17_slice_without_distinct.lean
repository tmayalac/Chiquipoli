-- NEGATIVE CONTROL. Must FAIL to compile.
-- Lemma 3.4's independence step without the hypothesis that two vertices are
-- distinct. It is false without it: at a configuration whose vertices all
-- coincide at the origin, T3 = (Jp_0, ..., Jp_{n-1}) vanishes identically, so
-- the rotation coefficient is unconstrained and R(p) is at most 2-dimensional.
-- That is exactly why the paper hypothesises "at least two distinct vertices".
import ChiquipoliLean
namespace Chiquipoli.FirstOrder
theorem bad {n : ℕ} {p : Fin n → ℝ × ℝ} {i : Fin n}
    {c : ℝ × ℝ × ℝ} (h : rigidOf p c = 0) : c = 0 := by
  have hi1 : c.1 - c.2.2 * (p i).2 = 0 := by
    have := congrArg Prod.fst (congrFun h i); simpa [rigidOf] using this
  have hi2 : c.2.1 + c.2.2 * (p i).1 = 0 := by
    have := congrArg Prod.snd (congrFun h i); simpa [rigidOf] using this
  have hom : c.2.2 = 0 := by linarith
  have ha : c.1 = 0 := by rw [hom] at hi1; linarith
  have hb : c.2.1 = 0 := by rw [hom] at hi2; linarith
  exact Prod.ext ha (Prod.ext hb hom)
end Chiquipoli.FirstOrder
