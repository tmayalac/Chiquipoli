-- NEGATIVE CONTROL. Must FAIL to compile.
-- The support determinants are positive only for the upper-half-plane root
-- (sin z > 0). The mirror image is an equally valid polygon with every
-- determinant flipped, so dropping the orientation hypothesis must break the
-- proof; if this compiled, the convexity certificates would be claiming
-- something orientation-independent, which is false.
import ChiquipoliLean
namespace Chiquipoli
theorem bad (z : ℝ) (hc : Real.cos z ∈ Set.Ioo clo chi) :
    0 < cross (p0 z) (p1 z) (p2 z) := by
  rw [red0, red1, red2, cross_reduce]
  exact mul_pos (by norm_num)
    (by linarith [convD_0_2 (Real.cos z) (le_of_lt hc.1) (le_of_lt hc.2)])
end Chiquipoli
