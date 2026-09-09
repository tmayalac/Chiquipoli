-- NEGATIVE CONTROL. Must FAIL to compile.
-- Claims a side target of 2 - 3cos z instead of 2 - 2cos z.
import ChiquipoliLean
namespace Chiquipoli
theorem bad (z : ℝ) : sqd (p0 z) (p1 z) = 2 - 3 * Real.cos z := by
  rw [red0, red1, sqd_reduce]; simp only [XC0, XC1, YC0, YC1]; ring
end Chiquipoli
