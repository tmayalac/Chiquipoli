-- NEGATIVE CONTROL. Must FAIL to compile.
-- Claims an active diagonal has squared length 2 instead of 1.
import ChiquipoliLean
namespace Chiquipoli
theorem bad (z : ℝ) : sqd (p0 z) (p7 z) = 2 := by
  rw [red0, red7, sqd_reduce]; simp only [XC0, XC7, YC0, YC7]; ring
end Chiquipoli
