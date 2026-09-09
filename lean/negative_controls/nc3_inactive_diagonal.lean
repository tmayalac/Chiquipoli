-- NEGATIVE CONTROL. Must FAIL to compile.
-- (4,12) is an INACTIVE diagonal: the Julia certificate proves it is strictly
-- shorter than 1 (inactive margin > 0). Claiming it equals 1 must not go through.
import ChiquipoliLean
namespace Chiquipoli
theorem bad (z : ℝ) : sqd (p4 z) (p12 z) = 1 := by
  rw [red4, red12, sqd_reduce]; simp only [XC4, XC12, YC4, YC12]; ring
end Chiquipoli
