-- NEGATIVE CONTROL. Must FAIL to compile.
-- Side (3,4) is one of the two identities that genuinely CONSUME the constructor
-- equation F z = 0. Dropping that hypothesis must break the proof; if this
-- compiled, the "29 unconditional vs 2 conditional" split would be wrong.
import ChiquipoliLean
namespace Chiquipoli
theorem bad (z : ℝ) : sqd (p3 z) (p4 z) = 2 - 2 * Real.cos z := by
  rw [red3, red4, sqd_reduce]; simp only [XC3, XC4, YC3, YC4]; ring
end Chiquipoli
