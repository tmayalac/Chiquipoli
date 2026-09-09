-- NEGATIVE CONTROL. Must FAIL to compile.
-- The inactive-diagonal bound is NOT a global fact about the constructor: it
-- holds only where the root lives. Dropping the bracket hypotheses must break
-- it, otherwise the certificates would be proving something suspiciously
-- stronger than the geometry allows.
import ChiquipoliLean
namespace Chiquipoli
theorem bad (c : ℝ) :
    (1/100 : ℝ) ≤ 1 - ((1 - c ^ 2) * (XC12 c - XC4 c) ^ 2 + (YC12 c - YC4 c) ^ 2) := by
  unfold XC4 XC12 YC4 YC12
  nlinarith [sq_nonneg c, sq_nonneg (1 - c), sq_nonneg (1 + c)]
end Chiquipoli
