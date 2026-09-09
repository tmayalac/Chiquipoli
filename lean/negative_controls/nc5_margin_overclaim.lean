-- NEGATIVE CONTROL. Must FAIL to compile.
-- The Bernstein certificate for the tightest inactive pair (4,12) proves a
-- margin of 1/100; the true margin is ≈0.0161. Claiming 1/10 must not go
-- through — otherwise the certificates would not be bounding anything real.
import ChiquipoliLean
namespace Chiquipoli
theorem bad (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
    (1/10 : ℝ) ≤ 1 - ((1 - c ^ 2) * (XC12 c - XC4 c) ^ 2 + (YC12 c - YC4 c) ^ 2) := by
  linarith [inactive_4_12 c h₁ h₂]
end Chiquipoli
