-- NEGATIVE CONTROL. Must FAIL to compile.
-- Theorem 3.5 needs the active-diameter multipliers STRICTLY POSITIVE. Claiming
-- one of them is negative must not go through — if it did, the witness would be
-- proving both a statement and its negation, i.e. the system would be
-- inconsistent.
import ChiquipoliLean
namespace Chiquipoli
theorem bad (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : mL0 c < 0 := by
  linarith [mL0_pos c h₁ h₂]
end Chiquipoli
