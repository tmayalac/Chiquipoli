-- NEGATIVE CONTROL. Must FAIL to compile.
-- The single most important sanity check on a development this size: the
-- certified bounds must not be mutually contradictory. If `False` were derivable
-- from them, every theorem in the file would be vacuously true and the whole
-- Lean layer would be worthless. This asks exactly that, and must be rejected.
import ChiquipoliLean
namespace Chiquipoli
theorem bad (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : False := by
  have p1 := pivB1 c h₁ h₂
  have p2 := pivB2 c h₁ h₂
  have m0 := mL0_pos c h₁ h₂
  have d  := dFc_lower_bound c h₁ h₂
  linarith
end Chiquipoli
