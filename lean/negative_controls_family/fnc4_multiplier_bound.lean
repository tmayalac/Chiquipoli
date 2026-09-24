-- NEGATIVE CONTROL (family). Must FAIL to compile.
-- The diameter multipliers of A32 are about 10⁻⁴. A lower bound of 1 for the
-- first one must not be provable from its Taylor enclosure.
import ChiquipoliFamily.A32
namespace Chiquipoli.Family.A32
theorem bad (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : (1 : ℝ) ≤ mL0 c := by
  have := lam_lb0 c h₁ h₂
  linarith
end Chiquipoli.Family.A32
