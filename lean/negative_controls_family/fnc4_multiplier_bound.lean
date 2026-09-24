-- NEGATIVE CONTROL (family). Must FAIL to compile.
-- The first active-diameter stress of A32 (st32) is certified in a narrow
-- enclosure around a small positive value. Claiming it is at least 1, from that
-- same enclosure, must not go through.
import ChiquipoliFamily.A32
namespace Chiquipoli.Family.A32
open Chiquipoli.Family
theorem bad (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : (1 : ℝ) ≤ st32 c := by
  have h := encS32 c h₁ h₂
  have := (abs_le.mp h).1
  linarith
end Chiquipoli.Family.A32
