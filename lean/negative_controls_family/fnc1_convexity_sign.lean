-- NEGATIVE CONTROL (family). Must FAIL to compile.
-- A support determinant of A32 claimed NEGATIVE, with the same proof the
-- certificate uses: the enclosures must not be able to prove the wrong sign.
import ChiquipoliFamily.A32
namespace Chiquipoli.Family.A32
open Chiquipoli.Family
theorem bad (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
    (XC1 c - XC0 c) * (YC2 c - YC0 c) - (YC1 c - YC0 c) * (XC2 c - XC0 c) < 0 := by
  have h := det_lb (encX0 c h₁ h₂) (encX1 c h₁ h₂) (encX2 c h₁ h₂) (encY0 c h₁ h₂) (encY1 c h₁ h₂) (encY2 c h₁ h₂)
  have := convD_0_2 c h₁ h₂
  linarith
end Chiquipoli.Family.A32
