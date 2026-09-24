-- NEGATIVE CONTROL (family). Must FAIL to compile.
-- The tightest inactive pair of A32, (8,24), is at squared distance 0.99808.
-- Claiming it below 0.99 must not go through: the margin is real, not slack.
import ChiquipoliFamily.A32
namespace Chiquipoli.Family.A32
open Chiquipoli.Family
theorem bad (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
    (1 - c ^ 2) * (XC24 c - XC8 c) ^ 2 + (YC24 c - YC8 c) ^ 2 < 99 / 100 := by
  obtain ⟨hs0, hs⟩ := sin2_bounds c h₁ h₂
  have h := sqd_ub (encX8 c h₁ h₂) (encX24 c h₁ h₂) (encY8 c h₁ h₂) (encY24 c h₁ h₂) hs0 hs
  unfold sb rho at h
  norm_num [abs_of_pos, abs_of_neg] at h
  linarith
end Chiquipoli.Family.A32
