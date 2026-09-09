-- NEGATIVE CONTROL. Must FAIL to compile.
-- Claims the side length clears 0.1959554930055385229, one unit past the
-- certified lower bound in the 19th decimal place. The true value is
-- 0.1959554930055385228996..., so this is false by about 10^-19 — far below
-- anything a wider bracket could see. If it compiled, the tight root bracket
-- of `SideLength.lean` would be proving more than the root supports.
import ChiquipoliLean
namespace Chiquipoli
theorem bad (z : ℝ) (hF : Ffun z = 0) (hc : Real.cos z ∈ Set.Ioo clo chi) :
    (1959554930055385229 / 10 ^ 19 : ℝ) ≤ Real.sqrt (2 - 2 * Real.cos z) := by
  obtain ⟨h1, h2⟩ := cos_root_tight z hF hc
  have hq : (0:ℝ) ≤ 1959554930055385229 / 10 ^ 19 := by norm_num
  have hsq : ((1959554930055385229 / 10 ^ 19 : ℝ)) ^ 2 ≤ 2 - 2 * Real.cos z := by
    unfold cHi at h2; nlinarith
  calc (1959554930055385229 / 10 ^ 19 : ℝ)
      = Real.sqrt ((1959554930055385229 / 10 ^ 19) ^ 2) := (Real.sqrt_sq hq).symm
    _ ≤ Real.sqrt (2 - 2 * Real.cos z) := Real.sqrt_le_sqrt hsq
end Chiquipoli
