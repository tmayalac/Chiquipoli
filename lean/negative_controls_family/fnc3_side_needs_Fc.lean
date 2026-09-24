-- NEGATIVE CONTROL (family). Must FAIL to compile.
-- Side 7 of A32 is one of the two that hold only at the root of Fc. Claimed for
-- every c, by the proof of an unconditional side, it must be rejected.
import ChiquipoliFamily.A32
namespace Chiquipoli.Family.A32
theorem bad (c : ℝ) :
    (1 - c ^ 2) * (XC8 c - XC7 c) ^ 2 + (YC8 c - YC7 c) ^ 2 = 2 - 2 * c := by
  unfold XC7 XC8 YC7 YC8; ring
end Chiquipoli.Family.A32
