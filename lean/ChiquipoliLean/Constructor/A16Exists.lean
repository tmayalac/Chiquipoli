/-
The headline statement: an A16 configuration exists, and it is *exactly*
equilateral with *exactly* unit active diagonals.

This is Lemma 6.1 of the article together with the existence half of
Proposition 6.2(1), stated for the explicit Bingane–Audet constructor and
proved end to end inside the Lean kernel.
-/
import ChiquipoliLean.Constructor.Identities
import ChiquipoliLean.Constructor.RootExists

namespace Chiquipoli

open Real Set

/-- The common side length squared, `ℓ(z)^2 = (2 sin(z/2))^2 = 2 - 2 cos z`. -/
lemma ell_sq (z : ℝ) : (2 * sin (z / 2)) ^ 2 = 2 - 2 * cos z := by
  linear_combination four_sin_sq_half z

/-- **All sixteen sides have the same length `ℓ(z) = 2 sin(z/2)`.** -/
theorem all_sides (z : ℝ) (hF : Ffun z = 0) :
    sqd (p0 z)  (p1 z)  = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p1 z)  (p2 z)  = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p2 z)  (p3 z)  = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p3 z)  (p4 z)  = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p4 z)  (p5 z)  = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p5 z)  (p6 z)  = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p6 z)  (p7 z)  = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p7 z)  (p8 z)  = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p8 z)  (p9 z)  = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p9 z)  (p10 z) = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p10 z) (p11 z) = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p11 z) (p12 z) = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p12 z) (p13 z) = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p13 z) (p14 z) = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p14 z) (p15 z) = (2 * sin (z / 2)) ^ 2 ∧
    sqd (p15 z) (p0 z)  = (2 * sin (z / 2)) ^ 2 := by
  rw [ell_sq]
  exact ⟨side_0_1 z, side_1_2 z, side_2_3 z, side_3_4 z hF, side_4_5 z,
         side_5_6 z, side_6_7 z, side_7_8 z, side_8_9 z, side_9_10 z,
         side_10_11 z, side_11_12 z, side_12_13 z hF, side_13_14 z,
         side_14_15 z, side_15_0 z⟩

/-- **All fifteen active diagonals have length exactly `1`.**

Note these hold for *every* `z`: they are ring identities of the constructor,
independent of the scalar equation. -/
theorem all_active_diameters (z : ℝ) :
    sqd (p0 z) (p7 z)  = 1 ∧ sqd (p0 z) (p8 z)  = 1 ∧ sqd (p0 z) (p9 z)  = 1 ∧
    sqd (p1 z) (p9 z)  = 1 ∧ sqd (p2 z) (p9 z)  = 1 ∧ sqd (p2 z) (p10 z) = 1 ∧
    sqd (p3 z) (p10 z) = 1 ∧ sqd (p3 z) (p11 z) = 1 ∧ sqd (p3 z) (p12 z) = 1 ∧
    sqd (p4 z) (p13 z) = 1 ∧ sqd (p5 z) (p13 z) = 1 ∧ sqd (p6 z) (p13 z) = 1 ∧
    sqd (p6 z) (p14 z) = 1 ∧ sqd (p7 z) (p14 z) = 1 ∧ sqd (p7 z) (p15 z) = 1 :=
  ⟨diam_0_7 z, diam_0_8 z, diam_0_9 z, diam_1_9 z, diam_2_9 z, diam_2_10 z,
   diam_3_10 z, diam_3_11 z, diam_3_12 z, diam_4_13 z, diam_5_13 z,
   diam_6_13 z, diam_6_14 z, diam_7_14 z, diam_7_15 z⟩

/-- **Main theorem.** There is a real parameter `z`, with `cos z` inside the
certified bracket, at which the Bingane–Audet constructor produces a
hexadecagon whose sixteen sides all have the common length `2 sin(z/2)` and
whose fifteen active diagonals all have length exactly `1`.

Everything above is exact: no interval arithmetic, no floating point, and no
step of the form "an interval contains zero, therefore the value is zero". -/
theorem A16_exists :
    ∃ z : ℝ,
      cos z ∈ Ioo clo chi ∧
      Ffun z = 0 ∧
      (sqd (p0 z)  (p1 z)  = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p1 z)  (p2 z)  = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p2 z)  (p3 z)  = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p3 z)  (p4 z)  = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p4 z)  (p5 z)  = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p5 z)  (p6 z)  = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p6 z)  (p7 z)  = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p7 z)  (p8 z)  = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p8 z)  (p9 z)  = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p9 z)  (p10 z) = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p10 z) (p11 z) = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p11 z) (p12 z) = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p12 z) (p13 z) = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p13 z) (p14 z) = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p14 z) (p15 z) = (2 * sin (z / 2)) ^ 2 ∧
       sqd (p15 z) (p0 z)  = (2 * sin (z / 2)) ^ 2) ∧
      (sqd (p0 z) (p7 z)  = 1 ∧ sqd (p0 z) (p8 z)  = 1 ∧ sqd (p0 z) (p9 z)  = 1 ∧
       sqd (p1 z) (p9 z)  = 1 ∧ sqd (p2 z) (p9 z)  = 1 ∧ sqd (p2 z) (p10 z) = 1 ∧
       sqd (p3 z) (p10 z) = 1 ∧ sqd (p3 z) (p11 z) = 1 ∧ sqd (p3 z) (p12 z) = 1 ∧
       sqd (p4 z) (p13 z) = 1 ∧ sqd (p5 z) (p13 z) = 1 ∧ sqd (p6 z) (p13 z) = 1 ∧
       sqd (p6 z) (p14 z) = 1 ∧ sqd (p7 z) (p14 z) = 1 ∧ sqd (p7 z) (p15 z) = 1) := by
  obtain ⟨z, hF, hc⟩ := exists_constructor_root
  exact ⟨z, hc, hF, all_sides z hF, all_active_diameters z⟩

end Chiquipoli
