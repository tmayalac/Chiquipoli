/-
**Lemma 6.1 of the paper, formally verified.**

The sixteen side equalities and the fifteen active-diameter equalities of the
A16 candidate. Twenty-nine of the thirty-one hold *identically in `z`* — they
are ring identities, true of the constructor whatever the value of the scalar
parameter. Only the two sides `(3,4)` and `(12,13)` actually consume the
constructor equation `F z = 0`, and they consume it with quotient exactly `1`:

    sqd (p3 z) (p4 z) - (2 - 2 cos z)  =  Fc (cos z)   (on the nose)

This is the "29 vs 2" split that the Julia certificate reports, re-established
here inside the Lean kernel. No interval, no floating point, and in particular
no step of the form "this interval contains zero, therefore the quantity is
zero" appears anywhere in this file.
-/
import ChiquipoliLean.Constructor.Coordinates

namespace Chiquipoli

open Real

/-! ### The fourteen unconditional sides -/

theorem side_0_1 (z : ℝ) : sqd (p0 z) (p1 z) = 2 - 2 * cos z := by
  rw [red0, red1, sqd_reduce]; simp only [XC0, XC1, YC0, YC1]; ring

theorem side_1_2 (z : ℝ) : sqd (p1 z) (p2 z) = 2 - 2 * cos z := by
  rw [red1, red2, sqd_reduce]; simp only [XC1, XC2, YC1, YC2]; ring

theorem side_2_3 (z : ℝ) : sqd (p2 z) (p3 z) = 2 - 2 * cos z := by
  rw [red2, red3, sqd_reduce]; simp only [XC2, XC3, YC2, YC3]; ring

theorem side_4_5 (z : ℝ) : sqd (p4 z) (p5 z) = 2 - 2 * cos z := by
  rw [red4, red5, sqd_reduce]; simp only [XC4, XC5, YC4, YC5]; ring

theorem side_5_6 (z : ℝ) : sqd (p5 z) (p6 z) = 2 - 2 * cos z := by
  rw [red5, red6, sqd_reduce]; simp only [XC5, XC6, YC5, YC6]; ring

theorem side_6_7 (z : ℝ) : sqd (p6 z) (p7 z) = 2 - 2 * cos z := by
  rw [red6, red7, sqd_reduce]; simp only [XC6, XC7, YC6, YC7]; ring

theorem side_7_8 (z : ℝ) : sqd (p7 z) (p8 z) = 2 - 2 * cos z := by
  rw [red7, red8, sqd_reduce]; simp only [XC7, XC8, YC7, YC8]; ring

theorem side_8_9 (z : ℝ) : sqd (p8 z) (p9 z) = 2 - 2 * cos z := by
  rw [red8, red9, sqd_reduce]; simp only [XC8, XC9, YC8, YC9]; ring

theorem side_9_10 (z : ℝ) : sqd (p9 z) (p10 z) = 2 - 2 * cos z := by
  rw [red9, red10, sqd_reduce]; simp only [XC9, XC10, YC9, YC10]; ring

theorem side_10_11 (z : ℝ) : sqd (p10 z) (p11 z) = 2 - 2 * cos z := by
  rw [red10, red11, sqd_reduce]; simp only [XC10, XC11, YC10, YC11]; ring

theorem side_11_12 (z : ℝ) : sqd (p11 z) (p12 z) = 2 - 2 * cos z := by
  rw [red11, red12, sqd_reduce]; simp only [XC11, XC12, YC11, YC12]; ring

theorem side_13_14 (z : ℝ) : sqd (p13 z) (p14 z) = 2 - 2 * cos z := by
  rw [red13, red14, sqd_reduce]; simp only [XC13, XC14, YC13, YC14]; ring

theorem side_14_15 (z : ℝ) : sqd (p14 z) (p15 z) = 2 - 2 * cos z := by
  rw [red14, red15, sqd_reduce]; simp only [XC14, XC15, YC14, YC15]; ring

theorem side_15_0 (z : ℝ) : sqd (p15 z) (p0 z) = 2 - 2 * cos z := by
  rw [red15, red0, sqd_reduce]; simp only [XC15, XC0, YC15, YC0]; ring

/-! ### The two sides that consume the constructor equation

Both defects are *exactly* `Fc (cos z)` — quotient `1`, remainder `0`. -/

theorem sqd_12_13 (z : ℝ) : sqd (p12 z) (p13 z) = (2 - 2 * cos z) + Fc (cos z) := by
  rw [red12, red13, sqd_reduce]; simp only [XC12, XC13, YC12, YC13, Fc]; ring

theorem side_3_4 (z : ℝ) (hF : Ffun z = 0) : sqd (p3 z) (p4 z) = 2 - 2 * cos z := by
  rw [sqd_3_4, Fc_cos_eq_Ffun, hF, add_zero]

theorem side_12_13 (z : ℝ) (hF : Ffun z = 0) : sqd (p12 z) (p13 z) = 2 - 2 * cos z := by
  rw [sqd_12_13, Fc_cos_eq_Ffun, hF, add_zero]

/-! ### The fifteen active diameters, all unconditional -/

theorem diam_0_7 (z : ℝ) : sqd (p0 z) (p7 z) = 1 := by
  rw [red0, red7, sqd_reduce]; simp only [XC0, XC7, YC0, YC7]; ring

theorem diam_0_8 (z : ℝ) : sqd (p0 z) (p8 z) = 1 := by
  rw [red0, red8, sqd_reduce]; simp only [XC0, XC8, YC0, YC8]; ring

theorem diam_0_9 (z : ℝ) : sqd (p0 z) (p9 z) = 1 := by
  rw [red0, red9, sqd_reduce]; simp only [XC0, XC9, YC0, YC9]; ring

theorem diam_1_9 (z : ℝ) : sqd (p1 z) (p9 z) = 1 := by
  rw [red1, red9, sqd_reduce]; simp only [XC1, XC9, YC1, YC9]; ring

theorem diam_2_9 (z : ℝ) : sqd (p2 z) (p9 z) = 1 := by
  rw [red2, red9, sqd_reduce]; simp only [XC2, XC9, YC2, YC9]; ring

theorem diam_2_10 (z : ℝ) : sqd (p2 z) (p10 z) = 1 := by
  rw [red2, red10, sqd_reduce]; simp only [XC2, XC10, YC2, YC10]; ring

theorem diam_3_10 (z : ℝ) : sqd (p3 z) (p10 z) = 1 := by
  rw [red3, red10, sqd_reduce]; simp only [XC3, XC10, YC3, YC10]; ring

theorem diam_3_11 (z : ℝ) : sqd (p3 z) (p11 z) = 1 := by
  rw [red3, red11, sqd_reduce]; simp only [XC3, XC11, YC3, YC11]; ring

theorem diam_3_12 (z : ℝ) : sqd (p3 z) (p12 z) = 1 := by
  rw [red3, red12, sqd_reduce]; simp only [XC3, XC12, YC3, YC12]; ring

theorem diam_4_13 (z : ℝ) : sqd (p4 z) (p13 z) = 1 := by
  rw [red4, red13, sqd_reduce]; simp only [XC4, XC13, YC4, YC13]; ring

theorem diam_5_13 (z : ℝ) : sqd (p5 z) (p13 z) = 1 := by
  rw [red5, red13, sqd_reduce]; simp only [XC5, XC13, YC5, YC13]; ring

theorem diam_6_13 (z : ℝ) : sqd (p6 z) (p13 z) = 1 := by
  rw [red6, red13, sqd_reduce]; simp only [XC6, XC13, YC6, YC13]; ring

theorem diam_6_14 (z : ℝ) : sqd (p6 z) (p14 z) = 1 := by
  rw [red6, red14, sqd_reduce]; simp only [XC6, XC14, YC6, YC14]; ring

theorem diam_7_14 (z : ℝ) : sqd (p7 z) (p14 z) = 1 := by
  rw [red7, red14, sqd_reduce]; simp only [XC7, XC14, YC7, YC14]; ring

theorem diam_7_15 (z : ℝ) : sqd (p7 z) (p15 z) = 1 := by
  rw [red7, red15, sqd_reduce]; simp only [XC7, XC15, YC7, YC15]; ring

end Chiquipoli
