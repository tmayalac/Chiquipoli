/-
The A16 constructor, written in Lean directly from `coordinates(z)` in
`src/A16Certificate.jl`, and its reduction to the generated polynomial layer.

Nothing here is imported from Julia: the sixteen vertices below are transcribed
by hand from the Julia source, while `XC*`/`YC*`/`Fc` in `Generated.lean` come
from Julia's exact `Rational{BigInt}` arithmetic. The `red*` lemmas prove the
two agree, so a transcription slip on either side fails to compile.
-/
import ChiquipoliLean.Chebyshev
import ChiquipoliLean.Generated

namespace Chiquipoli

open Real

/-- `X(z)` of the Bingane–Audet constructor. -/
noncomputable def Xf (z : ℝ) : ℝ := sin z - (2 * cos z - 1) * sin (4 * z)

/-- `Y(z)` of the Bingane–Audet constructor. -/
noncomputable def Yf (z : ℝ) : ℝ := cos z - (2 * cos z - 1) * cos (4 * z)

/-- The scalar equation whose root fixes the A16 candidate:
`F z = (2 X(z) + sin 7z)^2 + (cos 7z)^2 - 4 sin(z/2)^2`. -/
noncomputable def Ffun (z : ℝ) : ℝ :=
  (2 * Xf z + sin (7 * z)) ^ 2 + cos (7 * z) ^ 2 - 4 * sin (z / 2) ^ 2

/-- Squared Euclidean distance between two planar points. -/
noncomputable def sqd (a b : ℝ × ℝ) : ℝ := (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2

/-! ### The sixteen labelled vertices -/

-- `p0` and `p8` are constant vertices: the constructor pins them at the origin
-- and at the north pole, so they genuinely do not mention `z`.
set_option linter.unusedVariables false in
noncomputable def p0  (z : ℝ) : ℝ × ℝ := (0, 0)
noncomputable def p1  (z : ℝ) : ℝ × ℝ := (sin (2*z) - sin z, cos z - cos (2*z))
noncomputable def p2  (z : ℝ) : ℝ × ℝ := (sin (3*z) - sin z, cos z - cos (3*z))
noncomputable def p3  (z : ℝ) : ℝ × ℝ := (-Xf z, Yf z)
noncomputable def p4  (z : ℝ) : ℝ × ℝ := (Xf z + sin (7*z), Yf z + cos (7*z))
noncomputable def p5  (z : ℝ) : ℝ × ℝ := (Xf z + sin (6*z), Yf z + cos (6*z))
noncomputable def p6  (z : ℝ) : ℝ × ℝ := (Xf z + sin (5*z), Yf z + cos (5*z))
noncomputable def p7  (z : ℝ) : ℝ × ℝ := (sin z, cos z)
set_option linter.unusedVariables false in
noncomputable def p8  (z : ℝ) : ℝ × ℝ := (0, 1)
noncomputable def p9  (z : ℝ) : ℝ × ℝ := (-sin z, cos z)
noncomputable def p10 (z : ℝ) : ℝ × ℝ := (-Xf z - sin (5*z), Yf z + cos (5*z))
noncomputable def p11 (z : ℝ) : ℝ × ℝ := (-Xf z - sin (6*z), Yf z + cos (6*z))
noncomputable def p12 (z : ℝ) : ℝ × ℝ := (-Xf z - sin (7*z), Yf z + cos (7*z))
noncomputable def p13 (z : ℝ) : ℝ × ℝ := (Xf z, Yf z)
noncomputable def p14 (z : ℝ) : ℝ × ℝ := (sin z - sin (3*z), cos z - cos (3*z))
noncomputable def p15 (z : ℝ) : ℝ × ℝ := (sin z - sin (2*z), cos z - cos (2*z))

/-! ### Reduction to the polynomial layer

Each vertex has the exact form `(sin z * XC i (cos z), YC i (cos z))`. These are
pure ring identities once the multiple angles are expanded — the Pythagorean
identity is *not* used, because every `sin` occurs linearly. -/

lemma red0  (z : ℝ) : p0  z = (sin z * XC0  (cos z), YC0  (cos z)) := by
  simp [p0, XC0, YC0]

lemma red1  (z : ℝ) : p1  z = (sin z * XC1  (cos z), YC1  (cos z)) := by
  simp only [p1, XC1, YC1, sin_2, cos_2, Prod.mk.injEq]; constructor <;> ring

lemma red2  (z : ℝ) : p2  z = (sin z * XC2  (cos z), YC2  (cos z)) := by
  simp only [p2, XC2, YC2, sin_3, cos_3, Prod.mk.injEq]; constructor <;> ring

lemma red3  (z : ℝ) : p3  z = (sin z * XC3  (cos z), YC3  (cos z)) := by
  simp only [p3, Xf, Yf, XC3, YC3, sin_4, cos_4, Prod.mk.injEq]; constructor <;> ring

lemma red4  (z : ℝ) : p4  z = (sin z * XC4  (cos z), YC4  (cos z)) := by
  simp only [p4, Xf, Yf, XC4, YC4, sin_4, cos_4, sin_7, cos_7, Prod.mk.injEq]
  constructor <;> ring

lemma red5  (z : ℝ) : p5  z = (sin z * XC5  (cos z), YC5  (cos z)) := by
  simp only [p5, Xf, Yf, XC5, YC5, sin_4, cos_4, sin_6, cos_6, Prod.mk.injEq]
  constructor <;> ring

lemma red6  (z : ℝ) : p6  z = (sin z * XC6  (cos z), YC6  (cos z)) := by
  simp only [p6, Xf, Yf, XC6, YC6, sin_4, cos_4, sin_5, cos_5, Prod.mk.injEq]
  constructor <;> ring

lemma red7  (z : ℝ) : p7  z = (sin z * XC7  (cos z), YC7  (cos z)) := by
  simp only [p7, XC7, YC7, Prod.mk.injEq]; constructor <;> ring

lemma red8  (z : ℝ) : p8  z = (sin z * XC8  (cos z), YC8  (cos z)) := by
  simp [p8, XC8, YC8]

lemma red9  (z : ℝ) : p9  z = (sin z * XC9  (cos z), YC9  (cos z)) := by
  simp only [p9, XC9, YC9, Prod.mk.injEq]; constructor <;> ring

lemma red10 (z : ℝ) : p10 z = (sin z * XC10 (cos z), YC10 (cos z)) := by
  simp only [p10, Xf, Yf, XC10, YC10, sin_4, cos_4, sin_5, cos_5, Prod.mk.injEq]
  constructor <;> ring

lemma red11 (z : ℝ) : p11 z = (sin z * XC11 (cos z), YC11 (cos z)) := by
  simp only [p11, Xf, Yf, XC11, YC11, sin_4, cos_4, sin_6, cos_6, Prod.mk.injEq]
  constructor <;> ring

lemma red12 (z : ℝ) : p12 z = (sin z * XC12 (cos z), YC12 (cos z)) := by
  simp only [p12, Xf, Yf, XC12, YC12, sin_4, cos_4, sin_7, cos_7, Prod.mk.injEq]
  constructor <;> ring

lemma red13 (z : ℝ) : p13 z = (sin z * XC13 (cos z), YC13 (cos z)) := by
  simp only [p13, Xf, Yf, XC13, YC13, sin_4, cos_4, Prod.mk.injEq]; constructor <;> ring

lemma red14 (z : ℝ) : p14 z = (sin z * XC14 (cos z), YC14 (cos z)) := by
  simp only [p14, XC14, YC14, sin_3, cos_3, Prod.mk.injEq]; constructor <;> ring

lemma red15 (z : ℝ) : p15 z = (sin z * XC15 (cos z), YC15 (cos z)) := by
  simp only [p15, XC15, YC15, sin_2, cos_2, Prod.mk.injEq]; constructor <;> ring

/-! ### Squared distance in the polynomial layer -/

/-- Once both endpoints are in reduced form, the squared distance loses every
trace of `sin z`. This is the single place the Pythagorean identity is spent. -/
lemma sqd_reduce (z X Y X' Y' : ℝ) :
    sqd (sin z * X, Y) (sin z * X', Y')
      = (1 - cos z ^ 2) * (X' - X) ^ 2 + (Y' - Y) ^ 2 := by
  simp only [sqd]
  linear_combination ((X' - X) ^ 2) * pyth z

/-- `4 sin(z/2)^2 = 2 - 2 cos z`, the exact target for a side length. -/
lemma four_sin_sq_half (z : ℝ) : 4 * sin (z / 2) ^ 2 = 2 - 2 * cos z := by
  have h2 : (2 : ℝ) * (z / 2) = z := by ring
  have hc := cos_2 (z / 2)
  rw [h2] at hc
  have hp := pyth (z / 2)
  linear_combination 4 * hp + 2 * hc

/-! ### The constructor equation *is* the side `(3,4)` defect

`F z` is, by construction, the squared length of the edge `p3 p4` minus the
square of the common side length — so the link between the trigonometric `Ffun`
and the generated polynomial `Fc` needs no separate computation. -/

lemma Ffun_eq_sqd (z : ℝ) : Ffun z = sqd (p3 z) (p4 z) - 4 * sin (z / 2) ^ 2 := by
  simp only [Ffun, sqd, p3, p4]; ring

lemma sqd_3_4 (z : ℝ) : sqd (p3 z) (p4 z) = (2 - 2 * cos z) + Fc (cos z) := by
  rw [red3, red4, sqd_reduce]
  simp only [XC3, XC4, YC3, YC4, Fc]; ring

/-- The generated polynomial evaluates the constructor equation exactly:
`Fc (cos z) = F z` for every real `z`. -/
theorem Fc_cos_eq_Ffun (z : ℝ) : Fc (cos z) = Ffun z := by
  rw [Ffun_eq_sqd, sqd_3_4, four_sin_sq_half]; ring

end Chiquipoli
