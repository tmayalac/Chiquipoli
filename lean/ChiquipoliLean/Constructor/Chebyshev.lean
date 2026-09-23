/-
Multiple-angle reduction for the A16 constructor.

The constructor uses `sin (k*z)` and `cos (k*z)` for `k = 1, …, 7`. Each reduces
to a polynomial in `c = cos z`, with the sine carrying a single factor of
`sin z`:

    sin (k*z) = sin z * U (k-1) (cos z),      cos (k*z) = T k (cos z),

`T`/`U` the Chebyshev polynomials of the first/second kind. The `sin` lemmas are
pure ring identities (`U k = c * U (k-1) + T k`); the `cos` lemmas each consume
the Pythagorean identity exactly once, with coefficient `-U (k-1) (cos z)`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Chiquipoli

open Real

variable (z : ℝ)

/-- The Pythagorean identity in the orientation used throughout: it is the *only*
place where `sin z` is eliminated, so every later step is pure polynomial algebra. -/
lemma pyth : sin z ^ 2 = 1 - cos z ^ 2 := by
  linear_combination sin_sq_add_cos_sq z

/-! ### Sines: `sin (k*z) = sin z * U (k-1) (cos z)` -/

lemma sin_1 : sin (1 * z) = sin z * 1 := by rw [one_mul]; ring

lemma sin_2 : sin (2 * z) = sin z * (2 * cos z) := by
  have h : (2 : ℝ) * z = z + z := by ring
  rw [h, sin_add]; ring

lemma cos_1 : cos (1 * z) = cos z := by rw [one_mul]

lemma cos_2 : cos (2 * z) = 2 * cos z ^ 2 - 1 := by
  have h : (2 : ℝ) * z = z + z := by ring
  rw [h, cos_add]
  linear_combination -pyth z

lemma sin_3 : sin (3 * z) = sin z * (4 * cos z ^ 2 - 1) := by
  have h : (3 : ℝ) * z = 2 * z + z := by ring
  rw [h, sin_add, sin_2, cos_2]; ring

lemma cos_3 : cos (3 * z) = 4 * cos z ^ 3 - 3 * cos z := by
  have h : (3 : ℝ) * z = 2 * z + z := by ring
  rw [h, cos_add, sin_2, cos_2]
  linear_combination (-(2 * cos z)) * pyth z

lemma sin_4 : sin (4 * z) = sin z * (8 * cos z ^ 3 - 4 * cos z) := by
  have h : (4 : ℝ) * z = 3 * z + z := by ring
  rw [h, sin_add, sin_3, cos_3]; ring

lemma cos_4 : cos (4 * z) = 8 * cos z ^ 4 - 8 * cos z ^ 2 + 1 := by
  have h : (4 : ℝ) * z = 3 * z + z := by ring
  rw [h, cos_add, sin_3, cos_3]
  linear_combination (-(4 * cos z ^ 2 - 1)) * pyth z

lemma sin_5 : sin (5 * z) = sin z * (16 * cos z ^ 4 - 12 * cos z ^ 2 + 1) := by
  have h : (5 : ℝ) * z = 4 * z + z := by ring
  rw [h, sin_add, sin_4, cos_4]; ring

lemma cos_5 : cos (5 * z) = 16 * cos z ^ 5 - 20 * cos z ^ 3 + 5 * cos z := by
  have h : (5 : ℝ) * z = 4 * z + z := by ring
  rw [h, cos_add, sin_4, cos_4]
  linear_combination (-(8 * cos z ^ 3 - 4 * cos z)) * pyth z

lemma sin_6 : sin (6 * z) = sin z * (32 * cos z ^ 5 - 32 * cos z ^ 3 + 6 * cos z) := by
  have h : (6 : ℝ) * z = 5 * z + z := by ring
  rw [h, sin_add, sin_5, cos_5]; ring

lemma cos_6 : cos (6 * z) = 32 * cos z ^ 6 - 48 * cos z ^ 4 + 18 * cos z ^ 2 - 1 := by
  have h : (6 : ℝ) * z = 5 * z + z := by ring
  rw [h, cos_add, sin_5, cos_5]
  linear_combination (-(16 * cos z ^ 4 - 12 * cos z ^ 2 + 1)) * pyth z

lemma sin_7 :
    sin (7 * z) = sin z * (64 * cos z ^ 6 - 80 * cos z ^ 4 + 24 * cos z ^ 2 - 1) := by
  have h : (7 : ℝ) * z = 6 * z + z := by ring
  rw [h, sin_add, sin_6, cos_6]; ring

lemma cos_7 :
    cos (7 * z) = 64 * cos z ^ 7 - 112 * cos z ^ 5 + 56 * cos z ^ 3 - 7 * cos z := by
  have h : (7 : ℝ) * z = 6 * z + z := by ring
  rw [h, cos_add, sin_6, cos_6]
  linear_combination (-(32 * cos z ^ 5 - 32 * cos z ^ 3 + 6 * cos z)) * pyth z

end Chiquipoli
