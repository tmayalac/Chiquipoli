/-
# Problem 3, the algebraic core: one rung of the strip

Along the first half of the strip the rungs are `u_i = −e(θ_i)` with
`θ_i = φ + i z` (`RungVec.rung_vec`), `e(θ) = (cos θ, sin θ)`. Give the side of step
`i` (from `ρ_i` to `ρ_{i+1}`) the weight `−τ_i/ℓ` and write
`S_i = −(τ_i/ℓ) (u_i − u_{i+1})` for its force. The multipliers of Problem 3 are
chosen so that every rung satisfies

    λ_i u_i − S_{i−1} + S_i = ε_i κ (1, 0),                      (`rung_core`)

with `ε_i ∈ {1, 0, −1}` as step `i` switches from `a` to `t`, keeps its type, or
switches back. The equilibrium of a vertex is the sum of this identity over its
run of rungs, where the `ε_i` cancel.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Chiquipoli.Family.Trig.P3

open Real

/-- `e(θ) = (cos θ, sin θ)`. -/
noncomputable def e (θ : ℝ) : ℝ × ℝ := (cos θ, sin θ)

/-- `e(θ + 2w) − e(θ) = 2 sin w · (−sin(θ + w), cos(θ + w))`. -/
lemma e_diff (θ w : ℝ) :
    e (θ + 2 * w) - e θ = (2 * sin w) • ((-sin (θ + w), cos (θ + w)) : ℝ × ℝ) := by
  have h1 : θ + 2 * w = (θ + w) + w := by ring
  have h2 : θ = (θ + w) - w := by ring
  simp only [e, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · rw [h1, cos_add]; conv_lhs => rw [h2]
    rw [cos_sub]; ring_nf
  · rw [h1, sin_add]; conv_lhs => rw [h2]
    rw [sin_sub]; ring_nf

/-- The force of the side of a step whose rungs are `−e(θ)` and `−e(θ + 2w)`,
with weight `−τ/ℓ`, `ℓ = 2 sin w`. -/
noncomputable def S (τ θ w : ℝ) : ℝ × ℝ := (-τ / (2 * sin w)) • ((-e θ) - (-e (θ + 2 * w)))

lemma S_eq (τ θ w : ℝ) (hw : sin w ≠ 0) : S τ θ w = τ • ((sin (θ + w), -cos (θ + w)) : ℝ × ℝ) := by
  unfold S
  rw [show (-e θ) - (-e (θ + 2 * w)) = e (θ + 2 * w) - e θ by abel, e_diff, smul_smul]
  simp only [Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> field_simp

/-- **One rung.** With `τ = τ' + ε κ sin θ / cos w` and
`λ = (τ' + τ) sin w − ε κ cos θ`, the rung `−e(θ)` with weight `λ`, the side
before it (`τ'`, rungs `−e(θ − 2w)`, `−e(θ)`) and the side after it (`τ`, rungs
`−e(θ)`, `−e(θ + 2w)`) leave exactly `ε κ (1, 0)`. -/
theorem rung_core (θ w τ' ε κ : ℝ) (hw : sin w ≠ 0) (hcw : cos w ≠ 0) :
    let τ := τ' + ε * κ * sin θ / cos w
    let lam := (τ' + τ) * sin w - ε * κ * cos θ
    lam • (-e θ) - S τ' (θ - 2 * w) w + S τ θ w = ((ε * κ, 0) : ℝ × ℝ) := by
  intro τ lam
  rw [S_eq _ _ _ hw, S_eq _ _ _ hw]
  have a1 : θ - 2 * w + w = θ - w := by ring
  rw [a1]
  simp only [e, lam, τ, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, Prod.fst_neg, Prod.snd_neg, sin_add, cos_add, sin_sub, cos_sub]
  have hθ := sin_sq_add_cos_sq θ
  constructor
  · field_simp
    linear_combination (ε * κ * cos w) * hθ
  · field_simp
    ring

end Chiquipoli.Family.Trig.P3
