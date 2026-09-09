/-
**Proposition 6.2(2): the certified side length and perimeter.**

The one item of Proposition 6.2 with no Lean counterpart until now. The rest of
the development proves the sides are *equal*; nothing pinned the common value
numerically, because the certified bracket `[clo, chi] = [0.9808, 0.980801]` for
`cos z*` is far too wide — it gives `ℓ` to five digits, and the paper states
nineteen.

The fix is a second, much tighter bracket, obtained the same way as the first
and for free: `Fc` is strictly increasing on `[clo, chi]` (`Fc_strictMonoOn`) and
has integer coefficients, so evaluating it at two rationals a unit apart in the
22nd decimal place and checking the signs by exact arithmetic isolates the root
to within `10⁻²²`. That is `cos_root_tight` below. Everything else is algebra:

    ℓ² = (2 sin(z/2))² = 2 − 2 cos z,

so bounds on `cos z*` give bounds on `ℓ²` directly, and bounds on `ℓ` itself by
monotonicity of the square root. No interval arithmetic, no floating point — the
sign checks are exact rational evaluations of a degree-12 integer polynomial.

The bounds proved here are exactly the paper's displayed ones. Unlike the
convexity and inactive-margin constants, which Lean certifies in a deliberately
rounder and weaker form, these are stated at the paper's own sharpness.
-/
import ChiquipoliLean.Positivity
import ChiquipoliLean.Constructor

namespace Chiquipoli

open Real

/-- Tight rational lower bound for `cos z*`, one unit below it in the 22nd
decimal place. -/
noncomputable def cLo : ℝ := 9808007223804781715147 / 10 ^ 22

/-- Tight rational upper bound for `cos z*`. -/
noncomputable def cHi : ℝ := 9808007223804781715148 / 10 ^ 22

lemma cLo_mem : cLo ∈ Set.Icc clo chi := by
  constructor
  · unfold cLo clo; norm_num
  · unfold cLo chi; norm_num

lemma cHi_mem : cHi ∈ Set.Icc clo chi := by
  constructor
  · unfold cHi clo; norm_num
  · unfold cHi chi; norm_num

/-- Exact sign check: `Fc` is strictly negative at the lower rational. -/
lemma Fc_cLo_neg : Fc cLo < 0 := by
  unfold Fc cLo; norm_num

/-- Exact sign check: `Fc` is strictly positive at the upper rational. -/
lemma Fc_cHi_pos : 0 < Fc cHi := by
  unfold Fc cHi; norm_num

/-- **The root, isolated to `10⁻²²`.** Strict monotonicity turns the two sign
checks into a two-sided bound on `cos z*`. -/
theorem cos_root_tight (z : ℝ) (hF : Ffun z = 0)
    (hc : Real.cos z ∈ Set.Ioo clo chi) :
    cLo < Real.cos z ∧ Real.cos z < cHi := by
  have hz : Real.cos z ∈ Set.Icc clo chi := ⟨le_of_lt hc.1, le_of_lt hc.2⟩
  have h0 : Fc (Real.cos z) = 0 := by rw [Fc_cos_eq_Ffun]; exact hF
  constructor
  · have : Fc cLo < Fc (Real.cos z) := by rw [h0]; exact Fc_cLo_neg
    exact (Fc_strictMonoOn.lt_iff_lt cLo_mem hz).mp this
  · have : Fc (Real.cos z) < Fc cHi := by rw [h0]; exact Fc_cHi_pos
    exact (Fc_strictMonoOn.lt_iff_lt hz cHi_mem).mp this

/-- The half-angle identity behind `ℓ² = 2 − 2 cos z`. -/
lemma sq_side_eq (z : ℝ) : (2 * Real.sin (z / 2)) ^ 2 = 2 - 2 * Real.cos z := by
  have h2 := Real.cos_two_mul (z / 2)
  have hs := Real.sin_sq_add_cos_sq (z / 2)
  rw [show 2 * (z / 2) = z by ring] at h2
  nlinarith [h2, hs]

/-- **Proposition 6.2(2), squared form.** The common squared side length,
enclosed. This is the quantity `A16_certificate` states the sides are equal to. -/
theorem sq_side_bounds (z : ℝ) (hF : Ffun z = 0)
    (hc : Real.cos z ∈ Set.Ioo clo chi) :
    2 - 2 * cHi ≤ (2 * Real.sin (z / 2)) ^ 2 ∧
    (2 * Real.sin (z / 2)) ^ 2 ≤ 2 - 2 * cLo := by
  obtain ⟨h1, h2⟩ := cos_root_tight z hF hc
  rw [sq_side_eq]
  constructor <;> linarith

lemma side_sq_nonneg (z : ℝ) (hF : Ffun z = 0) (hc : Real.cos z ∈ Set.Ioo clo chi) :
    (0:ℝ) ≤ 2 - 2 * Real.cos z := by
  have := (cos_root_tight z hF hc).2
  unfold cHi at this; linarith

/-- **Proposition 6.2(2), the side length.** `ℓ = √(2 − 2 cos z*)` lies in the
paper's displayed interval. -/
theorem side_length_bounds (z : ℝ) (hF : Ffun z = 0)
    (hc : Real.cos z ∈ Set.Ioo clo chi) :
    (1959554930055385228 / 10 ^ 19 : ℝ) ≤ Real.sqrt (2 - 2 * Real.cos z) ∧
    Real.sqrt (2 - 2 * Real.cos z) ≤ 1959554930055385230 / 10 ^ 19 := by
  obtain ⟨h1, h2⟩ := cos_root_tight z hF hc
  constructor
  · have hq : (0:ℝ) ≤ 1959554930055385228 / 10 ^ 19 := by norm_num
    have hsq : ((1959554930055385228 / 10 ^ 19 : ℝ)) ^ 2 ≤ 2 - 2 * Real.cos z := by
      unfold cHi at h2; nlinarith
    calc (1959554930055385228 / 10 ^ 19 : ℝ)
        = Real.sqrt ((1959554930055385228 / 10 ^ 19) ^ 2) := (Real.sqrt_sq hq).symm
      _ ≤ Real.sqrt (2 - 2 * Real.cos z) := Real.sqrt_le_sqrt hsq
  · have hr : (0:ℝ) ≤ 1959554930055385230 / 10 ^ 19 := by norm_num
    have hsq : 2 - 2 * Real.cos z ≤ ((1959554930055385230 / 10 ^ 19 : ℝ)) ^ 2 := by
      unfold cLo at h1; nlinarith
    calc Real.sqrt (2 - 2 * Real.cos z)
        ≤ Real.sqrt ((1959554930055385230 / 10 ^ 19) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 1959554930055385230 / 10 ^ 19 := Real.sqrt_sq hr

/-- **Proposition 6.2(2), the perimeter.** `16ℓ` lies in the paper's displayed
interval. -/
theorem perimeter_bounds (z : ℝ) (hF : Ffun z = 0)
    (hc : Real.cos z ∈ Set.Ioo clo chi) :
    (31352878880886163663 / 10 ^ 19 : ℝ) ≤ 16 * Real.sqrt (2 - 2 * Real.cos z) ∧
    16 * Real.sqrt (2 - 2 * Real.cos z) ≤ 31352878880886163665 / 10 ^ 19 := by
  obtain ⟨h1, h2⟩ := cos_root_tight z hF hc
  have hnn : (0:ℝ) ≤ 2 - 2 * Real.cos z := side_sq_nonneg z hF hc
  constructor
  · have hq : (0:ℝ) ≤ 31352878880886163663 / (16 * 10 ^ 19) := by norm_num
    have hsq : ((31352878880886163663 / (16 * 10 ^ 19) : ℝ)) ^ 2 ≤ 2 - 2 * Real.cos z := by
      unfold cHi at h2; nlinarith
    have := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hq] at this
    linarith
  · have hr : (0:ℝ) ≤ 31352878880886163665 / (16 * 10 ^ 19) := by norm_num
    have hsq : 2 - 2 * Real.cos z ≤ ((31352878880886163665 / (16 * 10 ^ 19) : ℝ)) ^ 2 := by
      unfold cLo at h1; nlinarith
    have := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hr] at this
    linarith

end Chiquipoli
