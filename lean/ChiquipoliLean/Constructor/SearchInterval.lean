/-
The article's search interval, and root uniqueness stated on it.

`Positivity.lean` proves that `Fc` has exactly one root with `c` in
`[slo, shi] = [49/50, 491/500]`, and `constructor_root_unique_in_search` lifts
that to the angle, but only for angles whose cosine is *assumed* to lie in the
bracket. The article states uniqueness on its own search interval

    I_search = (2 arcsin(sin(π/16) / 2), π/16),

(Proposition 6.2(1)), and the passage from one to the other, the inclusion
`cos(I_search) ⊆ [49/50, 491/500]`, was left unformalised. An external audit of
the package (2026-09) flagged exactly this. This file proves the inclusion, from
Mathlib's bounds on `π`, `sin` and `cos`, and states uniqueness on `I_search`
itself, together with existence of a root inside it, so the Lean statement is
the article's with nothing left to the reader.

The margins are wide: on `I_search`, `z` lies in `(0.1948, 0.19635)`, so
`cos z` lies in about `(0.98072, 0.98111)`, well inside `[0.98, 0.982]`. No
interval arithmetic and no floating point: every step is a rational inequality
closed by `norm_num`/`nlinarith`.
-/
import ChiquipoliLean.Generated.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds

namespace Chiquipoli

open Real Set

/-- The article's lower endpoint `2 arcsin(sin(π/16)/2)`. -/
noncomputable def searchLo : ℝ := 2 * Real.arcsin (Real.sin (π / 16) / 2)

/-- The article's upper endpoint `π/16`. -/
noncomputable def searchHi : ℝ := π / 16

/-- The article's search interval `I_search`, open as printed. -/
noncomputable def searchInterval : Set ℝ := Ioo searchLo searchHi

lemma searchHi_lt : searchHi < 19635 / 100000 := by
  unfold searchHi; have := Real.pi_lt_d4; linarith

/-- `sin(π/16)/2 > 0.0974`, from `sin x > x - x³/6` and `π > 3.14`. -/
lemma half_sin_pi_div_sixteen_gt : (974 : ℝ) / 10000 < Real.sin (π / 16) / 2 := by
  have hpi := Real.pi_gt_d2
  have hx : (0 : ℝ) < π / 16 := by positivity
  have hs := Real.sin_gt_sub_cube hx
  have hlo : (314 : ℝ) / 1600 < π / 16 := by linarith
  have hup : π / 16 < (1 : ℝ) := by have := Real.pi_lt_d2; linarith
  -- x - x³/6 is increasing on (0,1), so it exceeds its value at 314/1600
  have hmono : (314 : ℝ) / 1600 - ((314 : ℝ) / 1600) ^ 3 / 6
      ≤ π / 16 - (π / 16) ^ 3 / 6 := by
    nlinarith [sq_nonneg (π / 16 - 314 / 1600), mul_pos hx hx]
  -- `norm_num` only on the rational side: on the goal it would rewrite
  -- `sin (π/16)` into nested radicals.
  norm_num at hmono
  linarith

/-- `searchLo > 0.1948`: `arcsin a > a` for `a > 0`, since `sin t < t`. -/
lemma searchLo_gt : (1948 : ℝ) / 10000 < searchLo := by
  set a := Real.sin (π / 16) / 2 with ha
  have ha0 : 974 / 10000 < a := half_sin_pi_div_sixteen_gt
  have ha1 : a ≤ 1 := by
    have := Real.sin_le_one (π / 16); rw [ha]; linarith
  have hpos : 0 < Real.arcsin a := Real.arcsin_pos.mpr (by linarith)
  have hsin : Real.sin (Real.arcsin a) = a := Real.sin_arcsin (by linarith) ha1
  have hlt : a < Real.arcsin a := by
    have := Real.sin_lt hpos; rw [hsin] at this; exact this
  unfold searchLo; rw [← ha]; linarith

/-- Every angle of `I_search` lies in `[0, 1]` and has its cosine in the bracket
`[slo, shi]` on which `Fc` has a unique root. -/
theorem cos_mem_bracket_of_mem_search {z : ℝ} (hz : z ∈ searchInterval) :
    z ∈ Icc (0 : ℝ) 1 ∧ Real.cos z ∈ Icc slo shi := by
  obtain ⟨hz₁, hz₂⟩ := hz
  have hl := searchLo_gt
  have hu := searchHi_lt
  have zlo : (1948 : ℝ) / 10000 < z := lt_trans hl hz₁
  have zhi : z < 19635 / 100000 := lt_trans hz₂ hu
  have habs : |z| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb := Real.cos_bound habs
  rw [abs_of_pos (by linarith : (0:ℝ) < z), abs_le] at hb
  have hlow := Real.one_sub_sq_div_two_le_cos (x := z)
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩⟩
  · unfold slo; nlinarith
  · unfold shi
    have h2 : (1948 : ℝ) ^ 2 / 10000 ^ 2 < z ^ 2 := by nlinarith
    have h4 : z ^ 4 < ((19635 : ℝ) / 100000) ^ 4 := by
      have : 0 < z := by linarith
      exact pow_lt_pow_left₀ zhi this.le (by norm_num)
    nlinarith [hb.2]

/-- **Proposition 6.2(1), uniqueness, on the article's own interval.** Two roots
of the constructor equation in `I_search` coincide. -/
theorem constructor_root_unique_in_article_search {z₁ z₂ : ℝ}
    (h₁ : z₁ ∈ searchInterval) (h₂ : z₂ ∈ searchInterval)
    (hf₁ : Ffun z₁ = 0) (hf₂ : Ffun z₂ = 0) : z₁ = z₂ := by
  obtain ⟨hz₁, hc₁⟩ := cos_mem_bracket_of_mem_search h₁
  obtain ⟨hz₂, hc₂⟩ := cos_mem_bracket_of_mem_search h₂
  exact constructor_root_unique_in_search hz₁ hz₂ hc₁ hc₂ hf₁ hf₂

/-! ## Existence in `I_search`

The root constructed in `RootExists.lean` has `cos z ∈ (clo, chi) =
(0.9808, 0.980801)`. Placing it inside `I_search` needs `cos(π/16) < 0.9808`, a
margin of about `1.5e-5`, too tight for the Taylor bounds above; Mathlib's exact
`cos(π/16) = √(2 + √(2 + √2))/2` closes it by three squarings. -/

/-- `0.98078 < cos(π/16) < 0.9808`, from the nested radical. -/
lemma cos_pi_div_sixteen_bounds :
    (98078 : ℝ) / 100000 < Real.cos (π / 16) ∧ Real.cos (π / 16) < 9808 / 10000 := by
  rw [Real.cos_pi_div_sixteen]
  have h2lo : (1414213 : ℝ) / 1000000 < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2hi : √2 < (1414214 : ℝ) / 1000000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3lo : (1847758 : ℝ) / 1000000 < √(2 + √2) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have h3hi : √(2 + √2) < (184776 : ℝ) / 100000 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  have h4lo : (196156 : ℝ) / 100000 < √(2 + √(2 + √2)) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have h4hi : √(2 + √(2 + √2)) < (19616 : ℝ) / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  constructor <;> linarith

/-- `cos(searchLo) = 1 - sin²(π/16)/2 > 0.980801`. -/
lemma cos_searchLo_gt : (980801 : ℝ) / 1000000 < Real.cos searchLo := by
  set a := Real.sin (π / 16) / 2 with ha
  have ha1 : a ≤ 1 := by have := Real.sin_le_one (π / 16); rw [ha]; linarith
  have ham : -1 ≤ a := by have := Real.neg_one_le_sin (π / 16); rw [ha]; linarith
  have hsin : Real.sin (Real.arcsin a) = a := Real.sin_arcsin ham ha1
  have hcos : Real.cos searchLo = 1 - 2 * a ^ 2 := by
    unfold searchLo; rw [← ha, Real.cos_two_mul', Real.cos_sq', hsin]; ring
  have hpyth : Real.sin (π / 16) ^ 2 = 1 - Real.cos (π / 16) ^ 2 := by
    rw [Real.sin_sq]
  have hc := (cos_pi_div_sixteen_bounds).1
  rw [hcos, ha, div_pow, hpyth]
  nlinarith

lemma searchLo_mem : searchLo ∈ Icc (0 : ℝ) π := by
  unfold searchLo
  have h0 : 0 ≤ Real.arcsin (Real.sin (π / 16) / 2) :=
    Real.arcsin_nonneg.mpr (by
      have := Real.sin_pos_of_pos_of_lt_pi (x := π / 16) (by positivity)
        (by linarith [Real.pi_pos]); linarith)
  have h1 := Real.arcsin_le_pi_div_two (Real.sin (π / 16) / 2)
  constructor <;> linarith

lemma searchHi_mem : searchHi ∈ Icc (0 : ℝ) π := by
  unfold searchHi; constructor <;> linarith [Real.pi_pos]

/-- **Proposition 6.2(1), in the article's own terms:** the constructor equation
has exactly one root in `I_search`. -/
theorem constructor_root_existsUnique_article_search :
    ∃! z, z ∈ searchInterval ∧ Ffun z = 0 := by
  obtain ⟨c, hc, hfc⟩ := Fc_root_exists
  have hclo : (-1 : ℝ) ≤ c := by have := hc.1; unfold clo at this; linarith
  have hchi : c ≤ 1 := by have := hc.2; unfold chi at this; linarith
  set z := Real.arccos c with hzdef
  have hzc : Real.cos z = c := Real.cos_arccos hclo hchi
  have hzmem : z ∈ Icc (0 : ℝ) π := ⟨Real.arccos_nonneg c, Real.arccos_le_pi c⟩
  have hFz : Ffun z = 0 := by rw [← Fc_cos_eq_Ffun, hzc, hfc]
  have hin : z ∈ searchInterval := by
    constructor
    · -- cos z < chi < cos searchLo, and cos is strictly decreasing on [0, π]
      have h1 : Real.cos z < Real.cos searchLo := by
        rw [hzc]; have := hc.2; have := cos_searchLo_gt; unfold chi at *; linarith
      exact (Real.strictAntiOn_cos.lt_iff_gt hzmem searchLo_mem).mp h1
    · -- cos(π/16) < clo < cos z
      have h1 : Real.cos searchHi < Real.cos z := by
        rw [hzc]; unfold searchHi
        have := hc.1; have := (cos_pi_div_sixteen_bounds).2; unfold clo at *; linarith
      exact (Real.strictAntiOn_cos.lt_iff_gt searchHi_mem hzmem).mp h1
  exact ⟨z, ⟨hin, hFz⟩, fun w hw => constructor_root_unique_in_article_search hw.1 hin hw.2 hFz⟩

end Chiquipoli
