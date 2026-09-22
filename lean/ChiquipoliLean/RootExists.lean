/-
Existence of the constructor root, by the intermediate value theorem applied to
the *polynomial* `Fc` — not to the transcendental `F`.

This is the step that makes the whole development non-vacuous: the identities in
`Identities.lean` are conditional on `F z = 0`, and here we prove such a `z`
really exists. The bracket is narrow enough to isolate the intended root: `Fc`
has nine sign changes on `[-1,1]`, but the nearest other one sits at
`c ≈ 0.9672`, far outside `[0.9808, 0.980801]`.

Scope note. What is proved here is *existence* of a root in the bracket.
Uniqueness is proved elsewhere in this development: on the bracket
`[49/50, 491/500]` for `c = cos z` by `Fc_root_existsUnique_search`
(`Positivity.lean`), and on the article's own search interval
`I_search = (2 arcsin(sin(π/16)/2), π/16)`, existence included, by
`constructor_root_existsUnique_article_search` (`SearchInterval.lean`). Julia
certifies the same statement independently, by interval Newton and strict
monotonicity of `F` on `I_search`.
-/
import ChiquipoliLean.Constructor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Order.IntermediateValue

namespace Chiquipoli

open Real Set

/-- The lower endpoint of the certified bracket for `c = cos z`. -/
noncomputable def clo : ℝ := 613 / 625

/-- The upper endpoint of the certified bracket for `c = cos z`. -/
noncomputable def chi : ℝ := 980801 / 1000000

lemma clo_lt_chi : clo < chi := by unfold clo chi; norm_num

lemma Fc_continuous : Continuous Fc := by unfold Fc; fun_prop

/-- `Fc` is strictly negative at the lower endpoint. -/
lemma Fc_clo_neg : Fc clo < 0 := by unfold Fc clo; norm_num

/-- `Fc` is strictly positive at the upper endpoint. -/
lemma Fc_chi_pos : 0 < Fc chi := by unfold Fc chi; norm_num

/-- The defining polynomial has a root strictly inside the bracket. -/
theorem Fc_root_exists : ∃ c ∈ Ioo clo chi, Fc c = 0 := by
  have hsub := intermediate_value_Ioo clo_lt_chi.le Fc_continuous.continuousOn
  have h0 : (0 : ℝ) ∈ Ioo (Fc clo) (Fc chi) := ⟨Fc_clo_neg, Fc_chi_pos⟩
  obtain ⟨c, hc, hfc⟩ := hsub h0
  exact ⟨c, hc, hfc⟩

/-- **The constructor root exists.** There is a real parameter `z` solving the
Bingane–Audet scalar equation `F z = 0`, with `cos z` pinned to the narrow
certified bracket. -/
theorem exists_constructor_root :
    ∃ z : ℝ, Ffun z = 0 ∧ cos z ∈ Ioo clo chi := by
  obtain ⟨c, hc, hfc⟩ := Fc_root_exists
  have hlo : (-1 : ℝ) ≤ c := by
    have := hc.1; unfold clo at this; linarith
  have hhi : c ≤ 1 := by
    have := hc.2; unfold chi at this; linarith
  have hcos : cos (arccos c) = c := Real.cos_arccos hlo hhi
  refine ⟨arccos c, ?_, ?_⟩
  · rw [← Fc_cos_eq_Ffun, hcos, hfc]
  · rw [hcos]; exact hc

end Chiquipoli
