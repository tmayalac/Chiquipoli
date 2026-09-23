/-
**Proposition 3.8 (first order instability criterion), kernel-checked.**

The counterpart to Theorem 3.5: a feasible direction that increases the
objective to first order rules out local maximality. Where Theorem 3.5 needs a
blow-up argument, this direction is elementary — the paper's proof is three
lines, and so is this.

The paper states it as: if `(v,η) ∈ K_eq(p,ℓ)` with `η > 0` is realised as the
initial velocity of a `C¹` feasible curve, then `(p,ℓ)` is not a local
maximiser, because `d/dt|₀ L = DL[v,η] = nη > 0`.

Everything specific to polygons is upstream of that computation. What the
argument actually uses is only that the perimeter *along the realising curve*
has a strictly positive derivative at `t = 0`; feasibility of the curve is what
makes the conclusion about the constrained problem rather than about `L` alone,
and it enters as the hypothesis that such a curve exists. So the content is
isolated here as a statement about a real function, and instantiated at the
rhombus in `Instances/SquareAndRhombus.lean`, where the realising curve is explicit.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

namespace Chiquipoli.FirstOrder

/-- **Proposition 3.8.** If the objective along a realising curve has strictly
positive derivative at `0`, it is strictly larger at every sufficiently small
positive time. This is the paper's "the perimeter increases for all sufficiently
small positive `t`", stated as an eventuality on `𝓝[>] 0`. -/
theorem increases_to_the_right {L : ℝ → ℝ} {c : ℝ}
    (hL : HasDerivAt L c 0) (hc : 0 < c) :
    ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), L 0 < L t := by
  have hs : Filter.Tendsto (slope L 0) (nhdsWithin 0 {0}ᶜ) (nhds c) :=
    hasDerivAt_iff_tendsto_slope.mp hL
  have hpos : ∀ᶠ y in nhdsWithin (0:ℝ) {0}ᶜ, 0 < slope L 0 y :=
    hs.eventually (eventually_gt_nhds hc)
  have hsub : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhdsWithin (0:ℝ) {0}ᶜ :=
    nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  filter_upwards [hsub hpos, self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field, div_pos_iff] at ht
  rcases ht with ⟨h1, _⟩ | ⟨_, h2⟩
  · linarith [sub_pos.mp h1]
  · exact absurd htpos (by simpa using not_lt.mpr (le_of_lt (sub_neg.mp h2)))

/-- The same conclusion in Mathlib's vocabulary: `0` is not a local maximum of
the objective along the curve. Two-sided, hence slightly weaker than
`increases_to_the_right`, but it is the statement "not a local maximiser" reads
as. -/
theorem not_isLocalMax {L : ℝ → ℝ} {c : ℝ} (hL : HasDerivAt L c 0) (hc : 0 < c) :
    ¬ IsLocalMax L 0 :=
  fun h => absurd (h.hasDerivAt_eq_zero hL) (ne_of_gt hc)

/-- The paper's exact shape: the derivative is `DL[v,η] = n·η`, so a feasible
direction with `η > 0` at a polygon with `n ≥ 1` sides is enough. -/
theorem not_isLocalMax_of_eta_pos {L : ℝ → ℝ} {n : ℕ} {η : ℝ}
    (hn : 0 < n) (hη : 0 < η) (hL : HasDerivAt L ((n : ℝ) * η) 0) :
    ¬ IsLocalMax L 0 :=
  not_isLocalMax hL (by positivity)

end Chiquipoli.FirstOrder
