/-
**The assembled certificate.**

Every other file here proves a *conditional* statement: "if `z` solves the
constructor equation, lies in the certified bracket, and has `sin z > 0`, then
⟨gate⟩". Existence of such a `z` is proved separately. Until this file, nothing
put the two together — so the development contained six implications and one
existence statement, and a reader had to perform the assembly mentally.

`A16_certificate` below performs it in Lean: it exhibits a single `z` at which
all six computational gates hold simultaneously. That is the statement a
referee should read; everything else is a lemma feeding it.

It proves no new mathematics. It closes a *presentation* gap, and a real one:
"the six gates are verified" and "there is a verified object satisfying the six
gates" are different claims, and only the second is what the certificate is
for.
-/
import ChiquipoliLean.Rank
import ChiquipoliLean.Main

namespace Chiquipoli

open Real

/-- An infinitesimal variation annihilated by every active constraint
differential: each of the sixteen side differentials equals the change `dt` in
the squared side length, and the active-diameter differentials vanish.

Fourteen of the fifteen active diameters appear — that is all `kernel_is_rigid`
consumes, so requiring fewer makes the conclusion stronger. -/
def IsAdmissibleVariation (z : ℝ) (w : Fin 16 → ℝ × ℝ) (dt : ℝ) : Prop :=
  dsq (p0 z) (p1 z) (w 0) (w 1) = dt ∧
  dsq (p1 z) (p2 z) (w 1) (w 2) = dt ∧
  dsq (p2 z) (p3 z) (w 2) (w 3) = dt ∧
  dsq (p3 z) (p4 z) (w 3) (w 4) = dt ∧
  dsq (p4 z) (p5 z) (w 4) (w 5) = dt ∧
  dsq (p5 z) (p6 z) (w 5) (w 6) = dt ∧
  dsq (p6 z) (p7 z) (w 6) (w 7) = dt ∧
  dsq (p7 z) (p8 z) (w 7) (w 8) = dt ∧
  dsq (p8 z) (p9 z) (w 8) (w 9) = dt ∧
  dsq (p9 z) (p10 z) (w 9) (w 10) = dt ∧
  dsq (p10 z) (p11 z) (w 10) (w 11) = dt ∧
  dsq (p11 z) (p12 z) (w 11) (w 12) = dt ∧
  dsq (p12 z) (p13 z) (w 12) (w 13) = dt ∧
  dsq (p13 z) (p14 z) (w 13) (w 14) = dt ∧
  dsq (p14 z) (p15 z) (w 14) (w 15) = dt ∧
  dsq (p15 z) (p0 z) (w 15) (w 0) = dt ∧
  dsq (p0 z) (p7 z) (w 0) (w 7) = 0 ∧
  dsq (p0 z) (p8 z) (w 0) (w 8) = 0 ∧
  dsq (p0 z) (p9 z) (w 0) (w 9) = 0 ∧
  dsq (p1 z) (p9 z) (w 1) (w 9) = 0 ∧
  dsq (p2 z) (p9 z) (w 2) (w 9) = 0 ∧
  dsq (p2 z) (p10 z) (w 2) (w 10) = 0 ∧
  dsq (p3 z) (p10 z) (w 3) (w 10) = 0 ∧
  dsq (p3 z) (p11 z) (w 3) (w 11) = 0 ∧
  dsq (p3 z) (p12 z) (w 3) (w 12) = 0 ∧
  dsq (p4 z) (p13 z) (w 4) (w 13) = 0 ∧
  dsq (p5 z) (p13 z) (w 5) (w 13) = 0 ∧
  dsq (p6 z) (p13 z) (w 6) (w 13) = 0 ∧
  dsq (p6 z) (p14 z) (w 6) (w 14) = 0 ∧
  dsq (p7 z) (p14 z) (w 7) (w 14) = 0

/-- All sixteen sides share the common length, stated over the cyclic successor
so that no side can be omitted. -/
theorem all_sides_cyclic (z : ℝ) (hF : Ffun z = 0) (i : Fin 16) :
    sqd (P i z) (P (nxt i) z) = (2 * Real.sin (z / 2)) ^ 2 := by
  rw [ell_sq]
  fin_cases i
  · exact side_0_1 z
  · exact side_1_2 z
  · exact side_2_3 z
  · exact side_3_4 z hF
  · exact side_4_5 z
  · exact side_5_6 z
  · exact side_6_7 z
  · exact side_7_8 z
  · exact side_8_9 z
  · exact side_9_10 z
  · exact side_10_11 z
  · exact side_11_12 z
  · exact side_12_13 z hF
  · exact side_13_14 z
  · exact side_14_15 z
  · exact side_15_0 z

/-- **The A16 certificate, assembled.**

There is a single real parameter `z` at which *all six* computational gates of
the certificate hold at once:

  1. `z` solves the constructor equation, in the upper half plane, with `cos z`
     in the certified bracket — and it is the **only** root in the search range;
  2. all sixteen sides have the common length `2 sin(z/2)`  (Lemma 6.1);
  3. all fifteen declared active diagonals have length exactly `1` (Lemma 6.1);
  4. **no** pair of vertices exceeds distance 1, and `(0,7)` attains it — the
     diameter is exactly 1  (Prop 6.2(4));
  5. every vertex lies strictly left of every edge — strict convexity in the
     labelled cyclic order  (Prop 6.2(3));
  6. there are multipliers with `Σ αᵢ = -1`, all fifteen diameter multipliers
     strictly positive, and vanishing weighted gradient sum at every vertex
     (Prop 6.2(5));
  7. every admissible infinitesimal variation is a rigid motion, and `dt = 0`
     — `I_eq = R_eq`  (Prop 6.2(6)).

**This statement by itself does not prove that A16 is a strict local maximum.**
It establishes the hypotheses that Theorem 3.5 consumes. Theorem 3.5 is
formalised separately, in `Feasible*.lean`, and
`Feasible.A16_locally_maximal` joins the two into the full conclusion. See
`lean/README.md` for the scope statement, including the reparametrisation used
in gates 6 and 7. -/
theorem A16_certificate :
    ∃ z : ℝ,
      -- (1) the root: exists, upper half plane, in the bracket, and unique
      Ffun z = 0 ∧ 0 < Real.sin z ∧ Real.cos z ∈ Set.Ioo clo chi ∧
      (∀ c' : ℝ, c' ∈ Set.Icc slo shi → Fc c' = 0 → c' = Real.cos z) ∧
      -- (2) equilateral
      (∀ i : Fin 16, sqd (P i z) (P (nxt i) z) = (2 * Real.sin (z / 2)) ^ 2) ∧
      -- (3) the fifteen declared active diagonals are exactly 1
      (sqd (p0 z) (p7 z)  = 1 ∧ sqd (p0 z) (p8 z)  = 1 ∧ sqd (p0 z) (p9 z)  = 1 ∧
       sqd (p1 z) (p9 z)  = 1 ∧ sqd (p2 z) (p9 z)  = 1 ∧ sqd (p2 z) (p10 z) = 1 ∧
       sqd (p3 z) (p10 z) = 1 ∧ sqd (p3 z) (p11 z) = 1 ∧ sqd (p3 z) (p12 z) = 1 ∧
       sqd (p4 z) (p13 z) = 1 ∧ sqd (p5 z) (p13 z) = 1 ∧ sqd (p6 z) (p13 z) = 1 ∧
       sqd (p6 z) (p14 z) = 1 ∧ sqd (p7 z) (p14 z) = 1 ∧ sqd (p7 z) (p15 z) = 1) ∧
      -- (4) the diameter is exactly 1
      ((∀ i j : Fin 16, sqd (P i z) (P j z) ≤ 1) ∧ sqd (P 0 z) (P 7 z) = 1) ∧
      -- (5) strict convexity with the labelled cyclic order
      (∀ i j : Fin 16, j ≠ i → j ≠ nxt i →
        0 < cross (P i z) (P (nxt i) z) (P j z)) ∧
      -- (6) stationarity with strictly positive multipliers
      ((∀ k : Fin 16, gradSum k z = (0, 0)) ∧
       (0 < mL0 (Real.cos z) ∧ 0 < mL1 (Real.cos z) ∧ 0 < mL2 (Real.cos z) ∧
        0 < mL3 (Real.cos z) ∧ 0 < mL4 (Real.cos z) ∧ 0 < mL5 (Real.cos z) ∧
        0 < mL6 (Real.cos z) ∧ 0 < mL7 (Real.cos z) ∧ 0 < mL8 (Real.cos z) ∧
        0 < mL9 (Real.cos z) ∧ 0 < mL10 (Real.cos z) ∧ 0 < mL11 (Real.cos z) ∧
        0 < mL12 (Real.cos z) ∧ 0 < mL13 (Real.cos z) ∧ 0 < mL14 (Real.cos z))) ∧
      -- (7) I_eq = R_eq
      (∀ (w : Fin 16 → ℝ × ℝ) (dt : ℝ), IsAdmissibleVariation z w dt →
        dt = 0 ∧ ∃ a b e : ℝ,
          w 0 = rigid a b e (p0 z) ∧ w 1 = rigid a b e (p1 z) ∧
          w 2 = rigid a b e (p2 z) ∧ w 3 = rigid a b e (p3 z) ∧
          w 4 = rigid a b e (p4 z) ∧ w 5 = rigid a b e (p5 z) ∧
          w 6 = rigid a b e (p6 z) ∧ w 7 = rigid a b e (p7 z) ∧
          w 8 = rigid a b e (p8 z) ∧ w 9 = rigid a b e (p9 z) ∧
          w 10 = rigid a b e (p10 z) ∧ w 11 = rigid a b e (p11 z) ∧
          w 12 = rigid a b e (p12 z) ∧ w 13 = rigid a b e (p13 z) ∧
          w 14 = rigid a b e (p14 z) ∧ w 15 = rigid a b e (p15 z)) := by
  obtain ⟨z, hF, hc, hs⟩ := exists_constructor_root_sin_pos
  have hcS : Real.cos z ∈ Set.Icc slo shi :=
    ⟨le_trans slo_le_clo (le_of_lt hc.1), le_trans (le_of_lt hc.2) chi_le_shi⟩
  have hFc : Fc (Real.cos z) = 0 := by rw [Fc_cos_eq_Ffun]; exact hF
  refine ⟨z, hF, hs, hc, ?_, all_sides_cyclic z hF, all_active_diameters z,
          diameter_eq_one z hF hc, fun i j h₁ h₂ => cross_pos z hs hc i j h₁ h₂,
          ⟨(multipliers_certified z hF hc).1, (multipliers_certified z hF hc).2.2⟩,
          ?_⟩
  · intro c' hc' hfc'
    exact Fc_root_unique_search hc' hcS hfc' hFc
  · rintro w dt ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
                 a15, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩
    exact kernel_is_rigid z hF hs hc w dt a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
      a12 a13 a14 a15 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13

end Chiquipoli
