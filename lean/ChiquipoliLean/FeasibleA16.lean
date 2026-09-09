/-
**The chain, closed: the certified `A16` coordinates imply local maximality.**

`FeasibleMain.lean` proves Theorem 3.5's blow-up half for an abstract
configuration satisfying hypotheses (i) and (ii). The rest of this development
certifies those hypotheses for `A16`. This file joins them, and the join is not
free: the two halves live in different normalisations.

THE NORMALISATION MISMATCH. `FirstOrderA16` works in the *squared* formulation —
the scalar variable is `t = ℓ²`, the objective is `t`, so `κ = 1` and every
constraint gradient is `2(p_j − p_i)` with no division by `ℓ`. `Feasible` works
with `ℓ` itself. The two differentials are therefore related by

  `(A16Data z).sideD v (2ℓη) i = eD p ℓ v η i`,   `(A16Data z).diamD v e = dD p v (a e) (b e)`

— the sides by the chain rule `d(ℓ²) = 2ℓ dℓ`, the diameters exactly. That is
the content of `A16_bridge`, and it is why `no_blowup_sequence_gen` carries the
scale factor `sc` rather than assuming `dataOf`.

WHAT IS ASSEMBLED. Feasibility of `A16` comes from `all_sides_cyclic` (the
sixteen side equalities), `diameter_eq_one` (no pair exceeds 1) and `cross_pos`
(strict convexity with the labelled cyclic order). Hypothesis (i) is
`A16_multiplier_identity` with `A16_lam_pos`; hypothesis (ii) is
`A16_Ieq_imp_R`. The slice needs two distinct vertices, which follows from a
diameter being exactly 1.
-/
import ChiquipoliLean.FeasibleMain
import ChiquipoliLean.Certificate
import ChiquipoliLean.FirstOrderA16
import ChiquipoliLean.Convexity
import ChiquipoliLean.Diameter
import ChiquipoliLean.Main

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder Filter Topology

/-! ## Dictionary between the two files' primitives -/

lemma sqd_eq_nsq (a b : ℝ × ℝ) : sqd a b = nsq (b - a) := by
  simp [sqd, nsq, ip, Prod.fst_sub, Prod.snd_sub]; ring

lemma cross_eq_cross (a b c : ℝ × ℝ) : cross a b c = _root_.Chiquipoli.cross a b c := by
  rw [cross_eq]; simp [_root_.Chiquipoli.cross]

lemma ip_twice_eq (a b w : ℝ × ℝ) : ip (twice a b) w = 2 * ip (b - a) w := by
  simp [ip, twice, Prod.fst_sub, Prod.snd_sub]; ring

lemma A16p_eq_P (z : ℝ) (i : Fin 16) : A16p z i = P i z := by
  fin_cases i <;> rfl

lemma nxt_eq_succ (i : Fin 16) : nxt i = i + 1 := by fin_cases i <;> rfl

lemma A16s_eq (z : ℝ) (i : Fin 16) : A16s z i = twice (A16p z i) (A16p z (i + 1)) := by
  fin_cases i <;> rfl

lemma A16u_eq (z : ℝ) (e : Fin 15) :
    A16u z e = twice (A16p z (A16a e)) (A16p z (A16b e)) := by
  fin_cases e <;> rfl

/-! ## The bridge between the two normalisations -/

/-- **The squared formulation's cone, from the `ℓ`-formulation's differentials.**
The side differentials differ by the chain-rule factor `2ℓ`; the diameter
differentials agree on the nose. -/
theorem A16_bridge (z l : ℝ) (v : Cfg 16) (eta : ℝ)
    (hs : ∀ i, eD (A16p z) l v eta i = 0)
    (hd : ∀ e, dD (A16p z) v (A16a e) (A16b e) ≤ 0) :
    (A16Data z).Keq v (2 * l * eta) := by
  constructor
  · intro i
    have h := hs i
    simp only [Data.sideD, A16Data, A16s_eq, ip_twice_eq]
    simp only [eD] at h
    linarith
  · intro e
    have h := hd e
    simp only [Data.diamD, A16Data, A16u_eq, ip_twice_eq]
    simp only [dD] at h
    linarith

/-! ## `A16` is feasible -/

/-- Half the constructor angle has positive sine, so the certified side length
`ℓ = 2 sin(z/2)` is positive. -/
lemma sin_half_pos {z : ℝ} (h0 : 0 < z) (hpi : z < Real.pi) : 0 < Real.sin (z / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- **`A16` lies in the feasible set**, in the paper's convex sense: strictly
convex with the labelled cyclic order, every diameter at most 1, every side
equal to `ℓ = 2 sin(z/2)`, and `ℓ > 0`. -/
theorem A16_isFeasibleConvex {z : ℝ} (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) (h0 : 0 < z) (hpi : z < Real.pi) :
    IsFeasibleConvex (A16p z, 2 * Real.sin (z / 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- strict convexity and the labelled cyclic order
    intro i j hji hjn
    rw [cross_eq_cross]
    simp only [A16p_eq_P, ← nxt_eq_succ i]
    exact cross_pos z hsz hcb i j hji (by rw [nxt_eq_succ]; exact hjn)
  · -- every diameter at most 1
    intro i j
    rw [dC, ← sqd_eq_nsq, sub_nonpos]
    simp only [A16p_eq_P]
    exact (diameter_eq_one z hF hcb).1 i j
  · -- every side equal to ℓ
    intro i
    rw [eC, ← sqd_eq_nsq, sub_eq_zero]
    simp only [A16p_eq_P, ← nxt_eq_succ]
    exact all_sides_cyclic z hF i
  · -- ℓ > 0
    have := sin_half_pos h0 hpi
    linarith

/-- The fifteen declared diameters are active at `A16`. -/
theorem A16_active {z : ℝ} (e : Fin 15) : dC (A16a e) (A16b e) (A16p z) = 0 := by
  rw [dC, ← sqd_eq_nsq, sub_eq_zero]
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ :=
    all_active_diameters z
  fin_cases e
  · exact d0
  · exact d1
  · exact d2
  · exact d3
  · exact d4
  · exact d5
  · exact d6
  · exact d7
  · exact d8
  · exact d9
  · exact d10
  · exact d11
  · exact d12
  · exact d13
  · exact d14

/-- Two vertices of `A16` are distinct — the pair whose diameter is exactly 1.
This is the nondegeneracy the local Euclidean slice consumes. -/
theorem A16_vertices_distinct {z : ℝ} (hF : Ffun z = 0)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) : A16p z 0 ≠ A16p z 7 := by
  intro hcon
  have h1 : sqd (P 0 z) (P 7 z) = 1 := (diameter_eq_one z hF hcb).2
  rw [sqd_eq_nsq] at h1
  simp only [← A16p_eq_P, ← hcon, sub_self] at h1
  simp [nsq, ip] at h1

/-! ## The chain, closed -/

/-- **`A16` is a strict local maximiser of the perimeter, modulo
orientation-preserving Euclidean motions.**

Every hypothesis is discharged from the certified data: the constructor root
exists in the bracket with `sin z > 0` (`RootExists`, `Convexity`), the
configuration is feasible (`A16_isFeasibleConvex`), the fifteen declared
diameters are active (`A16_active`), the multiplier identity holds with strictly
positive active multipliers (`A16_multiplier_identity`, `A16_lam_pos`), and
`I_eq ⊆ R_eq` (`A16_Ieq_imp_R`).

The conclusion is the paper's: in a neighbourhood of `A16`, every feasible
equilateral small polygon whose side length is at least `ℓ` has side length
exactly `ℓ` and is congruent to `A16` by an orientation-preserving Euclidean
motion. Since the perimeter is `16ℓ`, none has larger perimeter. -/
theorem A16_strict_local_max {z : ℝ} (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) (h0 : 0 < z) (hpi : z < Real.pi) :
    IsFeasibleConvex (A16p z, 2 * Real.sin (z / 2)) ∧
    ∀ᶠ y in 𝓝 ((A16p z, 2 * Real.sin (z / 2)) : Amb 16),
      IsFeasible y → 2 * Real.sin (z / 2) ≤ y.2 →
        Congruent y.1 (A16p z) ∧ y.2 = 2 * Real.sin (z / 2) := by
  have hfeas := A16_isFeasibleConvex hF hsz hcb h0 hpi
  have hl : (0 : ℝ) < 2 * Real.sin (z / 2) := hfeas.2.2.2
  refine ⟨hfeas, ?_⟩
  refine eventually_congruent_of_no_worse (ii := 0) (jj := 7) hl
    (A16_vertices_distinct hF hcb) (D := A16Data z) rfl
    (a := A16a) (b := A16b)
    (sc := 2 * (2 * Real.sin (z / 2))) (by linarith)
    (fun v eta hs hd => ?_)
    one_pos (A16_multiplier_identity z hF) (A16_lam_pos z hcb)
    (A16_Ieq_imp_R z hF hsz hcb) (fun i => hfeas.2.2.1 i) (fun e => A16_active e)
  exact A16_bridge z (2 * Real.sin (z / 2)) v eta hs hd

/-! ## The chain, closed unconditionally

`A16_strict_local_max` still carries `0 < z < π` as hypotheses, needed only to
know `sin(z/2) > 0`. The constructor root can be chosen there: it is produced as
`arccos c`, which lies in `[0, π]`, and `sin z > 0` rules out both endpoints. -/

/-- The constructor root, with its argument pinned to `(0, π)`. -/
theorem exists_A16_root_in_Ioo_pi :
    ∃ z : ℝ, Ffun z = 0 ∧ 0 < Real.sin z ∧ Real.cos z ∈ Set.Ioo clo chi ∧
      0 < z ∧ z < Real.pi := by
  obtain ⟨c, hc, hfc⟩ := Fc_root_exists
  have hlo : (-1 : ℝ) < c := by have := hc.1; unfold clo at this; linarith
  have hhi : c < 1 := by have := hc.2; unfold chi at this; linarith
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos hlo.le hhi.le
  have hsin : 0 < Real.sin (Real.arccos c) := by
    rw [Real.sin_arccos]; exact Real.sqrt_pos.mpr (by nlinarith)
  refine ⟨Real.arccos c, ?_, hsin, ?_, ?_, ?_⟩
  · rw [← Fc_cos_eq_Ffun, hcos, hfc]
  · rw [hcos]; exact hc
  · rcases (Real.arccos_nonneg c).lt_or_eq with h | h
    · exact h
    · exact absurd hsin (by rw [← h]; simp)
  · rcases (Real.arccos_le_pi c).lt_or_eq with h | h
    · exact h
    · exact absurd hsin (by rw [h]; simp)

/-- **THE CHAIN, CLOSED.**

There is a configuration — the one the rest of this package certifies, built
from the unique constructor root in the bracket — which is a strictly convex
equilateral small hexadecagon and a strict local maximiser of the perimeter
among feasible equilateral small hexadecagons, modulo orientation-preserving
Euclidean motions.

Every step from the certified coordinates to this conclusion is checked by the
kernel: the exact algebra of the constructor, the interval-free rational bounds
on the root, the sixteen side equalities and fifteen active diameters, strict
convexity with the labelled cyclic order, the multiplier identity with strictly
positive active multipliers, `I_eq ⊆ R_eq`, and — via `Feasible.lean` through
`FeasibleMain.lean` — the blow-up argument of Theorem 3.5 itself. -/
theorem A16_locally_maximal :
    ∃ z : ℝ, ∃ l : ℝ, 0 < l ∧
      -- the constructor root, and it is the only one in the search bracket
      Ffun z = 0 ∧ Real.cos z ∈ Set.Ioo clo chi ∧
      (∀ z' : ℝ, z' ∈ Set.Icc (0:ℝ) 1 → Real.cos z' ∈ Set.Icc slo shi →
        Ffun z' = 0 → z' = z) ∧
      -- the configuration it builds is a strictly convex equilateral small 16-gon
      IsFeasibleConvex (A16p z, l) ∧
      -- and it is a strict local maximiser, modulo Euclidean motions
      (∀ᶠ y in 𝓝 ((A16p z, l) : Amb 16),
        IsFeasible y → l ≤ y.2 → Congruent y.1 (A16p z) ∧ y.2 = l) ∧
      -- equivalently: no nearby feasible competitor has a larger side length
      (∀ᶠ y in 𝓝 ((A16p z, l) : Amb 16), IsFeasible y → y.2 ≤ l) := by
  obtain ⟨z, hF, hsz, hcb, h0, hpi⟩ := exists_A16_root_in_Ioo_pi
  obtain ⟨hfeas, hev⟩ := A16_strict_local_max hF hsz hcb h0 hpi
  -- `z ≤ 1`: cos is strictly decreasing on `[0, π]` and `cos 1 ≤ 5/9 < clo`.
  have hzr : z ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨h0.le, ?_⟩
    by_contra hgt
    push Not at hgt
    have hlt : Real.cos z < Real.cos 1 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi zero_le_one hpi.le hgt
    have h59 : Real.cos 1 ≤ 5 / 9 := Real.cos_one_le
    have := hcb.1
    unfold clo at this
    linarith
  have hzs : Real.cos z ∈ Set.Icc slo shi := by
    constructor
    · have := hcb.1; unfold clo at this; unfold slo; linarith
    · have := hcb.2; unfold chi at this; unfold shi; linarith
  refine ⟨z, 2 * Real.sin (z / 2), hfeas.2.2.2, hF, hcb,
    fun z' hz' hc' hf' => constructor_root_unique_in_search hz' hzr hc' hzs hf' hF,
    hfeas, hev, ?_⟩
  filter_upwards [hev] with y hy hf
  by_contra hlt
  push Not at hlt
  exact absurd (hy hf hlt.le).2 (ne_of_gt hlt)

end Chiquipoli.Feasible
