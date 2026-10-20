/-
**Theorem 6.4 (an explicit radius), the argument — kernel-checked.**

The article's Theorem 6.4 says that an equilateral small hexadecagon `(q, m)`
with `m ≥ ℓ` whose distance to `A16`, measured modulo orientation-preserving
Euclidean motions, is below `6.63 × 10⁻⁴` is the image of `A16` under such a
motion. Its proof has two parts of different kinds: an argument valid for any
configuration satisfying certain certified inequalities, and those inequalities
at `A16`. This file formalises the first part, for an arbitrary `n` and an
arbitrary set of active diameters; `Instances/A16Radius.lean` discharges the
hypotheses at `A16`.

WHAT IS PROVED HERE.

  * `distMod`, the distance modulo motions of the article, with the infimum over
    motions shown to be attained (`distMod_attained`) — so it is the minimum the
    article writes.
  * `exists_optimal_motion`: the minimising motion, built explicitly (centroids
    for the translation, `θ = arg(a + ib)` for the rotation), together with the
    two first-order conditions `Σ ξᵢ = 0`, `Σ ⟪ξᵢ, J pᵢ⟫ = 0` that put the
    displacement orthogonal to the rigid motions. No compactness is used.
  * `radius_of_certificate`: the argument itself. Exact Taylor expansion of the
    squared constraints, the multiplier identity, coercivity on the complement
    of the motions, and the conclusion `m = ℓ ∧ Congruent q p`.

THE NORMALISATION. As everywhere in this development, the multiplier identity is
used in the squared formulation (`t = ℓ²`, objective `t`, gradients
`2(p_j − p_i)`): there the Taylor expansions of the constraints are exact and
their quadratic remainders are the nonnegative numbers `|Δξ|²`. The steps are
those of the article's proof; the constants are the ones of this normalisation
(`A` bounds `−αᵢ`, `Λ` bounds `λₑ` from below, `σ2` bounds `‖B̃h‖²/‖h‖²` on the
complement of the motions), and the radius condition reads
`16 r² (Λ² + A²) ≤ σ2 Λ²`.

The competitor is not assumed convex, nor labelled in any order: only its side
lengths and its active diameters enter, as in the article.
-/
import ChiquipoliLean.Theory.FeasibleMain
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder Finset

variable {n : ℕ} [NeZero n]

/-! ## Distance modulo motions -/

/-- The quantity minimised in the article's distance modulo motions:
`Σᵢ |g(qᵢ) − pᵢ|² + (m − ℓ)²` for the motion `g = gmove c`. -/
noncomputable def motionCost (q : Cfg n) (m : ℝ) (p : Cfg n) (l : ℝ) (c : ℝ × ℝ × ℝ) : ℝ :=
  (∑ i, nsq (gmove c (q i) - p i)) + (m - l) ^ 2

/-- The distance modulo orientation-preserving Euclidean motions. -/
noncomputable def distMod (q : Cfg n) (m : ℝ) (p : Cfg n) (l : ℝ) : ℝ :=
  Real.sqrt (sInf (Set.range (motionCost q m p l)))

/-! ## Elementary algebra -/

omit [NeZero n] in
lemma gmove_eq (c : ℝ × ℝ × ℝ) (x : ℝ × ℝ) : gmove c x = (c.1, c.2.1) + rot c.2.2 x := by
  simp [gmove, Prod.ext_iff]

omit [NeZero n] in
lemma rot_add (t : ℝ) (x y : ℝ × ℝ) : rot t (x + y) = rot t x + rot t y := by
  simp only [rot, Prod.ext_iff, Prod.fst_add, Prod.snd_add]; constructor <;> ring

/-- Rotation as an additive map, so that it commutes with finite sums. -/
noncomputable def rotHom (t : ℝ) : ℝ × ℝ →+ ℝ × ℝ where
  toFun := rot t
  map_zero' := by simp [rot]
  map_add' := rot_add t

omit [NeZero n] in
lemma rot_sum (t : ℝ) (f : Fin n → ℝ × ℝ) : rot t (∑ i, f i) = ∑ i, rot t (f i) :=
  map_sum (rotHom t) f univ

omit [NeZero n] in
lemma ip_sum_left (f : Fin n → ℝ × ℝ) (w : ℝ × ℝ) : ∑ i, ip (f i) w = ip (∑ i, f i) w := by
  simp only [ip, Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib, Finset.sum_mul]

omit [NeZero n] in
@[simp] lemma ip_zero_l (w : ℝ × ℝ) : ip 0 w = 0 := by simp [ip]

omit [NeZero n] in
lemma ip_J_self (x : ℝ × ℝ) : ip x (J x) = 0 := by
  simp only [ip, J]; ring

/-- The centroid of a configuration. -/
noncomputable def cen (q : Cfg n) : ℝ × ℝ :=
  ((n : ℝ)⁻¹ * ∑ i, (q i).1, (n : ℝ)⁻¹ * ∑ i, (q i).2)

lemma sum_sub_cen (q : Cfg n) : ∑ i, (q i - cen q) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    simp only [Prod.fst_sub, Prod.fst_zero]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    simp only [cen]; field_simp; ring
  · rw [Prod.snd_sum]
    simp only [Prod.snd_sub, Prod.snd_zero]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    simp only [cen]; field_simp; ring

/-! ## The optimal motion, constructed explicitly

For a fixed rotation the best translation matches the centroids; after that the
cost is `C − 2(a cos θ + b sin θ)` for two numbers `a`, `b` determined by the
centred configurations, which is minimised at `θ = arg(a + ib)`. No compactness
argument is needed. -/

/-- The scalar `a cos θ + b sin θ` is maximised at `θ = arg (a + i b)`, where in
addition `a sin θ = b cos θ`. -/
lemma arg_max (a b : ℝ) :
    a * Real.sin (Complex.arg ⟨a, b⟩) - b * Real.cos (Complex.arg ⟨a, b⟩) = 0 ∧
    ∀ t : ℝ, a * Real.cos t + b * Real.sin t ≤
      a * Real.cos (Complex.arg ⟨a, b⟩) + b * Real.sin (Complex.arg ⟨a, b⟩) := by
  set z : ℂ := ⟨a, b⟩ with hz
  by_cases h0 : z = 0
  · have ha : a = 0 := by have := congrArg Complex.re h0; simpa [hz] using this
    have hb : b = 0 := by have := congrArg Complex.im h0; simpa [hz] using this
    subst ha; subst hb
    exact ⟨by ring, fun t => by simp⟩
  · have hρ : 0 < ‖z‖ := norm_pos_iff.mpr h0
    have hρ2 : ‖z‖ ^ 2 = a ^ 2 + b ^ 2 := by
      rw [Complex.sq_norm, hz, Complex.normSq_mk]; ring
    have hc : Real.cos (Complex.arg z) = a / ‖z‖ := by rw [Complex.cos_arg h0]
    have hs : Real.sin (Complex.arg z) = b / ‖z‖ := by rw [Complex.sin_arg]
    rw [hc, hs]
    refine ⟨by field_simp; ring, fun t => ?_⟩
    have hval : a * (a / ‖z‖) + b * (b / ‖z‖) = ‖z‖ := by
      field_simp; nlinarith [hρ2]
    rw [hval]
    nlinarith [sq_nonneg (a * Real.sin t - b * Real.cos t), Real.sin_sq_add_cos_sq t,
      sq_nonneg (a * Real.cos t + b * Real.sin t - ‖z‖)]

/-- **The optimal motion.** For any two configurations there is a motion `c`
attaining the infimum of `motionCost`, and at it the displacement
`ξᵢ = g(qᵢ) − pᵢ` satisfies the two first-order conditions of the article:
`Σ ξᵢ = 0` and `Σ ⟪ξᵢ, J pᵢ⟫ = 0`, i.e. `ξ ⊥ R(p)`. -/
theorem exists_optimal_motion (q p : Cfg n) (m l : ℝ) :
    ∃ c : ℝ × ℝ × ℝ, (∀ c', motionCost q m p l c ≤ motionCost q m p l c') ∧
      (∑ i, (gmove c (q i) - p i)) = 0 ∧
      (∑ i, ip (gmove c (q i) - p i) (J (p i))) = 0 := by
  set Q : Fin n → ℝ × ℝ := fun i => q i - cen q with hQ
  set P : Fin n → ℝ × ℝ := fun i => p i - cen p with hP
  set a : ℝ := ∑ i, ((Q i).1 * (P i).1 + (Q i).2 * (P i).2) with ha
  set b : ℝ := ∑ i, ((Q i).1 * (P i).2 - (Q i).2 * (P i).1) with hb
  set θ : ℝ := Complex.arg ⟨a, b⟩ with hθ
  obtain ⟨hK1, hK2⟩ := arg_max a b
  rw [← hθ] at hK1 hK2
  have hQs : ∑ i, Q i = 0 := sum_sub_cen q
  have hPs : ∑ i, P i = 0 := sum_sub_cen p
  -- every motion, in centred form
  have hform : ∀ (c : ℝ × ℝ × ℝ) (i : Fin n), gmove c (q i) - p i =
      (rot c.2.2 (Q i) - P i) + ((c.1, c.2.1) + rot c.2.2 (cen q) - cen p) := by
    intro c i
    have : q i = Q i + cen q := by simp [hQ]
    rw [gmove_eq, this, rot_add]
    simp only [hP]; abel
  -- the centred part sums to zero
  have hXs : ∀ t, ∑ i, (rot t (Q i) - P i) = 0 := by
    intro t; rw [Finset.sum_sub_distrib, ← rot_sum, hQs, hPs]; simp [rot]
  -- cost of the centred part, as a function of the angle
  have hcent : ∀ t, ∑ i, nsq (rot t (Q i) - P i) =
      (∑ i, nsq (Q i)) + (∑ i, nsq (P i)) - 2 * (a * Real.cos t + b * Real.sin t) := by
    intro t
    have hpt : ∀ i, nsq (rot t (Q i) - P i) = nsq (Q i) + nsq (P i)
        - 2 * (Real.cos t * ((Q i).1 * (P i).1 + (Q i).2 * (P i).2)
              + Real.sin t * ((Q i).1 * (P i).2 - (Q i).2 * (P i).1)) := by
      intro i
      have h := Real.sin_sq_add_cos_sq t
      simp only [nsq, ip, rot, Prod.fst_sub, Prod.snd_sub]
      linear_combination ((Q i).1 ^ 2 + (Q i).2 ^ 2) * h
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ha, hb]
    ring
  -- the full cost is at least the centred cost
  have hlow : ∀ c : ℝ × ℝ × ℝ, (∑ i, nsq (rot c.2.2 (Q i) - P i)) ≤ ∑ i, nsq (gmove c (q i) - p i) := by
    intro c
    set d : ℝ × ℝ := (c.1, c.2.1) + rot c.2.2 (cen q) - cen p
    have : ∀ i, nsq (gmove c (q i) - p i) =
        nsq (rot c.2.2 (Q i) - P i) + 2 * ip (rot c.2.2 (Q i) - P i) d + nsq d := by
      intro i; rw [hform c i, nsq_add]
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ip_sum_left, hXs]
    simp only [ip_zero_l, mul_zero, add_zero]
    have := Finset.sum_nonneg (fun i (_ : i ∈ (univ : Finset (Fin n))) => nsq_nonneg d)
    linarith
  -- the optimal motion
  set c0 : ℝ × ℝ × ℝ := ((cen p - rot θ (cen q)).1, (cen p - rot θ (cen q)).2, θ) with hc0
  have hd0 : ((c0.1, c0.2.1) + rot c0.2.2 (cen q) - cen p) = 0 := by
    simp only [hc0]; ext <;> simp
  have hxi : ∀ i, gmove c0 (q i) - p i = rot θ (Q i) - P i := by
    intro i; rw [hform c0 i, hd0, add_zero]
  refine ⟨c0, ?_, ?_, ?_⟩
  · intro c'
    simp only [motionCost]
    have h1 : ∑ i, nsq (gmove c0 (q i) - p i) = ∑ i, nsq (rot θ (Q i) - P i) := by
      simp only [hxi]
    have h2 := hlow c'
    rw [h1, hcent θ]
    rw [hcent c'.2.2] at h2
    have := hK2 c'.2.2
    linarith
  · simp only [hxi]; exact hXs θ
  · simp only [hxi]
    have hJ : ∀ i, ip (rot θ (Q i) - P i) (J (p i)) =
        ip (rot θ (Q i) - P i) (J (cen p))
        + (Real.sin θ * ((Q i).1 * (P i).1 + (Q i).2 * (P i).2)
           - Real.cos θ * ((Q i).1 * (P i).2 - (Q i).2 * (P i).1)) := by
      intro i
      have : p i = P i + cen p := by simp [hP]
      rw [this]
      simp only [ip, J, rot, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hJ i), Finset.sum_add_distrib, ip_sum_left, hXs θ]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← ha, ← hb]
    simp only [ip_zero_l]
    linarith [hK1]


/-! ## The infimum is a minimum -/

omit [NeZero n] in
lemma motionCost_nonneg (q : Cfg n) (m : ℝ) (p : Cfg n) (l : ℝ) (c : ℝ × ℝ × ℝ) :
    0 ≤ motionCost q m p l c :=
  add_nonneg (Finset.sum_nonneg fun _ _ => nsq_nonneg _) (sq_nonneg _)

/-- The infimum defining `distMod` is attained, so `distMod` is the minimum over
motions that the article writes. -/
theorem distMod_attained (q : Cfg n) (m : ℝ) (p : Cfg n) (l : ℝ) :
    ∃ c : ℝ × ℝ × ℝ, IsLeast (Set.range (motionCost q m p l)) (motionCost q m p l c) ∧
      distMod q m p l = Real.sqrt (motionCost q m p l c) := by
  obtain ⟨c, hmin, -, -⟩ := exists_optimal_motion q p m l
  have hleast : IsLeast (Set.range (motionCost q m p l)) (motionCost q m p l c) :=
    ⟨⟨c, rfl⟩, by rintro _ ⟨c', rfl⟩; exact hmin c'⟩
  exact ⟨c, hleast, by rw [distMod, hleast.csInf_eq]⟩

omit [NeZero n] in
lemma exists_cost_lt_of_distMod_lt {q : Cfg n} {m : ℝ} {p : Cfg n} {l r : ℝ}
    (h : distMod q m p l < r) : ∃ c, motionCost q m p l c < r ^ 2 := by
  have hr : 0 < r := lt_of_le_of_lt (Real.sqrt_nonneg _) h
  rw [distMod, Real.sqrt_lt' hr] at h
  obtain ⟨x, ⟨c, rfl⟩, hx⟩ := exists_lt_of_csInf_lt (Set.range_nonempty _) h
  exact ⟨c, hx⟩

/-! ## Two summation inequalities -/

lemma sum_nsq_succ (ξ : Cfg n) : ∑ i, nsq (ξ (i + 1)) = ∑ i, nsq (ξ i) :=
  Equiv.sum_comp (Equiv.addRight 1) (fun i => nsq (ξ i))

/-- `Σᵢ |ξᵢ₊₁ − ξᵢ|² ≤ 4 Σᵢ |ξᵢ|²`. -/
lemma sum_nsq_diff_le (ξ : Cfg n) : ∑ i, nsq (ξ (i + 1) - ξ i) ≤ 4 * cip ξ ξ := by
  have h : ∀ i, nsq (ξ (i + 1) - ξ i) ≤ 2 * nsq (ξ (i + 1)) + 2 * nsq (ξ i) := by
    intro i
    simp only [nsq, ip, Prod.fst_sub, Prod.snd_sub]
    nlinarith [sq_nonneg ((ξ (i + 1)).1 + (ξ i).1), sq_nonneg ((ξ (i + 1)).2 + (ξ i).2)]
  calc ∑ i, nsq (ξ (i + 1) - ξ i)
      ≤ ∑ i, (2 * nsq (ξ (i + 1)) + 2 * nsq (ξ i)) := Finset.sum_le_sum fun i _ => h i
    _ = 4 * cip ξ ξ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_nsq_succ]
      simp only [cip, nsq]; ring

omit [NeZero n] in
/-- For nonnegative terms, the sum of squares is at most the square of the sum. -/
lemma sum_sq_le_sq_sum {κ : Type*} [Fintype κ] (x : κ → ℝ) (hx : ∀ k, 0 ≤ x k) :
    ∑ k, x k ^ 2 ≤ (∑ k, x k) ^ 2 := by
  have h : ∀ k ∈ (univ : Finset κ), x k ^ 2 ≤ x k * ∑ j, x j := by
    intro k _
    have := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ k)
    nlinarith [hx k]
  calc ∑ k, x k ^ 2 ≤ ∑ k, x k * ∑ j, x j := Finset.sum_le_sum h
    _ = (∑ k, x k) ^ 2 := by rw [← Finset.sum_mul]; ring

/-! ## Theorem 6.4, abstractly

This is the proof of the article's Theorem 6.4, written in the squared
normalisation used throughout this development (`t = ℓ²`, objective `t`,
constraint gradients `2(p_j − p_i)`), for an arbitrary `n` and an arbitrary set of
active diameters. Its steps are the article's: the optimal motion puts
`h = (ξ, dt)` orthogonal to the rigid motions; the squared constraints are
quadratic, so their Taylor expansions are exact; the multiplier identity bounds
the diameter part of `Bh`; the coercivity of `B` on the complement of the
motions then forces `ξ = 0`.

The constants differ from the printed ones only because the normalisation
differs: `A` bounds `−αᵢ` (not `‖α‖₂`), `Λ` bounds the diameter multipliers
from below, `σ2` is a lower bound for `‖Bh‖²/‖h‖²` on the complement of the
motions, and the radius condition reads `16 r² (Λ² + A²) ≤ σ2 Λ²`. -/

variable {ι : Type*} [Fintype ι]

theorem radius_of_certificate (D : Data n ι) {p : Cfg n} {l : ℝ} (hl : 0 < l)
    (hp : D.p = p)
    (hs : ∀ i, D.s i = (2 : ℝ) • (p (i + 1) - p i))
    (hu : ∀ e, D.u e = (2 : ℝ) • (p (D.b e) - p (D.a e)))
    (hside : ∀ i, nsq (p (i + 1) - p i) = l ^ 2)
    (hdiam : ∀ e, nsq (p (D.b e) - p (D.a e)) = 1)
    {α : Fin n → ℝ} {lam : ι → ℝ} (hm : D.MultiplierIdentity 1 α lam)
    {A Λ σ2 r : ℝ} (hΛ : 0 < Λ) (hA : ∀ i, -A ≤ α i) (hlam : ∀ e, Λ ≤ lam e)
    (hcoer : ∀ (v : Cfg n) (dt : ℝ), (∀ w, D.R w → cip v w = 0) →
      σ2 * (cip v v + dt ^ 2) ≤ (∑ i, (D.sideD v dt i) ^ 2) + ∑ e, (D.diamD v e) ^ 2)
    (hrad : 16 * r ^ 2 * (Λ ^ 2 + A ^ 2) ≤ σ2 * Λ ^ 2)
    (q : Cfg n) (m : ℝ)
    (hqs : ∀ i, nsq (q (i + 1) - q i) = m ^ 2)
    (hqd : ∀ e, nsq (q (D.b e) - q (D.a e)) ≤ 1)
    (hlm : l ≤ m) (hdist : distMod q m p l < r) :
    m = l ∧ Congruent q p := by
  obtain ⟨c1, hc1⟩ := exists_cost_lt_of_distMod_lt hdist
  obtain ⟨c, hmin, hsum, hrot⟩ := exists_optimal_motion q p m l
  have hcost : motionCost q m p l c < r ^ 2 := lt_of_le_of_lt (hmin c1) hc1
  set ξ : Cfg n := fun i => gmove c (q i) - p i with hξ
  set dt : ℝ := m ^ 2 - l ^ 2 with hdt
  have hdt0 : 0 ≤ dt := by nlinarith
  have hN0 : 0 ≤ cip ξ ξ := Finset.sum_nonneg fun i _ => ip_self_nonneg _
  have hNr : cip ξ ξ < r ^ 2 := by
    have h1 : cip ξ ξ ≤ motionCost q m p l c := by
      have := sq_nonneg (m - l)
      simp only [motionCost, cip, nsq, hξ]; linarith
    linarith
  -- a motion preserves differences, and the moved competitor is `p + ξ`
  have hmove : ∀ i j, nsq ((p j + ξ j) - (p i + ξ i)) = nsq (q j - q i) := by
    intro i j
    simp only [hξ, add_sub_cancel]
    exact nsq_gmove_sub c (q j) (q i)
  -- `ξ ⊥ R(p)`
  have horth : ∀ w, D.R w → cip ξ w = 0 := by
    rintro w ⟨t, ω, hw⟩
    have hsplit : ∀ i, ip (ξ i) (w i) = ip (ξ i) t + ω * ip (ξ i) (J (p i)) := by
      intro i
      rw [hw i, hp]
      simp only [ip, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    simp only [cip]
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ i, ip (ξ i) t = ip (∑ i, ξ i) t := ip_sum_left ξ t
    rw [h1]
    have h2 : (∑ i, ξ i) = 0 := hsum
    have h3 : (∑ i, ip (ξ i) (J (p i))) = 0 := hrot
    rw [h2, h3]; simp
  -- exact Taylor expansion of the side constraints
  have hsideD : ∀ i, D.sideD ξ dt i = - nsq (ξ (i + 1) - ξ i) := by
    intro i
    have h1 := hmove i (i + 1)
    rw [hqs i] at h1
    have h2 : (p (i + 1) + ξ (i + 1)) - (p i + ξ i) = (p (i + 1) - p i) + (ξ (i + 1) - ξ i) := by
      abel
    rw [h2, nsq_add, hside i] at h1
    simp only [Data.sideD, hs i, ip_smul_left]
    rw [hdt]; linarith
  -- exact Taylor expansion of the active diameter constraints
  have hdiamD : ∀ e, D.diamD ξ e ≤ - nsq (ξ (D.b e) - ξ (D.a e)) := by
    intro e
    have h1 := hmove (D.a e) (D.b e)
    have h3 := hqd e
    rw [← h1] at h3
    have h2 : (p (D.b e) + ξ (D.b e)) - (p (D.a e) + ξ (D.a e)) =
        (p (D.b e) - p (D.a e)) + (ξ (D.b e) - ξ (D.a e)) := by abel
    rw [h2, nsq_add, hdiam e] at h3
    simp only [Data.diamD, hu e, ip_smul_left]
    linarith
  have hy0 : ∀ e, D.diamD ξ e ≤ 0 := fun e =>
    le_trans (hdiamD e) (neg_nonpos.mpr (nsq_nonneg _))
  have hs0 : ∀ i, 0 ≤ nsq (ξ (i + 1) - ξ i) := fun i => nsq_nonneg _
  set S : ℝ := ∑ i, nsq (ξ (i + 1) - ξ i) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hs0 i
  have hS4 : S ≤ 4 * cip ξ ξ := sum_nsq_diff_le ξ
  -- the multiplier identity at `(ξ, dt)`
  have hid := hm ξ dt
  simp only [hsideD, one_mul] at hid
  have hY1 : ∑ e, lam e * (- D.diamD ξ e) = - dt + ∑ i, (- α i) * nsq (ξ (i + 1) - ξ i) := by
    have e1 : ∑ e, lam e * (- D.diamD ξ e) = - ∑ e, lam e * D.diamD ξ e := by
      rw [← Finset.sum_neg_distrib]; congr 1; ext e; ring
    have e2 : ∑ i, (- α i) * nsq (ξ (i + 1) - ξ i) = ∑ i, α i * - nsq (ξ (i + 1) - ξ i) := by
      congr 1; ext i; ring
    rw [e1, e2]; linarith
  have hY2 : ∑ e, Λ * (- D.diamD ξ e) ≤ ∑ e, lam e * (- D.diamD ξ e) :=
    Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hlam e) (neg_nonneg.mpr (hy0 e))
  have hY3 : ∑ i, (- α i) * nsq (ξ (i + 1) - ξ i) ≤ ∑ i, A * nsq (ξ (i + 1) - ξ i) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (by linarith [hA i]) (hs0 i)
  set Y : ℝ := ∑ e, (- D.diamD ξ e) with hYdef
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun e _ => neg_nonneg.mpr (hy0 e)
  have hYb : Λ * Y ≤ A * S := by
    have : Λ * Y = ∑ e, Λ * (- D.diamD ξ e) := by rw [hYdef, Finset.mul_sum]
    have h' : ∑ i, A * nsq (ξ (i + 1) - ξ i) = A * S := by rw [hS, Finset.mul_sum]
    linarith
  -- the quadratic form at `h = (ξ, dt)`
  have hQ1 : ∑ i, (D.sideD ξ dt i) ^ 2 ≤ S ^ 2 := by
    have : ∑ i, (D.sideD ξ dt i) ^ 2 = ∑ i, (nsq (ξ (i + 1) - ξ i)) ^ 2 := by
      congr 1; ext i; rw [hsideD i]; ring
    rw [this, hS]; exact sum_sq_le_sq_sum _ hs0
  have hQ2 : ∑ e, (D.diamD ξ e) ^ 2 ≤ Y ^ 2 := by
    have : ∑ e, (D.diamD ξ e) ^ 2 = ∑ e, (- D.diamD ξ e) ^ 2 := by congr 1; ext e; ring
    rw [this, hYdef]; exact sum_sq_le_sq_sum _ fun e => neg_nonneg.mpr (hy0 e)
  have hQ : Λ ^ 2 * ((∑ i, (D.sideD ξ dt i) ^ 2) + ∑ e, (D.diamD ξ e) ^ 2)
      ≤ S ^ 2 * (Λ ^ 2 + A ^ 2) := by
    have hΛY : (Λ * Y) ^ 2 ≤ (A * S) ^ 2 := by
      have : 0 ≤ Λ * Y := mul_nonneg hΛ.le hY0
      nlinarith
    nlinarith [hQ1, hQ2, sq_nonneg Λ]
  have hco := hcoer ξ dt horth
  -- `r > 0` and `σ2 > 0`
  have hr : 0 < r := lt_of_le_of_lt (Real.sqrt_nonneg _) hdist
  have hA2 : 0 < Λ ^ 2 + A ^ 2 := by positivity
  have hΛ2 : 0 < Λ ^ 2 := by positivity
  have hσ : 0 < σ2 := by
    have h1 : 0 < 16 * r ^ 2 * (Λ ^ 2 + A ^ 2) := by positivity
    have h2 : 0 < σ2 * Λ ^ 2 := lt_of_lt_of_le h1 hrad
    exact pos_of_mul_pos_left h2 hΛ2.le
  -- the conclusion: `ξ = 0`
  have hN : cip ξ ξ = 0 := by
    by_contra hne
    have hNpos : 0 < cip ξ ξ := lt_of_le_of_ne hN0 (Ne.symm hne)
    have k0 : σ2 * cip ξ ξ ≤ σ2 * (cip ξ ξ + dt ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg dt]) hσ.le
    have k2 : S ^ 2 ≤ 16 * cip ξ ξ ^ 2 := by
      have := pow_le_pow_left₀ hS0 hS4 2
      calc S ^ 2 ≤ (4 * cip ξ ξ) ^ 2 := this
        _ = 16 * cip ξ ξ ^ 2 := by ring
    have k3 : cip ξ ξ * (σ2 * Λ ^ 2) ≤ cip ξ ξ * (16 * cip ξ ξ * (Λ ^ 2 + A ^ 2)) := by
      calc cip ξ ξ * (σ2 * Λ ^ 2) = Λ ^ 2 * (σ2 * cip ξ ξ) := by ring
        _ ≤ Λ ^ 2 * ((∑ i, (D.sideD ξ dt i) ^ 2) + ∑ e, (D.diamD ξ e) ^ 2) :=
          mul_le_mul_of_nonneg_left (le_trans k0 hco) hΛ2.le
        _ ≤ S ^ 2 * (Λ ^ 2 + A ^ 2) := hQ
        _ ≤ (16 * cip ξ ξ ^ 2) * (Λ ^ 2 + A ^ 2) := mul_le_mul_of_nonneg_right k2 hA2.le
        _ = cip ξ ξ * (16 * cip ξ ξ * (Λ ^ 2 + A ^ 2)) := by ring
    have k4 : σ2 * Λ ^ 2 ≤ 16 * cip ξ ξ * (Λ ^ 2 + A ^ 2) := le_of_mul_le_mul_left k3 hNpos
    have k5 : 16 * cip ξ ξ * (Λ ^ 2 + A ^ 2) < 16 * r ^ 2 * (Λ ^ 2 + A ^ 2) := by
      have := mul_lt_mul_of_pos_right hNr hA2
      linarith
    linarith
  have hξ0 : ξ = 0 := eq_zero_of_cip_self hN
  have h0 : ∀ i, ξ i = 0 := fun i => congrFun hξ0 i
  have hdt' : dt = 0 := by
    have h := hsideD 0
    have hz : nsq (0 : ℝ × ℝ) = 0 := nsq_eq_zero_iff.mpr rfl
    simp only [Data.sideD, h0, sub_self, ip_zero_right, zero_sub, hz, neg_zero,
      neg_eq_zero] at h
    exact h
  refine ⟨?_, c, ?_⟩
  · have hsq : m ^ 2 = l ^ 2 := by linarith
    exact (pow_left_inj₀ (by linarith) hl.le two_ne_zero).mp hsq
  · funext i
    show gmove c (q i) = p i
    exact sub_eq_zero.mp (h0 i)

end Chiquipoli.Feasible
