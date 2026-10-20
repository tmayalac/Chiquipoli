/-
**Coercivity of the squared-normalisation Jacobian, from a rational certificate.**

`Theory/Radius.lean` needs a lower bound `σ2 (‖v‖² + dt²) ≤ ‖B̃(v, dt)‖²` for every
`v` orthogonal to the rigid motions. At `A16` the entries of `B̃` are irrational,
so the bound is obtained in three steps, each proved here in general:

  * `Qform`, the quadratic form of `B̃ᵀB̃ + VVᵀ` (`V` spanning the rigid motions),
    which on the complement of the motions is `‖B̃(v, dt)‖²` (`Qform_eq_of_orth`);
  * `Qform_perturb`: if every coordinate of `p` is within `ε` of a configuration
    `ph`, then `Qform p ≥ (1 − t) Qform ph − (1/t − 1)(128 + 128|ι| + 2n) ε² ‖v‖²`;
  * `gram_lower`: for a rational matrix `C`, an approximate `LDLᵀ` factorisation of
    `CᵀC − σ·Id` whose exact residual has absolute row sums at most `μ` gives
    `‖Cx‖² ≥ (σ − μ)‖x‖²`. The residual is computed in `ℚ`, so the instance checks
    it with `decide +kernel`: no rounding, no floating point.

`enclose_mul` and `enclose_one` turn rational brackets for `sin z` and for the
coordinate polynomials into the coordinatewise enclosures `Qform_perturb` uses.
-/
import ChiquipoliLean.Theory.FeasibleMain

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder Finset

variable {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι]

/-! ## The quadratic form `‖B̃ h‖² + ‖Vᵀ h‖²` -/

/-- Side row of the squared-normalisation Jacobian `B̃`, applied to `(v, dt)`. -/
def sideRow (p : Cfg n) (v : Cfg n) (dt : ℝ) (i : Fin n) : ℝ :=
  2 * ip (p (i + 1) - p i) (v (i + 1) - v i) - dt

omit [NeZero n] in
/-- Active diameter row of `B̃`, applied to `v`. -/
def diamRow (p : Cfg n) (a b : ι → Fin n) (v : Cfg n) (e : ι) : ℝ :=
  2 * ip (p (b e) - p (a e)) (v (b e) - v (a e))

/-- `‖B̃(v,dt)‖² + Σₖ ⟪v, τₖ⟫²`, where `τ₁, τ₂` are the translations and
`τ₃ = Jp` the rotation: the quadratic form of `B̃ᵀB̃ + VVᵀ`. -/
def Qform (p : Cfg n) (a b : ι → Fin n) (v : Cfg n) (dt : ℝ) : ℝ :=
  (∑ i, (sideRow p v dt i) ^ 2) + (∑ e, (diamRow p a b v e) ^ 2)
    + (∑ i, (v i).1) ^ 2 + (∑ i, (v i).2) ^ 2 + (∑ i, ip (v i) (J (p i))) ^ 2

/-- On the complement of the rigid motions the last three terms vanish, and the
form is `Σ sideD² + Σ diamD²` of the squared-normalisation data. -/
theorem Qform_eq_of_orth (D : Data n ι) {p : Cfg n} (hp : D.p = p)
    (hs : ∀ i, D.s i = (2 : ℝ) • (p (i + 1) - p i))
    (hu : ∀ e, D.u e = (2 : ℝ) • (p (D.b e) - p (D.a e)))
    (v : Cfg n) (dt : ℝ) (horth : ∀ w, D.R w → cip v w = 0) :
    Qform p D.a D.b v dt = (∑ i, (D.sideD v dt i) ^ 2) + ∑ e, (D.diamD v e) ^ 2 := by
  have h1 : cip v (fun _ => ((1 : ℝ), (0 : ℝ))) = 0 :=
    horth _ ⟨(1, 0), 0, fun i => by simp⟩
  have h2 : cip v (fun _ => ((0 : ℝ), (1 : ℝ))) = 0 :=
    horth _ ⟨(0, 1), 0, fun i => by simp⟩
  have h3 : cip v (fun i => J (p i)) = 0 :=
    horth _ ⟨(0, 0), 1, fun i => by simp [hp]⟩
  have e1 : (∑ i, (v i).1) = 0 := by
    rw [← h1]; simp [cip, ip]
  have e2 : (∑ i, (v i).2) = 0 := by
    rw [← h2]; simp [cip, ip]
  have e3 : (∑ i, ip (v i) (J (p i))) = 0 := h3
  have es : ∀ i, D.sideD v dt i = sideRow p v dt i := by
    intro i; simp [Data.sideD, sideRow, hs i, ip_smul_left]
  have ed : ∀ e, D.diamD v e = diamRow p D.a D.b v e := by
    intro e; simp [Data.diamD, diamRow, hu e, ip_smul_left]
  simp only [Qform, e1, e2, e3, es, ed]; ring

/-! ## Perturbation of the configuration -/

omit [NeZero n] in
/-- `(x + y)² ≥ (1 − t) x² − (1/t − 1) y²` for `0 < t`. -/
lemma sq_add_ge {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    (1 - t) * x ^ 2 - (1 / t - 1) * y ^ 2 ≤ (x + y) ^ 2 := by
  have key : (x + y) ^ 2 - ((1 - t) * x ^ 2 - (1 / t - 1) * y ^ 2) = (t * x + y) ^ 2 / t := by
    field_simp; ring
  have : 0 ≤ (t * x + y) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  linarith

omit [NeZero n] in
/-- Cauchy–Schwarz in `ℝ²`. -/
lemma ip_sq_le (x y : ℝ × ℝ) : ip x y ^ 2 ≤ nsq x * nsq y := by
  simp only [nsq, ip]
  nlinarith [sq_nonneg (x.1 * y.2 - x.2 * y.1)]

omit [NeZero n] in
lemma nsq_sub_le (x y : ℝ × ℝ) : nsq (x - y) ≤ 2 * nsq x + 2 * nsq y := by
  simp only [nsq, ip, Prod.fst_sub, Prod.snd_sub]
  nlinarith [sq_nonneg (x.1 + y.1), sq_nonneg (x.2 + y.2)]

omit [NeZero n] in
/-- If both coordinates of `e` and `e'` are at most `ε` in absolute value, then
`|e − e'|² ≤ 8ε²`. -/
lemma nsq_diff_le_eps {e e' : ℝ × ℝ} {ε : ℝ} (h : |e.1| ≤ ε ∧ |e.2| ≤ ε)
    (h' : |e'.1| ≤ ε ∧ |e'.2| ≤ ε) : nsq (e - e') ≤ 8 * ε ^ 2 := by
  simp only [nsq, ip, Prod.fst_sub, Prod.snd_sub]
  have a1 := abs_le.mp h.1; have a2 := abs_le.mp h.2
  have b1 := abs_le.mp h'.1; have b2 := abs_le.mp h'.2
  nlinarith [sq_nonneg (e.1 - e'.1), sq_nonneg (e.2 - e'.2)]

omit [NeZero n] in
lemma nsq_le_cip (v : Cfg n) (j : Fin n) : nsq (v j) ≤ cip v v :=
  Finset.single_le_sum (f := fun i => nsq (v i)) (fun _ _ => nsq_nonneg _) (Finset.mem_univ j)

/-- **Perturbation.** If every coordinate of `p` is within `ε` of the
corresponding coordinate of `ph`, the form at `p` is bounded below by the form at
`ph`, up to an error proportional to `ε² ‖v‖²`. -/
theorem Qform_perturb {p ph : Cfg n} (a b : ι → Fin n) {ε t : ℝ}
    (hε : ∀ i, |(p i - ph i).1| ≤ ε ∧ |(p i - ph i).2| ≤ ε) (ht0 : 0 < t) (ht1 : t < 1)
    (v : Cfg n) (dt : ℝ) :
    (1 - t) * Qform ph a b v dt
      - (1 / t - 1) * ((128 + 128 * (Fintype.card ι : ℝ) + 2 * n) * ε ^ 2 * cip v v)
      ≤ Qform p a b v dt := by
  set e : Cfg n := fun i => p i - ph i with he
  have hk : 0 ≤ 1 / t - 1 := by rw [sub_nonneg, le_div_iff₀ ht0]; linarith
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hε 0).1
  set N := cip v v
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => ip_self_nonneg _
  -- the three perturbed families of rows
  set ds : Fin n → ℝ := fun i => 2 * ip (e (i + 1) - e i) (v (i + 1) - v i)
  set dd : ι → ℝ := fun k => 2 * ip (e (b k) - e (a k)) (v (b k) - v (a k))
  set dr : ℝ := ∑ i, ip (v i) (J (e i))
  have rs : ∀ i, sideRow p v dt i = sideRow ph v dt i + ds i := by
    intro i; simp only [sideRow, ds, he, ip, Prod.fst_sub, Prod.snd_sub]; ring
  have rd : ∀ k, diamRow p a b v k = diamRow ph a b v k + dd k := by
    intro k; simp only [diamRow, dd, he, ip, Prod.fst_sub, Prod.snd_sub]; ring
  have rr : (∑ i, ip (v i) (J (p i))) = (∑ i, ip (v i) (J (ph i))) + dr := by
    simp only [dr, ← Finset.sum_add_distrib]
    congr 1; ext i; simp only [he, ip, J, Prod.fst_sub, Prod.snd_sub]; ring
  -- bounds on the perturbations
  have bs : ∑ i, ds i ^ 2 ≤ 128 * ε ^ 2 * N := by
    have hpt : ∀ i, ds i ^ 2 ≤ 32 * ε ^ 2 * (2 * nsq (v (i + 1)) + 2 * nsq (v i)) := by
      intro i
      have c1 := ip_sq_le (e (i + 1) - e i) (v (i + 1) - v i)
      have c2 := nsq_diff_le_eps (hε (i + 1)) (hε i)
      have c3 := nsq_sub_le (v (i + 1)) (v i)
      have c4 := nsq_nonneg (v (i + 1) - v i)
      have c5 := nsq_nonneg (e (i + 1) - e i)
      simp only [ds]
      calc (2 * ip (e (i + 1) - e i) (v (i + 1) - v i)) ^ 2
          = 4 * ip (e (i + 1) - e i) (v (i + 1) - v i) ^ 2 := by ring
        _ ≤ 4 * (nsq (e (i + 1) - e i) * nsq (v (i + 1) - v i)) := by linarith
        _ ≤ 4 * (8 * ε ^ 2 * nsq (v (i + 1) - v i)) := by
            have := mul_le_mul_of_nonneg_right c2 c4; linarith
        _ ≤ 32 * ε ^ 2 * (2 * nsq (v (i + 1)) + 2 * nsq (v i)) := by
            have := mul_le_mul_of_nonneg_left c3 (by positivity : (0:ℝ) ≤ 32 * ε ^ 2)
            linarith
    calc ∑ i, ds i ^ 2 ≤ ∑ i, 32 * ε ^ 2 * (2 * nsq (v (i + 1)) + 2 * nsq (v i)) :=
          Finset.sum_le_sum fun i _ => hpt i
      _ = 128 * ε ^ 2 * N := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          have := Equiv.sum_comp (Equiv.addRight (1 : Fin n)) (fun i => nsq (v i))
          simp only [Equiv.coe_addRight] at this
          rw [this]; simp only [N, cip, nsq]; ring
  have bd : ∑ k, dd k ^ 2 ≤ 128 * (Fintype.card ι : ℝ) * ε ^ 2 * N := by
    have hpt : ∀ k, dd k ^ 2 ≤ 128 * ε ^ 2 * N := by
      intro k
      have c1 := ip_sq_le (e (b k) - e (a k)) (v (b k) - v (a k))
      have c2 := nsq_diff_le_eps (hε (b k)) (hε (a k))
      have c3 := nsq_sub_le (v (b k)) (v (a k))
      have c4 := nsq_nonneg (v (b k) - v (a k))
      have c6 := nsq_le_cip v (b k)
      have c7 := nsq_le_cip v (a k)
      simp only [dd]
      calc (2 * ip (e (b k) - e (a k)) (v (b k) - v (a k))) ^ 2
          = 4 * ip (e (b k) - e (a k)) (v (b k) - v (a k)) ^ 2 := by ring
        _ ≤ 4 * (nsq (e (b k) - e (a k)) * nsq (v (b k) - v (a k))) := by linarith
        _ ≤ 4 * (8 * ε ^ 2 * nsq (v (b k) - v (a k))) := by
            have := mul_le_mul_of_nonneg_right c2 c4; linarith
        _ ≤ 4 * (8 * ε ^ 2 * (4 * N)) := by
            have : nsq (v (b k) - v (a k)) ≤ 4 * N := by linarith
            have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 8 * ε ^ 2)
            linarith
        _ = 128 * ε ^ 2 * N := by ring
    calc ∑ k, dd k ^ 2 ≤ ∑ _k : ι, 128 * ε ^ 2 * N := Finset.sum_le_sum fun k _ => hpt k
      _ = 128 * (Fintype.card ι : ℝ) * ε ^ 2 * N := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have br : dr ^ 2 ≤ 2 * n * ε ^ 2 * N := by
    have hdr : dr = (∑ i, (v i).1 * (- (e i).2)) + ∑ i, (v i).2 * (e i).1 := by
      simp only [dr, ip, J, ← Finset.sum_add_distrib]
    have w1 : ∑ i, (- (e i).2) ^ 2 ≤ n * ε ^ 2 := by
      calc ∑ i, (- (e i).2) ^ 2 ≤ ∑ _i : Fin n, ε ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have := abs_le.mp (hε i).2
            simp only [he] at this ⊢; nlinarith
        _ = n * ε ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have w2 : ∑ i, ((e i).1) ^ 2 ≤ n * ε ^ 2 := by
      calc ∑ i, ((e i).1) ^ 2 ≤ ∑ _i : Fin n, ε ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have := abs_le.mp (hε i).1
            simp only [he] at this ⊢; nlinarith
        _ = n * ε ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have cs1 := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => (v i).1) (fun i => - (e i).2)
    have cs2 := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => (v i).2) (fun i => (e i).1)
    have hv : (∑ i, (v i).1 ^ 2) + (∑ i, (v i).2 ^ 2) = N := by
      simp only [N, cip, ip, ← Finset.sum_add_distrib]; congr 1; ext i; ring
    have v1 : 0 ≤ ∑ i, (v i).1 ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have v2 : 0 ≤ ∑ i, (v i).2 ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [hdr]
    set S1 := ∑ i, (v i).1 * (- (e i).2)
    set S2 := ∑ i, (v i).2 * (e i).1
    have k1 : S1 ^ 2 ≤ (∑ i, (v i).1 ^ 2) * (n * ε ^ 2) :=
      le_trans cs1 (mul_le_mul_of_nonneg_left w1 v1)
    have k2 : S2 ^ 2 ≤ (∑ i, (v i).2 ^ 2) * (n * ε ^ 2) :=
      le_trans cs2 (mul_le_mul_of_nonneg_left w2 v2)
    have k3 : (S1 + S2) ^ 2 ≤ 2 * S1 ^ 2 + 2 * S2 ^ 2 := by nlinarith [sq_nonneg (S1 - S2)]
    have k4 : 2 * n * ε ^ 2 * N
        = 2 * ((∑ i, (v i).1 ^ 2) * (n * ε ^ 2)) + 2 * ((∑ i, (v i).2 ^ 2) * (n * ε ^ 2)) := by
      rw [← hv]; ring
    linarith
  -- assemble
  have hQp : Qform p a b v dt =
      (∑ i, (sideRow ph v dt i + ds i) ^ 2) + (∑ k, (diamRow ph a b v k + dd k) ^ 2)
        + (∑ i, (v i).1) ^ 2 + (∑ i, (v i).2) ^ 2 + ((∑ i, ip (v i) (J (ph i))) + dr) ^ 2 := by
    simp only [Qform, rs, rd, rr]
  have l1 : ∑ i, ((1 - t) * sideRow ph v dt i ^ 2 - (1 / t - 1) * ds i ^ 2)
      ≤ ∑ i, (sideRow ph v dt i + ds i) ^ 2 := Finset.sum_le_sum fun i _ => sq_add_ge ht0 _ _
  have l2 : ∑ k, ((1 - t) * diamRow ph a b v k ^ 2 - (1 / t - 1) * dd k ^ 2)
      ≤ ∑ k, (diamRow ph a b v k + dd k) ^ 2 := Finset.sum_le_sum fun k _ => sq_add_ge ht0 _ _
  have l3 := sq_add_ge ht0 (∑ i, ip (v i) (J (ph i))) dr
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at l1 l2
  rw [hQp]
  simp only [Qform]
  have tt : 0 ≤ t := ht0.le
  have q1 : 0 ≤ (∑ i, (v i).1) ^ 2 := sq_nonneg _
  have q2 : 0 ≤ (∑ i, (v i).2) ^ 2 := sq_nonneg _
  have m1 := mul_le_mul_of_nonneg_left bs hk
  have m2 := mul_le_mul_of_nonneg_left bd hk
  have m3 := mul_le_mul_of_nonneg_left br hk
  nlinarith [m1, m2, m3, l1, l2, l3, q1, q2]


/-! ## Enclosures of products

The vertex enclosures of the instance are of the form `x = sin z · X(cos z)` with
`sin z` and `X(cos z)` in rational brackets. -/

omit [NeZero n] in
/-- On `[s₁, s₂] × [X₁, X₂]` with `s₁ ≥ 0`, the product `sX` lies between the
extreme corner values; so it is within `ε` of `xh` once all four corners are. -/
lemma enclose_mul {s X s1 s2 X1 X2 xh ε : ℝ} (h0 : 0 ≤ s1) (hs1 : s1 ≤ s) (hs2 : s ≤ s2)
    (hX1 : X1 ≤ X) (hX2 : X ≤ X2)
    (c1 : |s1 * X1 - xh| ≤ ε) (c2 : |s2 * X1 - xh| ≤ ε)
    (c3 : |s1 * X2 - xh| ≤ ε) (c4 : |s2 * X2 - xh| ≤ ε) :
    |s * X - xh| ≤ ε := by
  have hs : 0 ≤ s := le_trans h0 hs1
  rw [abs_le] at c1 c2 c3 c4 ⊢
  have lo1 : s * X1 ≤ s * X := mul_le_mul_of_nonneg_left hX1 hs
  have hi1 : s * X ≤ s * X2 := mul_le_mul_of_nonneg_left hX2 hs
  constructor
  · rcases le_total 0 X1 with h | h
    · have : s1 * X1 ≤ s * X1 := mul_le_mul_of_nonneg_right hs1 h
      linarith [c1.1]
    · have : s2 * X1 ≤ s * X1 := by nlinarith
      linarith [c2.1]
  · rcases le_total 0 X2 with h | h
    · have : s * X2 ≤ s2 * X2 := mul_le_mul_of_nonneg_right hs2 h
      linarith [c4.2]
    · have : s * X2 ≤ s1 * X2 := by nlinarith
      linarith [c3.2]

omit [NeZero n] in
lemma enclose_one {Y Y1 Y2 yh ε : ℝ} (h1 : Y1 ≤ Y) (h2 : Y ≤ Y2)
    (c1 : |Y1 - yh| ≤ ε) (c2 : |Y2 - yh| ≤ ε) : |Y - yh| ≤ ε := by
  rw [abs_le] at c1 c2 ⊢
  constructor <;> linarith [c1.1, c2.2]

/-! ## A lower bound for a Gram form, certified in exact rationals

For a rational matrix `C` (rows `k`, columns `i`), a rational matrix `L`, a
nonnegative rational vector `d` and rationals `σ`, `μ`: if the residual
`E = CᵀC − σ·Id − L·diag(d)·Lᵀ` has every absolute row sum at most `μ`, then
`‖Cx‖² ≥ (σ − μ)‖x‖²` for every real `x`. The residual is computed in `ℚ`, so the
row sums can be checked by the kernel with no rounding. -/

/-- The residual of an approximate `LDLᵀ` factorisation of `CᵀC − σ·Id`. -/
def gramResidual {r m : ℕ} (C : Fin r → Fin m → ℚ) (L : Fin m → Fin m → ℚ) (d : Fin m → ℚ)
    (σ : ℚ) (i j : Fin m) : ℚ :=
  (∑ k, C k i * C k j) - (if i = j then σ else 0) - ∑ k, L i k * d k * L j k

omit [NeZero n] in
lemma gramResidual_symm {r m : ℕ} (C : Fin r → Fin m → ℚ) (L : Fin m → Fin m → ℚ)
    (d : Fin m → ℚ) (σ : ℚ) (i j : Fin m) :
    gramResidual C L d σ i j = gramResidual C L d σ j i := by
  unfold gramResidual
  have h1 : (∑ k, C k i * C k j) = ∑ k, C k j * C k i := by congr 1; ext k; ring
  have h2 : (∑ k, L i k * d k * L j k) = ∑ k, L j k * d k * L i k := by congr 1; ext k; ring
  have h3 : (if i = j then σ else 0) = (if j = i then σ else 0) := by
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [h1, h2, h3]

omit [NeZero n] in
theorem gram_lower {r m : ℕ} (C : Fin r → Fin m → ℚ) (L : Fin m → Fin m → ℚ) (d : Fin m → ℚ)
    (σ μ : ℚ) (hd : ∀ k, 0 ≤ d k) (hrow : ∀ i, ∑ j, |gramResidual C L d σ i j| ≤ μ)
    (x : Fin m → ℝ) :
    ((σ - μ : ℚ) : ℝ) * ∑ i, x i ^ 2 ≤ ∑ k, (∑ i, (C k i : ℝ) * x i) ^ 2 := by
  set E : Fin m → Fin m → ℝ := fun i j => (gramResidual C L d σ i j : ℝ) with hE
  have hEs : ∀ i j, E i j = E j i := fun i j => by simp only [hE, gramResidual_symm]
  have hErow : ∀ i, ∑ j, |E i j| ≤ (μ : ℝ) := by
    intro i
    have := hrow i
    have hc : ((∑ j, |gramResidual C L d σ i j| : ℚ) : ℝ) ≤ (μ : ℝ) := by exact_mod_cast this
    simpa [hE, Rat.cast_sum, Rat.cast_abs] using hc
  -- the Gram matrix, entrywise
  have hG : ∀ i j, (∑ k, (C k i : ℝ) * (C k j : ℝ)) =
      (if i = j then (σ : ℝ) else 0) + (∑ k, (L i k : ℝ) * (d k : ℝ) * (L j k : ℝ)) + E i j := by
    intro i j
    simp only [hE, gramResidual]
    push_cast
    split_ifs <;> ring
  -- expand the square
  have hsq : ∑ k, (∑ i, (C k i : ℝ) * x i) ^ 2
      = ∑ i, ∑ j, (∑ k, (C k i : ℝ) * (C k j : ℝ)) * (x i * x j) := by
    have : ∀ k, (∑ i, (C k i : ℝ) * x i) ^ 2
        = ∑ i, ∑ j, ((C k i : ℝ) * (C k j : ℝ)) * (x i * x j) := by
      intro k
      rw [sq, Finset.sum_mul_sum]
      congr 1; ext i; congr 1; ext j; ring
    rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_comm]
    congr 1; ext i
    rw [Finset.sum_comm]
    congr 1; ext j
    rw [Finset.sum_mul]
  rw [hsq]
  simp only [hG, add_mul, Finset.sum_add_distrib]
  -- the three pieces
  have p1 : ∑ i, ∑ j, (if i = j then (σ : ℝ) else 0) * (x i * x j) = (σ : ℝ) * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    congr 1; ext i
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have p2 : 0 ≤ ∑ i, ∑ j, (∑ k, (L i k : ℝ) * (d k : ℝ) * (L j k : ℝ)) * (x i * x j) := by
    have hin : ∀ i, ∑ j, (∑ k, (L i k : ℝ) * (d k : ℝ) * (L j k : ℝ)) * (x i * x j)
        = ∑ k, ∑ j, (L i k : ℝ) * (d k : ℝ) * (L j k : ℝ) * (x i * x j) := by
      intro i
      simp only [Finset.sum_mul]
      exact Finset.sum_comm
    have hk : ∀ k, ∑ i, ∑ j, (L i k : ℝ) * (d k : ℝ) * (L j k : ℝ) * (x i * x j)
        = (d k : ℝ) * (∑ i, (L i k : ℝ) * x i) ^ 2 := by
      intro k
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
    have : ∑ i, ∑ j, (∑ k, (L i k : ℝ) * (d k : ℝ) * (L j k : ℝ)) * (x i * x j)
        = ∑ k, (d k : ℝ) * (∑ i, (L i k : ℝ) * x i) ^ 2 := by
      rw [Finset.sum_congr rfl (fun i _ => hin i), Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => hk k)
    rw [this]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (by exact_mod_cast hd k) (sq_nonneg _)
  have p3 : -((μ : ℝ) * ∑ i, x i ^ 2) ≤ ∑ i, ∑ j, E i j * (x i * x j) := by
    have hpt : ∀ i j, -(|E i j| * (x i ^ 2 + x j ^ 2) / 2) ≤ E i j * (x i * x j) := by
      intro i j
      have h1 : |E i j * (x i * x j)| ≤ |E i j| * (x i ^ 2 + x j ^ 2) / 2 := by
        rw [abs_mul]
        have : |x i * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i - x j), sq_nonneg (x i + x j)]
        have := mul_le_mul_of_nonneg_left this (abs_nonneg (E i j))
        linarith
      linarith [neg_abs_le (E i j * (x i * x j))]
    have hsum : ∑ i, ∑ j, |E i j| * (x i ^ 2 + x j ^ 2) / 2
        = (∑ i, x i ^ 2 * ∑ j, |E i j|) / 2 + (∑ j, x j ^ 2 * ∑ i, |E i j|) / 2 := by
      have : ∀ i j, |E i j| * (x i ^ 2 + x j ^ 2) / 2
          = x i ^ 2 * |E i j| / 2 + x j ^ 2 * |E i j| / 2 := by intro i j; ring
      simp only [this, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
      congr 1
      rw [Finset.sum_comm]
    have hcol : ∀ j, ∑ i, |E i j| ≤ (μ : ℝ) := by
      intro j
      have : ∑ i, |E i j| = ∑ i, |E j i| := by congr 1; ext i; rw [hEs]
      rw [this]; exact hErow j
    have b1 : ∑ i, x i ^ 2 * ∑ j, |E i j| ≤ ∑ i, x i ^ 2 * (μ : ℝ) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hErow i) (sq_nonneg _)
    have b2 : ∑ j, x j ^ 2 * ∑ i, |E i j| ≤ ∑ j, x j ^ 2 * (μ : ℝ) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg _)
    have b3 : ∑ i, x i ^ 2 * (μ : ℝ) = (μ : ℝ) * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    have hlow : -(∑ i, ∑ j, |E i j| * (x i ^ 2 + x j ^ 2) / 2)
        ≤ ∑ i, ∑ j, E i j * (x i * x j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun j _ => hpt i j
    rw [hsum] at hlow
    linarith
  push_cast
  linarith

end Chiquipoli.Feasible
