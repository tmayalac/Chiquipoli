/-
**General lemmas for the Bingane–Audet family, proved once for every `n`.**

The A16 layer (`ChiquipoliLean/`) certifies every sign condition with one
Bernstein certificate per polynomial. That does not scale: at `n = 32` a single
support determinant is a degree-29 polynomial, one Bernstein certificate for it
costs 38 s and 2 GB, and there are 960 of them. The family layer splits the
work in two instead:

  * **polynomial layer, `O(n)` facts.** Each vertex coordinate polynomial is
    enclosed, `|XC_k(c) − x̂_k| ≤ ρ`, on a rational interval around the root,
    by a centred Taylor expansion (`tbound`). These are the only certificates
    that expand a polynomial.

  * **sign layer, `O(n²)` facts.** Every support determinant, every inactive
    distance and every rigidity determinant is bounded from those enclosures
    by the lemmas below, which are proved here once. Each instance is then
    rational arithmetic checked by `norm_num`.

The statements certified are the same as in the A16 layer; only their proofs
change. Nothing here depends on `n`.

The last section proves infinitesimal rigidity by a Henneberg construction:
pin one bar, then add vertices one at a time, each joined to two already-pinned
vertices by bars with independent directions. That replaces the dense
elimination over `Q[c]/(Fc)` that the A16 rank certificate performs (160 s and
13.6 GB at `n = 16`), with `n − 2` two-by-two determinants.
-/
import ChiquipoliLean.Theory.FeasibleMain

namespace Chiquipoli.Family

open Chiquipoli.FirstOrder Chiquipoli.Feasible

/-! ## Enclosures by centred Taylor expansion -/

/-- A point of `[lo, hi]` lies within `r` of `c0` whenever `[lo, hi] ⊆ [c0 − r, c0 + r]`. -/
lemma near_of {lo hi c0 r c : ℝ} (hlo : c0 - r ≤ lo) (hhi : hi ≤ c0 + r)
    (h₁ : lo ≤ c) (h₂ : c ≤ hi) : |c - c0| ≤ r := by
  rw [abs_le]; constructor <;> linarith

/-- One Taylor term is bounded, on both sides, by its worst case. -/
lemma tbound (d a c c0 r : ℝ) (k : ℕ) (hr : |c - c0| ≤ r) (ha : |d| ≤ a) :
    |d * (c - c0) ^ k| ≤ a * r ^ k := by
  rw [abs_mul, abs_pow]
  exact mul_le_mul ha (pow_le_pow_left₀ (abs_nonneg _) hr k) (by positivity)
    ((abs_nonneg d).trans ha)

/-! ## Error propagation from vertex enclosures -/

/-- Bilinear error propagation: if `|u − û| ≤ a` and `|v − v̂| ≤ b`, then `u v`
lies within `|û| b + |v̂| a + a b` of `û v̂`. -/
lemma bilin (u v uh vh a b : ℝ) (hu : |u - uh| ≤ a) (hv : |v - vh| ≤ b) :
    |u * v - uh * vh| ≤ |uh| * b + |vh| * a + a * b := by
  have e : u * v - uh * vh = uh * (v - vh) + vh * (u - uh) + (u - uh) * (v - vh) := by ring
  rw [e]
  have e1 : |uh * (v - vh)| ≤ |uh| * b := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hv (abs_nonneg _)
  have e2 : |vh * (u - uh)| ≤ |vh| * a := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
  have e3 : |(u - uh) * (v - vh)| ≤ a * b := by
    rw [abs_mul]; exact mul_le_mul hu hv (abs_nonneg _) ((abs_nonneg _).trans hu)
  calc |uh * (v - vh) + vh * (u - uh) + (u - uh) * (v - vh)|
      ≤ |uh * (v - vh)| + |vh * (u - uh)| + |(u - uh) * (v - vh)| := abs_add_three _ _ _
    _ ≤ _ := by linarith

/-- The difference of two enclosed values is enclosed with twice the radius. -/
lemma sub_close {X0 X1 x0 x1 r : ℝ} (h0 : |X0 - x0| ≤ r) (h1 : |X1 - x1| ≤ r) :
    |(X1 - X0) - (x1 - x0)| ≤ 2 * r := by
  have : (X1 - X0) - (x1 - x0) = (X1 - x1) - (X0 - x0) := by ring
  rw [this]
  calc _ ≤ |X1 - x1| + |X0 - x0| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **A determinant from vertex enclosures.** With all six coordinates enclosed
with radius `r`, the determinant `(X₁ − X₀)(Y₂ − Y₀) − (Y₁ − Y₀)(X₂ − X₀)` is at
least its value at the centres minus an explicit error. Proved once; every
support determinant and every rigidity determinant is an instance. -/
lemma det_lb {X0 X1 X2 Y0 Y1 Y2 x0 x1 x2 y0 y1 y2 r : ℝ}
    (hx0 : |X0 - x0| ≤ r) (hx1 : |X1 - x1| ≤ r) (hx2 : |X2 - x2| ≤ r)
    (hy0 : |Y0 - y0| ≤ r) (hy1 : |Y1 - y1| ≤ r) (hy2 : |Y2 - y2| ≤ r) :
    ((x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0))
      - (|x1 - x0| * (2 * r) + |y2 - y0| * (2 * r) + (2 * r) * (2 * r))
      - (|y1 - y0| * (2 * r) + |x2 - x0| * (2 * r) + (2 * r) * (2 * r))
    ≤ (X1 - X0) * (Y2 - Y0) - (Y1 - Y0) * (X2 - X0) := by
  have h1 := abs_le.mp (bilin _ _ _ _ _ _ (sub_close hx0 hx1) (sub_close hy0 hy2))
  have h2 := abs_le.mp (bilin _ _ _ _ _ _ (sub_close hy0 hy1) (sub_close hx0 hx2))
  linarith [h1.1, h2.2]

/-- An enclosed value squared is at most the square of its centre's modulus plus
the radius. -/
lemma sq_le_of_close {X x r : ℝ} (h : |X - x| ≤ r) : X ^ 2 ≤ (|x| + r) ^ 2 := by
  have hX : |X| ≤ |x| + r := by
    calc |X| = |(X - x) + x| := by ring_nf
      _ ≤ |X - x| + |x| := abs_add_le _ _
      _ ≤ _ := by linarith
  calc X ^ 2 = |X| ^ 2 := (sq_abs X).symm
    _ ≤ (|x| + r) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hX 2

/-- **A squared distance from vertex enclosures.** With `x = sin z · X(c)`,
`y = Y(c)` and `sin² z = 1 − c² ≤ S`, the squared distance of two vertices is at
most an explicit rational bound. Every inactive pair is an instance. -/
lemma sqd_ub {X0 X1 Y0 Y1 x0 x1 y0 y1 r S c : ℝ}
    (hx0 : |X0 - x0| ≤ r) (hx1 : |X1 - x1| ≤ r)
    (hy0 : |Y0 - y0| ≤ r) (hy1 : |Y1 - y1| ≤ r)
    (hS0 : 0 ≤ 1 - c ^ 2) (hS : 1 - c ^ 2 ≤ S) :
    (1 - c ^ 2) * (X1 - X0) ^ 2 + (Y1 - Y0) ^ 2
      ≤ S * (|x1 - x0| + 2 * r) ^ 2 + (|y1 - y0| + 2 * r) ^ 2 := by
  have hx := sq_le_of_close (sub_close hx0 hx1)
  have hy := sq_le_of_close (sub_close hy0 hy1)
  have hX2 : 0 ≤ (X1 - X0) ^ 2 := sq_nonneg _
  have : (1 - c ^ 2) * (X1 - X0) ^ 2 ≤ S * (|x1 - x0| + 2 * r) ^ 2 :=
    mul_le_mul hS hx hX2 (hS0.trans hS)
  linarith

/-! ## Geometry of the reduced form `(sin z · X, Y)` -/

/-- The squared distance of two points in reduced form, with `sin² z` eliminated. -/
lemma nsq_reduced (s c X0 Y0 X1 Y1 : ℝ) (hs : s ^ 2 = 1 - c ^ 2) :
    nsq ((s * X1, Y1) - (s * X0, Y0)) = (1 - c ^ 2) * (X1 - X0) ^ 2 + (Y1 - Y0) ^ 2 := by
  simp only [nsq, ip, Prod.mk_sub_mk]
  have : (s * X1 - s * X0) * (s * X1 - s * X0) = s ^ 2 * (X1 - X0) ^ 2 := by ring
  rw [this, hs]; ring

/-- The cross product of three points in reduced form: the factor `sin z` comes
straight out. -/
lemma cross_reduced (s X0 Y0 X1 Y1 X2 Y2 : ℝ) :
    cross (s * X0, Y0) (s * X1, Y1) (s * X2, Y2)
      = s * ((X1 - X0) * (Y2 - Y0) - (Y1 - Y0) * (X2 - X0)) := by
  rw [cross_eq]; ring

/-! ## Infinitesimal rigidity by a Henneberg construction -/

/-- A vector orthogonal to two independent vectors is zero. -/
lemma two_bar_zero {u₁ u₂ x : ℝ × ℝ} (h₁ : ip u₁ x = 0) (h₂ : ip u₂ x = 0)
    (hd : u₁.1 * u₂.2 - u₁.2 * u₂.1 ≠ 0) : x = 0 := by
  simp only [ip] at h₁ h₂
  have hx1 : (u₁.1 * u₂.2 - u₁.2 * u₂.1) * x.1 = 0 := by linear_combination u₂.2 * h₁ - u₁.2 * h₂
  have hx2 : (u₁.1 * u₂.2 - u₁.2 * u₂.1) * x.2 = 0 := by linear_combination u₁.1 * h₂ - u₂.1 * h₁
  exact Prod.ext (by simpa [hd] using hx1) (by simpa [hd] using hx2)

/-- An infinitesimal rigid motion leaves every bar length stationary. -/
lemma rigid_bar (P Q : ℝ × ℝ) (t : ℝ × ℝ) (ω : ℝ) :
    ip (Q - P) ((t + ω • J Q) - (t + ω • J P)) = 0 := by
  simp only [ip, J, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **Pinning the first bar.** A displacement that keeps the bar `P → Q` stationary
agrees at both endpoints with an infinitesimal rigid motion. -/
lemma pin_bar {P Q wP wQ : ℝ × ℝ} (hPQ : P ≠ Q) (hbar : ip (Q - P) (wQ - wP) = 0) :
    ∃ (t : ℝ × ℝ) (ω : ℝ), wP = t + ω • J P ∧ wQ = t + ω • J Q := by
  set d := Q - P with hd
  have hdd : 0 < d.1 ^ 2 + d.2 ^ 2 := by
    have hne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
    rcases (Prod.ext_iff.not.mp hne) |> not_and_or.mp with h | h
    · have : d.1 ≠ 0 := h
      positivity
    · have : d.2 ≠ 0 := h
      positivity
  set ω := ip (J d) (wQ - wP) / (d.1 ^ 2 + d.2 ^ 2) with hω
  refine ⟨wP - ω • J P, ω, by abel, ?_⟩
  -- the residual at `Q` is orthogonal to `d` and to `J d`, hence zero
  have key : wQ - (wP - ω • J P + ω • J Q) = 0 := by
    apply two_bar_zero (u₁ := d) (u₂ := J d)
    · have : wQ - (wP - ω • J P + ω • J Q) = (wQ - wP) - ω • J d := by
        simp only [hd, J, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        constructor <;> ring
      rw [this]
      simp only [ip, J, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at hbar ⊢
      linear_combination hbar
    · have : wQ - (wP - ω • J P + ω • J Q) = (wQ - wP) - ω • J d := by
        simp only [hd, J, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        constructor <;> ring
      rw [this, hω]
      simp only [ip, J, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      field_simp
      ring
    · simp only [J]; nlinarith [hdd]
  have := sub_eq_zero.mp key
  exact this

/-- One Henneberg step: a vertex joined by two stationary bars with independent
directions to two vertices that do not move, does not move. -/
lemma henneberg_step {Pk Pi Pj wk wi wj : ℝ × ℝ}
    (hbi : ip (Pk - Pi) (wk - wi) = 0) (hbj : ip (Pk - Pj) (wk - wj) = 0)
    (hi : wi = 0) (hj : wj = 0)
    (hd : (Pk - Pi).1 * (Pk - Pj).2 - (Pk - Pi).2 * (Pk - Pj).1 ≠ 0) : wk = 0 := by
  subst hi hj
  simp only [sub_zero] at hbi hbj
  exact two_bar_zero hbi hbj hd

/-- The same step with the determinant written in the reduced coordinates
`(sin z · X, Y)`: it is `sin z` times a polynomial determinant. -/
lemma det_reduced (s Xk Yk Xi Yi Xj Yj : ℝ) :
    ((s * Xk, Yk) - (s * Xi, Yi)).1 * ((s * Xk, Yk) - (s * Xj, Yj)).2
      - ((s * Xk, Yk) - (s * Xi, Yi)).2 * ((s * Xk, Yk) - (s * Xj, Yj)).1
      = s * ((Xi - Xk) * (Yj - Yk) - (Yi - Yk) * (Xj - Xk)) := by
  simp only [Prod.fst_sub, Prod.snd_sub]; ring

/-- `(2 sin (z/2))² = 2 − 2 cos z`: the squared side length in terms of `cos z`. -/
lemma sq_two_sin_half (z : ℝ) : (2 * Real.sin (z / 2)) ^ 2 = 2 - 2 * Real.cos z := by
  have h : Real.cos z = 2 * Real.cos (z / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hs := Real.sin_sq_add_cos_sq (z / 2)
  linear_combination 4 * hs + 2 * h

/-! ## From per-case facts to the hypotheses of Theorem 3.5 -/

section general
variable {n : ℕ} [NeZero n]

/-- `Small` needs only the pairs `i < j`: the squared distance is symmetric and
vanishes on the diagonal. -/
lemma small_of_lt {q : Cfg n} (h : ∀ i j : Fin n, i < j → dC i j q ≤ 0) : Small q := by
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact h i j hij
  · subst hij; simp [dC, nsq, ip]
  · have := h j i hij
    have e : dC i j q = dC j i q := by
      simp only [dC, nsq, ip, Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]; exact this

/-- The two families of bar constraints contained in `I_eq`, with the side length
cleared (it is nonzero). -/
lemma bars_of_Ieq {iota : Type*} {p : Cfg n} {l : ℝ} (hl : l ≠ 0) {a b : iota → Fin n}
    {w : Cfg n} (h : (dataOf p l a b).Ieq w 0) :
    (∀ i, ip (p (i + 1) - p i) (w (i + 1) - w i) = 0) ∧
    (∀ e, ip (p (b e) - p (a e)) (w (b e) - w (a e)) = 0) := by
  obtain ⟨hs, hd⟩ := h
  refine ⟨fun i => ?_, fun e => hd e⟩
  have h1 := hs i
  simp only [Data.sideD, dataOf, ip_smul_left, sub_zero] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd h2 (inv_ne_zero hl)
  · exact h2

/-- A bar constraint does not depend on the orientation of the bar. -/
lemma bar_flip {P Q wP wQ : ℝ × ℝ} (h : ip (Q - P) (wQ - wP) = 0) : ip (P - Q) (wP - wQ) = 0 := by
  simp only [ip, Prod.fst_sub, Prod.snd_sub] at h ⊢; linear_combination h

/-- Subtracting an infinitesimal rigid motion preserves a bar constraint. -/
lemma bar_sub_rigid {P Q wP wQ t : ℝ × ℝ} {ω : ℝ} (h : ip (Q - P) (wQ - wP) = 0) :
    ip (Q - P) ((wQ - (t + ω • J Q)) - (wP - (t + ω • J P))) = 0 := by
  have hr := rigid_bar P Q t ω
  simp only [ip, J, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at h hr ⊢
  linear_combination h - hr

/-- **The multiplier identity of `dataOf`, from stationarity in the squared
formulation.** If the weighted bar vectors balance at every vertex (for every
displacement `v`) and the side weights sum to `−1`, then `(ℓ·A, Λ)` is a
multiplier vector for the paper's data with objective coefficient `κ = ℓ`. The
diameter weights are unchanged, so their positivity carries over as it is. -/
lemma mult_of_stationary {iota : Type*} [Fintype iota] {p : Cfg n} {l : ℝ} (hl : l ≠ 0)
    (a b : iota → Fin n) (A : Fin n → ℝ) (Λ : iota → ℝ)
    (hstat : ∀ v : Cfg n, (∑ i, A i * ip (p (i + 1) - p i) (v (i + 1) - v i))
        + ∑ e, Λ e * ip (p (b e) - p (a e)) (v (b e) - v (a e)) = 0)
    (hsum : ∑ i, A i = -1) :
    (dataOf p l a b).MultiplierIdentity l (fun i => l * A i) Λ := by
  intro v η
  have h := hstat v
  simp only [Data.sideD, Data.diamD, dataOf, ip_smul_left]
  have e1 : ∀ i, l * A i * (l⁻¹ * ip (p (i + 1) - p i) (v (i + 1) - v i) - η)
      = A i * ip (p (i + 1) - p i) (v (i + 1) - v i) - l * η * A i := by
    intro i; field_simp
  simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
  linarith

end general

/-! ## Centred enclosure arithmetic

Every quantity below is carried as `|x − x̂| ≤ r` with rational `x̂`, `r`. The
generator computes the centres and radii exactly, rounds them outward, and each
step is one of these lemmas plus rational side conditions for `norm_num`. -/

lemma add_close {x y xh yh r s : ℝ} (hx : |x - xh| ≤ r) (hy : |y - yh| ≤ s) :
    |(x + y) - (xh + yh)| ≤ r + s := by
  have : (x + y) - (xh + yh) = (x - xh) + (y - yh) := by ring
  rw [this]; exact (abs_add_le _ _).trans (by linarith)

lemma sub_close' {x y xh yh r s : ℝ} (hx : |x - xh| ≤ r) (hy : |y - yh| ≤ s) :
    |(x - y) - (xh - yh)| ≤ r + s := by
  have : (x - y) - (xh - yh) = (x - xh) - (y - yh) := by ring
  rw [this]; exact (abs_sub _ _).trans (by linarith)

lemma neg_close {x xh r : ℝ} (hx : |x - xh| ≤ r) : |(-x) - (-xh)| ≤ r := by
  have : (-x) - (-xh) = -(x - xh) := by ring
  rw [this, abs_neg]; exact hx

lemma mul_close {x y xh yh r s : ℝ} (hx : |x - xh| ≤ r) (hy : |y - yh| ≤ s) :
    |x * y - xh * yh| ≤ |xh| * s + |yh| * r + r * s :=
  bilin x y xh yh r s hx hy

/-- Division by a quantity enclosed away from zero. -/
lemma div_close {x d xh dh r δ : ℝ} (hx : |x - xh| ≤ r) (hd : |d - dh| ≤ δ) (hpos : δ < dh) :
    |x / d - xh / dh| ≤ (r * dh + |xh| * δ) / ((dh - δ) * dh) := by
  have hdh : 0 < dh := lt_of_le_of_lt (abs_nonneg _ |>.trans hd) hpos
  have hdlo : dh - δ ≤ d := by have := (abs_le.mp hd).1; linarith
  have hd0 : 0 < d := lt_of_lt_of_le (by linarith) hdlo
  have e : x / d - xh / dh = ((x - xh) * dh - xh * (d - dh)) / (d * dh) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (mul_pos hd0 hdh)]
  have hnum : |(x - xh) * dh - xh * (d - dh)| ≤ r * dh + |xh| * δ := by
    calc |(x - xh) * dh - xh * (d - dh)| ≤ |(x - xh) * dh| + |xh * (d - dh)| := abs_sub _ _
      _ = |x - xh| * dh + |xh| * |d - dh| := by rw [abs_mul, abs_mul, abs_of_pos hdh]
      _ ≤ r * dh + |xh| * δ := by
        gcongr
  have hden : (dh - δ) * dh ≤ d * dh := mul_le_mul_of_nonneg_right hdlo hdh.le
  have hden0 : 0 < (dh - δ) * dh := mul_pos (by linarith) hdh
  calc |(x - xh) * dh - xh * (d - dh)| / (d * dh)
      ≤ (r * dh + |xh| * δ) / (d * dh) := by gcongr
    _ ≤ (r * dh + |xh| * δ) / ((dh - δ) * dh) := by
        have hr0 : 0 ≤ r := (abs_nonneg _).trans hx
        have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hd
        exact div_le_div_of_nonneg_left
          (add_nonneg (mul_nonneg hr0 hdh.le) (mul_nonneg (abs_nonneg _) hδ0)) hden0 hden

/-- Move the centre to a rational `b` and round the radius up to `s`. -/
lemma recenter {x a b r e s : ℝ} (h : |x - a| ≤ r) (he : |a - b| ≤ e) (hs : r + e ≤ s) :
    |x - b| ≤ s := by
  have : x - b = (x - a) + (a - b) := by ring
  rw [this]; exact (abs_add_le _ _).trans (by linarith)

lemma pos_of_close {x xh r : ℝ} (h : |x - xh| ≤ r) (hr : r < xh) : 0 < x := by
  have := (abs_le.mp h).1; linarith

lemma neg_of_close {x xh r : ℝ} (h : |x - xh| ≤ r) (hr : xh + r < 0) : x < 0 := by
  have := (abs_le.mp h).2; linarith

/-- **Cramer balances a vertex.** Given the known force `(F₁, F₂)` at a vertex and
two bar vectors `a`, `b` with `det(a, b) ≠ 0`, the two stresses given by Cramer's
rule cancel it. Every Henneberg vertex of the self-stress is an instance. -/
lemma cramer_bal {F1 F2 a1 a2 b1 b2 : ℝ} (hD : a1 * b2 - a2 * b1 ≠ 0) :
    F1 + ((-F1) * b2 + F2 * b1) / (a1 * b2 - a2 * b1) * a1
        + ((-F2) * a1 + F1 * a2) / (a1 * b2 - a2 * b1) * b1 = 0 ∧
    F2 + ((-F1) * b2 + F2 * b1) / (a1 * b2 - a2 * b1) * a2
        + ((-F2) * a1 + F1 * a2) / (a1 * b2 - a2 * b1) * b2 = 0 := by
  have hi : (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1)⁻¹ = 1 := mul_inv_cancel₀ hD
  simp only [div_eq_mul_inv]
  constructor
  · linear_combination (-F1) * hi
  · linear_combination (-F2) * hi

/-- **The pinned bar.** With the stress `−(G·u)/(u·u)` on a bar `u`, the net force
at its endpoint has no component along `u`. -/
lemma pin_bal {G1 G2 u1 u2 : ℝ} (hu : u1 * u1 + u2 * u2 ≠ 0) :
    (G1 + (-(G1 * u1 + G2 * u2)) / (u1 * u1 + u2 * u2) * u1) * u1
      + (G2 + (-(G1 * u1 + G2 * u2)) / (u1 * u1 + u2 * u2) * u2) * u2 = 0 := by
  have hi : (u1 * u1 + u2 * u2) * (u1 * u1 + u2 * u2)⁻¹ = 1 := mul_inv_cancel₀ hu
  simp only [div_eq_mul_inv]
  linear_combination (-(G1 * u1 + G2 * u2)) * hi

section general2
variable {n : ℕ} [NeZero n]

/-- `mult_of_stationary` with the side weights summing to any negative `S`: then
`(ℓ·A, Λ)` is a multiplier vector with objective coefficient `κ = −ℓ S > 0`. The
stress found by the Henneberg recursion is not normalised, so this is the form
the family layer uses. -/
lemma mult_of_stationary' {iota : Type*} [Fintype iota] {p : Cfg n} {l : ℝ} (hl : l ≠ 0)
    (a b : iota → Fin n) (A : Fin n → ℝ) (Λ : iota → ℝ) (S : ℝ)
    (hstat : ∀ v : Cfg n, (∑ i, A i * ip (p (i + 1) - p i) (v (i + 1) - v i))
        + ∑ e, Λ e * ip (p (b e) - p (a e)) (v (b e) - v (a e)) = 0)
    (hsum : ∑ i, A i = S) :
    (dataOf p l a b).MultiplierIdentity (-(l * S)) (fun i => l * A i) Λ := by
  intro v η
  have h := hstat v
  simp only [Data.sideD, Data.diamD, dataOf, ip_smul_left]
  have e1 : ∀ i, l * A i * (l⁻¹ * ip (p (i + 1) - p i) (v (i + 1) - v i) - η)
      = A i * ip (p (i + 1) - p i) (v (i + 1) - v i) - l * η * A i := by
    intro i; field_simp
  simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
  linarith

end general2

end Chiquipoli.Family
