/-
Lemmas proved once, used by the certificate of Z64 (`generators/family/gen_z64.jl`).

Z64 is not of the form `(sin z · X(c), Y(c))` of the polygons A_n and Z32: four of
its vertices carry the unknown `y` (a square root), and `h = 1/2` enters as a
constant. Its coordinates are therefore enclosed directly, as functions of
`c = cos t` alone, with `sin t = √(1 − c²)` and `y = y₅₁(c) + √(radicand(c))`; the
lemmas below are what that needs beyond `Basic.lean`.
-/
import ChiquipoliFamily.Basic

set_option linter.unusedVariables false

namespace Chiquipoli.Family

open Chiquipoli.FirstOrder Chiquipoli.Feasible

/-- **A squared distance from vertex enclosures, plain coordinates.** With both
coordinates of both vertices enclosed with radius `r`, the squared distance is at
most an explicit bound. Every inactive pair of Z64 is an instance. -/
lemma sqd_ub0 {X0 X1 Y0 Y1 x0 x1 y0 y1 r : ℝ}
    (hx0 : |X0 - x0| ≤ r) (hx1 : |X1 - x1| ≤ r)
    (hy0 : |Y0 - y0| ≤ r) (hy1 : |Y1 - y1| ≤ r) :
    (X1 - X0) ^ 2 + (Y1 - Y0) ^ 2 ≤ (|x1 - x0| + 2 * r) ^ 2 + (|y1 - y0| + 2 * r) ^ 2 := by
  have hx := sq_le_of_close (sub_close hx0 hx1)
  have hy := sq_le_of_close (sub_close hy0 hy1)
  linarith

/-- An enclosure with radius `r` is an enclosure with any larger radius `s`. -/
lemma loose {x a r s : ℝ} (h : |x - a| ≤ r) (hrs : r ≤ s) : |x - a| ≤ s := h.trans hrs

/-- The square of `c` near `c₀`. -/
lemma sq_close {c c0 r : ℝ} (hr : |c - c0| ≤ r) :
    |c ^ 2 - c0 ^ 2| ≤ r * (2 * |c0| + r) := by
  have e : c ^ 2 - c0 ^ 2 = (c - c0) * ((c - c0) + 2 * c0) := by ring
  rw [e, abs_mul]
  have h2 : |(c - c0) + 2 * c0| ≤ r + 2 * |c0| := by
    calc |(c - c0) + 2 * c0| ≤ |c - c0| + |2 * c0| := abs_add_le _ _
      _ ≤ r + 2 * |c0| := by rw [abs_mul]; norm_num; linarith
  calc |c - c0| * |(c - c0) + 2 * c0| ≤ r * (r + 2 * |c0|) :=
        mul_le_mul hr h2 (abs_nonneg _) ((abs_nonneg _).trans hr)
    _ = r * (2 * |c0| + r) := by ring

/-- **A square root from an enclosure of its radicand.** If `u ≥ 0` is within `e` of
the square `s₀²` of a positive number, `√u` is within `e / s₀` of `s₀`. -/
lemma sqrt_close {u s0 e : ℝ} (hs0 : 0 < s0) (hu : 0 ≤ u) (h : |u - s0 ^ 2| ≤ e) :
    |Real.sqrt u - s0| ≤ e / s0 := by
  have hr := Real.sqrt_nonneg u
  have hsq := Real.sq_sqrt hu
  have key : |Real.sqrt u - s0| * (Real.sqrt u + s0) = |u - s0 ^ 2| := by
    have : u - s0 ^ 2 = (Real.sqrt u - s0) * (Real.sqrt u + s0) := by nlinarith [hsq]
    rw [this, abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt u + s0)]
  rw [le_div_iff₀ hs0]
  have h1 : |Real.sqrt u - s0| * s0 ≤ |Real.sqrt u - s0| * (Real.sqrt u + s0) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  linarith

/-- **The enclosure of a square root.** `u ≥ 0` within `EU` of `U₀`, `s₀ > 0`, and
`EU + |U₀ − s₀²| ≤ E` with `E / s₀ ≤ e`: then `√u` is within `e` of `s₀`. -/
lemma enc_sqrt {u U0 EU s0 E e : ℝ} (hu : 0 ≤ u) (h : |u - U0| ≤ EU) (hs0 : 0 < s0)
    (hE : EU + |U0 - s0 ^ 2| ≤ E) (he : E / s0 ≤ e) : |Real.sqrt u - s0| ≤ e := by
  have h1 : |u - s0 ^ 2| ≤ E := by
    have e1 : u - s0 ^ 2 = (u - U0) + (U0 - s0 ^ 2) := by ring
    rw [e1]
    exact (abs_add_le _ _).trans (by linarith)
  exact (sqrt_close hs0 hu h1).trans he

/-- `1 − c²` near `1 − c₀²`, for `c` near `c₀`: the radicand of `sin`. -/
lemma one_sub_sq_close {c c0 r : ℝ} (hr : |c - c0| ≤ r) :
    |(1 - c ^ 2) - (1 - c0 ^ 2)| ≤ r * (2 * |c0| + r) := by
  have e : (1 - c ^ 2) - (1 - c0 ^ 2) = -(c ^ 2 - c0 ^ 2) := by ring
  rw [e, abs_neg]
  exact sq_close hr

/-- Division by a quantity enclosed away from zero, from below: `div_close` for a negative
denominator. -/
lemma div_close_neg {x d xh dh r δ : ℝ} (hx : |x - xh| ≤ r) (hd : |d - dh| ≤ δ) (hneg : δ < -dh) :
    |x / d - xh / dh| ≤ (r * (-dh) + |xh| * δ) / ((-dh - δ) * (-dh)) := by
  have hx' : |-x - -xh| ≤ r := by rw [show -x - -xh = -(x - xh) by ring, abs_neg]; exact hx
  have hd' : |-d - -dh| ≤ δ := by rw [show -d - -dh = -(d - dh) by ring, abs_neg]; exact hd
  have h := div_close hx' hd' hneg
  calc |x / d - xh / dh| = |(-x) / (-d) - (-xh) / (-dh)| := by rw [neg_div_neg_eq, neg_div_neg_eq]
    _ ≤ (r * (-dh) + |-xh| * δ) / ((-dh - δ) * (-dh)) := h
    _ = (r * (-dh) + |xh| * δ) / ((-dh - δ) * (-dh)) := by rw [abs_neg]

/-- The radicand of a square root that is enclosed away from zero is nonnegative. -/
lemma nonneg_of_close {x xh r : ℝ} (h : |x - xh| ≤ r) (hr : r ≤ xh) : 0 ≤ x := by
  have := (abs_le.mp h).1
  linarith

/-! ## The four vertices of Z64 that no Henneberg step reaches

The vertices 14, 15, 49, 50 of Z64 each have one pinned neighbour (13, 16, 48, 51) and are
joined to each other by five more bars. No vertex addition by two bars reaches them, so they
are pinned as a unit (`block_pin`), and their stresses are solved as a unit (`cramer_lin`,
`blockA`). -/

/-- A vector orthogonal to a nonzero `u` is a multiple of `J u`. -/
lemma perp_smul {u w : ℝ × ℝ} (hu : u ≠ 0) (h : ip u w = 0) : ∃ α : ℝ, w = α • J u := by
  have hn : u.1 * u.1 + u.2 * u.2 ≠ 0 := by
    intro h0
    apply hu
    have h1 : u.1 = 0 := by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2]
    have h2 : u.2 = 0 := by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2]
    exact Prod.ext h1 h2
  refine ⟨(-u.2 * w.1 + u.1 * w.2) / (u.1 * u.1 + u.2 * u.2), ?_⟩
  simp only [ip] at h
  apply Prod.ext
  · simp only [J, Prod.smul_fst, smul_eq_mul]
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hn]
    linear_combination (-u.1) * h
  · simp only [J, Prod.smul_snd, smul_eq_mul]
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hn]
    linear_combination (-u.2) * h

/-- **Four vertices pinned as a unit.** Each of `a, b, c, d` has one bar to a pinned vertex
(`a', b', c', d'`, whose displacement is zero), and the bars `ab`, `ac`, `ad`, `cd` join them.
If the four coefficients below are nonzero, none of them moves. -/
lemma block_pin {Pa Pb Pc Pd Pa' Pb' Pc' Pd' wa wb wc wd : ℝ × ℝ}
    (hna : Pa - Pa' ≠ 0) (hnb : Pb - Pb' ≠ 0) (hnc : Pc - Pc' ≠ 0) (hnd : Pd - Pd' ≠ 0)
    (ha : ip (Pa - Pa') wa = 0) (hb : ip (Pb - Pb') wb = 0)
    (hc : ip (Pc - Pc') wc = 0) (hd : ip (Pd - Pd') wd = 0)
    (hab : ip (Pb - Pa) (wb - wa) = 0) (hac : ip (Pc - Pa) (wc - wa) = 0)
    (had : ip (Pd - Pa) (wd - wa) = 0) (hcd : ip (Pd - Pc) (wd - wc) = 0)
    (A1 : ip (Pb - Pa) (J (Pb - Pb')) ≠ 0) (A2 : ip (Pc - Pa) (J (Pc - Pc')) ≠ 0)
    (A3 : ip (Pd - Pa) (J (Pd - Pd')) ≠ 0)
    (K : ip (Pd - Pa) (J (Pa - Pa')) * ip (Pd - Pc) (J (Pd - Pd')) * ip (Pc - Pa) (J (Pc - Pc'))
        - ip (Pc - Pa) (J (Pa - Pa')) * ip (Pd - Pc) (J (Pc - Pc')) * ip (Pd - Pa) (J (Pd - Pd')) ≠ 0) :
    wa = 0 ∧ wb = 0 ∧ wc = 0 ∧ wd = 0 := by
  obtain ⟨xa, rfl⟩ := perp_smul hna ha
  obtain ⟨xb, rfl⟩ := perp_smul hnb hb
  obtain ⟨xc, rfl⟩ := perp_smul hnc hc
  obtain ⟨xd, rfl⟩ := perp_smul hnd hd
  have e : ∀ (u r s : ℝ × ℝ) (p q : ℝ), ip u (p • r - q • s) = p * ip u r - q * ip u s := by
    intro u r s p q; simp only [ip, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [e] at hab hac had hcd
  have h2 : xc * ip (Pc - Pa) (J (Pc - Pc')) = xa * ip (Pc - Pa) (J (Pa - Pa')) := by linarith
  have h3 : xd * ip (Pd - Pa) (J (Pd - Pd')) = xa * ip (Pd - Pa) (J (Pa - Pa')) := by linarith
  have h4 : xd * ip (Pd - Pc) (J (Pd - Pd')) = xc * ip (Pd - Pc) (J (Pc - Pc')) := by linarith
  have h1 : xb * ip (Pb - Pa) (J (Pb - Pb')) = xa * ip (Pb - Pa) (J (Pa - Pa')) := by linarith
  set A2' := ip (Pc - Pa) (J (Pc - Pc'))
  set A3' := ip (Pd - Pa) (J (Pd - Pd'))
  set B2' := ip (Pc - Pa) (J (Pa - Pa'))
  set B3' := ip (Pd - Pa) (J (Pa - Pa'))
  set A4' := ip (Pd - Pc) (J (Pd - Pd'))
  set B4' := ip (Pd - Pc) (J (Pc - Pc'))
  have hxa : xa = 0 := by
    have : (B3' * A4' * A2' - B2' * B4' * A3') * xa = 0 := by
      linear_combination (-(A4' * A2')) * h3 + (B4' * A3') * h2 + (A2' * A3') * h4
    exact (mul_eq_zero.mp this).resolve_left K
  have hxc : xc = 0 := by
    rw [hxa, zero_mul] at h2; exact (mul_eq_zero.mp h2).resolve_right A2
  have hxd : xd = 0 := by
    rw [hxa, zero_mul] at h3; exact (mul_eq_zero.mp h3).resolve_right A3
  have hxb : xb = 0 := by
    rw [hxa, zero_mul] at h1; exact (mul_eq_zero.mp h1).resolve_right A1
  subst hxa hxb hxc hxd
  simp

/-- **Cramer, linear in the known stress.** Scaling `cramer_bal` by `t`: a known force `t w`
is cancelled by the stresses `t · ((−w₁ b₂ + w₂ b₁)/D)` and `t · ((−w₂ a₁ + w₁ a₂)/D)`. -/
lemma cramer_lin {w1 w2 a1 a2 b1 b2 t : ℝ} (hD : a1 * b2 - a2 * b1 ≠ 0) :
    t * w1 + (t * (((-w1) * b2 + w2 * b1) / (a1 * b2 - a2 * b1))) * a1
        + (t * (((-w2) * a1 + w1 * a2) / (a1 * b2 - a2 * b1))) * b1 = 0 ∧
    t * w2 + (t * (((-w1) * b2 + w2 * b1) / (a1 * b2 - a2 * b1))) * a2
        + (t * (((-w2) * a1 + w1 * a2) / (a1 * b2 - a2 * b1))) * b2 = 0 := by
  obtain ⟨h1, h2⟩ := cramer_bal (F1 := w1) (F2 := w2) (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2) hD
  constructor
  · linear_combination t * h1
  · linear_combination t * h2

/-- **The vertex that closes the block.** With `x₁ = t ρ₁`, `σ = t ρσ` the stresses that solve
the vertex equation for the bar to the pinned neighbour and the bar `σ`, the vertex balances.
Here `A, B, C, D` are the four bar vectors at the vertex, `V = g C + h D`, `W = f B + j D`. -/
lemma blockA {A1 A2 B1 B2 C1 C2 D1 D2 t f g h j : ℝ}
    (hDV : A1 * (g * C2 + h * D2) - A2 * (g * C1 + h * D1) ≠ 0) :
    let V1 := g * C1 + h * D1; let V2 := g * C2 + h * D2
    let W1 := f * B1 + j * D1; let W2 := f * B2 + j * D2
    let DV := A1 * V2 - A2 * V1
    let σ := t * ((-(A1 * W2 - A2 * W1)) / DV); let x1 := t * ((-(W1 * V2 - W2 * V1)) / DV)
    x1 * A1 + (t * f) * B1 + (σ * g) * C1 + (σ * h + t * j) * D1 = 0 ∧
    x1 * A2 + (t * f) * B2 + (σ * g) * C2 + (σ * h + t * j) * D2 = 0 := by
  intro V1 V2 W1 W2 DV σ x1
  have hDV' : DV ≠ 0 := hDV
  have hx1 : x1 * DV = t * (-(W1 * V2 - W2 * V1)) := by simp only [x1]; field_simp
  have hσ : σ * DV = t * (-(A1 * W2 - A2 * W1)) := by simp only [σ]; field_simp
  have e1 : x1 * A1 + (t * f) * B1 + (σ * g) * C1 + (σ * h + t * j) * D1 = x1 * A1 + σ * V1 + t * W1 := by
    simp only [V1, W1]; ring
  have e2 : x1 * A2 + (t * f) * B2 + (σ * g) * C2 + (σ * h + t * j) * D2 = x1 * A2 + σ * V2 + t * W2 := by
    simp only [V2, W2]; ring
  rw [e1, e2]
  have k1 : (x1 * A1 + σ * V1 + t * W1) * DV = 0 := by
    simp only [DV]
    linear_combination A1 * hx1 + V1 * hσ
  have k2 : (x1 * A2 + σ * V2 + t * W2) * DV = 0 := by
    simp only [DV]
    linear_combination A2 * hx1 + V2 * hσ
  exact ⟨(mul_eq_zero.mp k1).resolve_right hDV', (mul_eq_zero.mp k2).resolve_right hDV'⟩

end Chiquipoli.Family
