/-
# Fixed-point interval arithmetic, computable, with its soundness proved once

An `FI` is a pair of integers `lo ≤ hi` standing for the real interval
`[lo / 2^K, hi / 2^K]`, `K = 384`. Every operation is plain integer arithmetic,
so the kernel evaluates it with its GMP-accelerated `Nat`/`Int` primitives; every
operation rounds OUTWARD (floor for lower ends, ceiling for upper ends), and its
soundness lemma (`mem_add`, `mem_mul`, …) says that the true value stays inside.

This is what replaces, for large `n`, the one-lemma-per-fact `norm_num`
certificates of `ChiquipoliFamily/Basic.lean`: a check over thousands of pairs
is one Boolean computation, run by the kernel (`decide +kernel`), and one
soundness theorem turns its `true` into the real statement.
-/
import Mathlib

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

/-- The number of binary digits after the point. -/
def K : ℕ := 384

/-- `2^K` as an integer. -/
def S : ℤ := 2 ^ K

lemma S_pos : (0 : ℤ) < S := by unfold S; positivity

lemma S_cast : ((S : ℤ) : ℝ) = (2 : ℝ) ^ K := by unfold S; push_cast; rfl

lemma two_pow_K_pos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity

/-- A fixed-point interval `[lo / 2^K, hi / 2^K]`. -/
structure FI where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr, Inhabited

/-- The real number an integer stands for. -/
noncomputable def val (a : ℤ) : ℝ := (a : ℝ) / (2 : ℝ) ^ K

/-- `x` lies in the interval. -/
def FI.mem (x : ℝ) (I : FI) : Prop := val I.lo ≤ x ∧ x ≤ val I.hi

/-! ## Rounding -/

/-- `⌊a / 2^K⌋`. -/
def fl (a : ℤ) : ℤ := a / S

/-- `⌈a / 2^K⌉`. -/
def cl (a : ℤ) : ℤ := -((-a) / S)

lemma fl_le (a : ℤ) : ((fl a : ℤ) : ℝ) ≤ (a : ℝ) / (2 : ℝ) ^ K := by
  have h := Int.ediv_mul_le a (ne_of_gt S_pos)
  have h' : ((a / S : ℤ) : ℝ) * (S : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
  rw [S_cast] at h'
  rw [le_div_iff₀ two_pow_K_pos]
  exact h'

lemma le_cl (a : ℤ) : (a : ℝ) / (2 : ℝ) ^ K ≤ ((cl a : ℤ) : ℝ) := by
  have h := fl_le (-a)
  unfold fl at h
  unfold cl
  push_cast at h ⊢
  have : -((a : ℝ) / (2 : ℝ) ^ K) = (-(a : ℝ)) / (2 : ℝ) ^ K := by ring
  linarith

/-! ## Operations -/

namespace FI

/-- The integer `k`, exactly. -/
def ofInt (k : ℤ) : FI := ⟨k * S, k * S⟩

def add (a b : FI) : FI := ⟨a.lo + b.lo, a.hi + b.hi⟩

def neg (a : FI) : FI := ⟨-a.hi, -a.lo⟩

def sub (a b : FI) : FI := ⟨a.lo - b.hi, a.hi - b.lo⟩

def mul (a b : FI) : FI :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨fl (min (min p1 p2) (min p3 p4)), cl (max (max p1 p2) (max p3 p4))⟩

/-- `1 / x` for an interval of positive numbers; `none` otherwise. -/
def invPos (a : FI) : Option FI :=
  if 0 < a.lo then some ⟨(S * S) / a.hi, -((-(S * S)) / a.lo)⟩ else none

/-- `1 / x` for an interval that does not contain `0`; `none` otherwise. -/
def inv (a : FI) : Option FI :=
  if 0 < a.lo then a.invPos
  else if a.hi < 0 then (a.neg.invPos).map neg
  else none

/-- `x / y`, when `y` is enclosed away from `0`. -/
def div (a b : FI) : Option FI := (b.inv).map (mul a)

/-- Widen by `r / 2^K` on both sides. -/
def widen (a : FI) (r : ℤ) : FI := ⟨a.lo - r, a.hi + r⟩

/-- `I ⊆ J`. -/
def subset (I J : FI) : Bool := decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)

end FI

/-! ## Soundness -/

open FI

lemma val_add (a b : ℤ) : val (a + b) = val a + val b := by unfold val; push_cast; ring
lemma val_sub (a b : ℤ) : val (a - b) = val a - val b := by unfold val; push_cast; ring
lemma val_neg (a : ℤ) : val (-a) = -val a := by unfold val; push_cast; ring

lemma mem_ofInt (k : ℤ) : FI.mem (k : ℝ) (ofInt k) := by
  unfold FI.mem ofInt val
  have : ((k * S : ℤ) : ℝ) / (2 : ℝ) ^ K = k := by
    push_cast; rw [S_cast]; field_simp
  rw [this]; exact ⟨le_rfl, le_rfl⟩

lemma mem_add {x y : ℝ} {a b : FI} (hx : FI.mem x a) (hy : FI.mem y b) :
    FI.mem (x + y) (add a b) := by
  unfold FI.mem add at *
  simp only [val_add]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma mem_neg {x : ℝ} {a : FI} (hx : FI.mem x a) : FI.mem (-x) (neg a) := by
  unfold FI.mem neg at *
  simp only [val_neg]
  constructor <;> linarith [hx.1, hx.2]

lemma mem_sub {x y : ℝ} {a b : FI} (hx : FI.mem x a) (hy : FI.mem y b) :
    FI.mem (x - y) (sub a b) := by
  unfold FI.mem sub at *
  simp only [val_sub]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- A product lies between the extreme corner products. -/
lemma mul_between {x y a b c d : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  -- x * y lies between a * y and b * y, and each of those between two corners
  have hxy : min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
    rcases le_total 0 y with hy | hy
    · exact ⟨min_le_left _ _ |>.trans (mul_le_mul_of_nonneg_right hx1 hy),
        (mul_le_mul_of_nonneg_right hx2 hy).trans (le_max_right _ _)⟩
    · exact ⟨min_le_right _ _ |>.trans (mul_le_mul_of_nonpos_right hx2 hy),
        (mul_le_mul_of_nonpos_right hx1 hy).trans (le_max_left _ _)⟩
  have hay : min (a * c) (a * d) ≤ a * y ∧ a * y ≤ max (a * c) (a * d) := by
    rcases le_total 0 a with ha | ha
    · exact ⟨min_le_left _ _ |>.trans (mul_le_mul_of_nonneg_left hy1 ha),
        (mul_le_mul_of_nonneg_left hy2 ha).trans (le_max_right _ _)⟩
    · exact ⟨min_le_right _ _ |>.trans (mul_le_mul_of_nonpos_left hy2 ha),
        (mul_le_mul_of_nonpos_left hy1 ha).trans (le_max_left _ _)⟩
  have hby : min (b * c) (b * d) ≤ b * y ∧ b * y ≤ max (b * c) (b * d) := by
    rcases le_total 0 b with hb | hb
    · exact ⟨min_le_left _ _ |>.trans (mul_le_mul_of_nonneg_left hy1 hb),
        (mul_le_mul_of_nonneg_left hy2 hb).trans (le_max_right _ _)⟩
    · exact ⟨min_le_right _ _ |>.trans (mul_le_mul_of_nonpos_left hy2 hb),
        (mul_le_mul_of_nonpos_left hy1 hb).trans (le_max_left _ _)⟩
  constructor
  · calc min (min (a * c) (a * d)) (min (b * c) (b * d))
        ≤ min (a * y) (b * y) := min_le_min hay.1 hby.1
      _ ≤ x * y := hxy.1
  · calc x * y ≤ max (a * y) (b * y) := hxy.2
      _ ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := max_le_max hay.2 hby.2

lemma val_mul_scaled (p q : ℤ) : val p * val q = ((p * q : ℤ) : ℝ) / (2 : ℝ) ^ K / (2 : ℝ) ^ K := by
  unfold val; push_cast; field_simp

lemma mem_mul {x y : ℝ} {a b : FI} (hx : FI.mem x a) (hy : FI.mem y b) :
    FI.mem (x * y) (mul a b) := by
  obtain ⟨h1, h2⟩ := mul_between hx.1 hx.2 hy.1 hy.2
  simp only [val_mul_scaled] at h1 h2
  -- the corner products at the doubled scale
  set P1 := a.lo * b.lo; set P2 := a.lo * b.hi; set P3 := a.hi * b.lo; set P4 := a.hi * b.hi
  have hmin : ((min (min P1 P2) (min P3 P4) : ℤ) : ℝ) / (2 : ℝ) ^ K / (2 : ℝ) ^ K
      = min (min ((P1 : ℝ) / 2 ^ K / 2 ^ K) ((P2 : ℝ) / 2 ^ K / 2 ^ K))
            (min ((P3 : ℝ) / 2 ^ K / 2 ^ K) ((P4 : ℝ) / 2 ^ K / 2 ^ K)) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ K * (2 : ℝ) ^ K := by positivity
    simp only [div_div]
    push_cast
    rw [min_div_div_right hpos.le, min_div_div_right hpos.le, min_div_div_right hpos.le]
  have hmax : ((max (max P1 P2) (max P3 P4) : ℤ) : ℝ) / (2 : ℝ) ^ K / (2 : ℝ) ^ K
      = max (max ((P1 : ℝ) / 2 ^ K / 2 ^ K) ((P2 : ℝ) / 2 ^ K / 2 ^ K))
            (max ((P3 : ℝ) / 2 ^ K / 2 ^ K) ((P4 : ℝ) / 2 ^ K / 2 ^ K)) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ K * (2 : ℝ) ^ K := by positivity
    simp only [div_div]
    push_cast
    rw [max_div_div_right hpos.le, max_div_div_right hpos.le, max_div_div_right hpos.le]
  unfold FI.mem mul
  simp only
  constructor
  · have hf := fl_le (min (min P1 P2) (min P3 P4))
    unfold val
    calc ((fl (min (min P1 P2) (min P3 P4)) : ℤ) : ℝ) / (2 : ℝ) ^ K
        ≤ ((min (min P1 P2) (min P3 P4) : ℤ) : ℝ) / (2 : ℝ) ^ K / (2 : ℝ) ^ K :=
          div_le_div_of_nonneg_right hf two_pow_K_pos.le
      _ ≤ x * y := by rw [hmin]; exact h1
  · have hc := le_cl (max (max P1 P2) (max P3 P4))
    unfold val
    calc x * y ≤ ((max (max P1 P2) (max P3 P4) : ℤ) : ℝ) / (2 : ℝ) ^ K / (2 : ℝ) ^ K := by
          rw [hmax]; exact h2
      _ ≤ ((cl (max (max P1 P2) (max P3 P4)) : ℤ) : ℝ) / (2 : ℝ) ^ K :=
          div_le_div_of_nonneg_right hc two_pow_K_pos.le

lemma floor_div_le (p d : ℤ) (hd : 0 < d) : (((p / d : ℤ)) : ℝ) ≤ (p : ℝ) / d := by
  have h := Int.ediv_mul_le p (ne_of_gt hd)
  have h' : ((p / d : ℤ) : ℝ) * (d : ℝ) ≤ (p : ℝ) := by exact_mod_cast h
  rw [le_div_iff₀ (by exact_mod_cast hd)]; exact h'

lemma le_ceil_div (p d : ℤ) (hd : 0 < d) : (p : ℝ) / d ≤ (((-((-p) / d)) : ℤ) : ℝ) := by
  have h := floor_div_le (-p) d hd
  push_cast at h ⊢
  have : -((p : ℝ) / d) = (-(p : ℝ)) / d := by ring
  linarith

lemma mem_invPos {x : ℝ} {a I : FI} (hx : FI.mem x a) (h : a.invPos = some I) :
    FI.mem x⁻¹ I := by
  unfold invPos at h
  split_ifs at h with hlo
  cases h
  have hK := two_pow_K_pos
  have hlo' : (0 : ℝ) < (a.lo : ℝ) := by exact_mod_cast hlo
  have hx1 : (a.lo : ℝ) / (2 : ℝ) ^ K ≤ x := hx.1
  have hx2 : x ≤ (a.hi : ℝ) / (2 : ℝ) ^ K := hx.2
  have hx0 : 0 < x := lt_of_lt_of_le (div_pos hlo' hK) hx1
  have hhi' : (0 : ℝ) < (a.hi : ℝ) := by
    have := lt_of_lt_of_le hx0 hx2
    exact (div_pos_iff_of_pos_right hK).mp this
  have hhi : (0 : ℤ) < a.hi := by exact_mod_cast hhi'
  have hSS : ((S * S : ℤ) : ℝ) = (2 : ℝ) ^ K * (2 : ℝ) ^ K := by push_cast; rw [S_cast]
  unfold FI.mem val
  constructor
  · -- ⌊S²/hi⌋ / 2^K ≤ 2^K / hi ≤ 1/x
    have f := floor_div_le (S * S) a.hi hhi
    rw [hSS] at f
    calc (((S * S) / a.hi : ℤ) : ℝ) / (2 : ℝ) ^ K
        ≤ ((2 : ℝ) ^ K * (2 : ℝ) ^ K / (a.hi : ℝ)) / (2 : ℝ) ^ K :=
          div_le_div_of_nonneg_right f hK.le
      _ = ((a.hi : ℝ) / (2 : ℝ) ^ K)⁻¹ := by field_simp
      _ ≤ x⁻¹ := inv_anti₀ hx0 hx2
  · -- 1/x ≤ 2^K / lo ≤ ⌈S²/lo⌉ / 2^K
    have c := le_ceil_div (S * S) a.lo hlo
    rw [hSS] at c
    calc x⁻¹ ≤ ((a.lo : ℝ) / (2 : ℝ) ^ K)⁻¹ := inv_anti₀ (div_pos hlo' hK) hx1
      _ = ((2 : ℝ) ^ K * (2 : ℝ) ^ K / (a.lo : ℝ)) / (2 : ℝ) ^ K := by field_simp
      _ ≤ ((-((-(S * S)) / a.lo) : ℤ) : ℝ) / (2 : ℝ) ^ K :=
          div_le_div_of_nonneg_right c hK.le

lemma mem_inv {x : ℝ} {a I : FI} (hx : FI.mem x a) (h : a.inv = some I) : FI.mem x⁻¹ I := by
  unfold inv at h
  split_ifs at h with h1 h2
  · exact mem_invPos hx h
  · cases hJ : a.neg.invPos with
    | none => rw [hJ] at h; cases h
    | some J =>
      rw [hJ] at h
      simp only [Option.map_some] at h
      cases h
      have := mem_neg (mem_invPos (mem_neg hx) hJ)
      rwa [inv_neg, neg_neg] at this

lemma mem_div {x y : ℝ} {a b I : FI} (hx : FI.mem x a) (hy : FI.mem y b) (h : div a b = some I) :
    FI.mem (x / y) I := by
  unfold div at h
  cases hJ : b.inv with
  | none => rw [hJ] at h; cases h
  | some J =>
    rw [hJ] at h
    simp only [Option.map_some] at h
    cases h
    rw [div_eq_mul_inv]
    exact mem_mul hx (mem_inv hy hJ)

lemma mem_widen {x y : ℝ} {a : FI} {r : ℤ} (hx : FI.mem x a) (hr : |y - x| ≤ val r) :
    FI.mem y (a.widen r) := by
  unfold FI.mem FI.widen at *
  simp only [val_sub, val_add]
  have := abs_le.mp hr
  constructor <;> linarith [hx.1, hx.2, this.1, this.2]

lemma mem_of_subset {x : ℝ} {I J : FI} (hx : FI.mem x I) (h : I.subset J = true) : FI.mem x J := by
  unfold FI.subset at h
  simp only [decide_eq_true_eq] at h
  unfold FI.mem val at *
  have h1 : (J.lo : ℝ) ≤ I.lo := by exact_mod_cast h.1
  have h2 : (I.hi : ℝ) ≤ J.hi := by exact_mod_cast h.2
  constructor
  · exact (div_le_div_of_nonneg_right h1 two_pow_K_pos.le).trans hx.1
  · exact hx.2.trans (div_le_div_of_nonneg_right h2 two_pow_K_pos.le)

/-- Membership read as a distance to the midpoint. -/
lemma abs_sub_mid {x : ℝ} {a : FI} (hx : FI.mem x a) :
    |x - (val a.lo + val a.hi) / 2| ≤ (val a.hi - val a.lo) / 2 := by
  unfold FI.mem at hx
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

end Chiquipoli.Family.Trig
