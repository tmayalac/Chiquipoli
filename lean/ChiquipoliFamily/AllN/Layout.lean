/-
# Where the published constructor puts each point, for every `n = 16k`

`Term.lean` runs upstream's code symbolically (`abS n`), and the per-case
certificates let the kernel *compute* which term sits at each index. Here that
computation is done once, by hand, for a symbolic `k`: `vertexS_eq` says that
for `n = 16k` and `1 ≤ x < n`, `x ≠ n/2`, vertex `x` is `spec k x`, given by
arithmetic on `x`.

Iteration `I` of the loop (`1 ≤ I ≤ 2k − 1`) writes the four points
`q_I, r_I, u_I, t_I` and their mirror images `M(·)`, at eight indices. For
`I = 2s` these are

    q ↦ 8k−1−4s,  r ↦ 16k−1−4s,  u ↦ 16k−2−4s,  t ↦ 16k−4s,

and for `I = 2s+1` they are

    q ↦ 16k−3−4s,  r ↦ 8k−3−4s,  u ↦ 8k−4−4s,  t ↦ 8k−2−4s.

The mirror image `M(·)` is written at `n − j`. The twelve assignments before
the loop are iteration `0`, with `t_0` the origin. No index is written twice, so
the final array is described by the loop invariant `Inv`.

In `[1, 4k)` the index `x = 4s + c` holds `M` of the point `lowRole x`:
`t_{2s}, r_{2s}, u_{2s}, q_{2s+1}` for `c = 0, 1, 2, 3`. In `[4k, 8k)`, with
`d = 8k − 1 − x = 4s + c`, it holds `midRole d`:
`q_{2s}, t_{2s+1}, r_{2s+1}, u_{2s+1}`. Index `8k` holds `(0, 1)`, and
`[8k+1, 16k)` holds the mirror image of `[1, 8k)`.
-/
import ChiquipoliFamily.Interval.Shapes

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig.Layout

open Chiquipoli.Family.Trig Tm

/-! ## The layout -/

/-- The points of block `i`, with the block `0` written before the loop. -/
def Q (i : ℕ) : Tm × Tm := if i = 0 then tq0 else tq i
def Rr (i : ℕ) : Tm × Tm := if i = 0 then tr0 else tr i
def U (i : ℕ) : Tm × Tm := if i = 0 then tu0 else tu i
def T (i : ℕ) : Tm × Tm := if i = 0 then tOrigin else tt i

/-- The point whose mirror image sits at `x ∈ [1, 4k)`. -/
def lowRole (x : ℕ) : Tm × Tm :=
  if x % 4 = 0 then T (2 * (x / 4))
  else if x % 4 = 1 then Rr (2 * (x / 4))
  else if x % 4 = 2 then U (2 * (x / 4))
  else Q (2 * (x / 4) + 1)

/-- The point at `x = 8k − 1 − d ∈ [4k, 8k)`. -/
def midRole (d : ℕ) : Tm × Tm :=
  if d % 4 = 0 then Q (2 * (d / 4))
  else if d % 4 = 1 then T (2 * (d / 4) + 1)
  else if d % 4 = 2 then Rr (2 * (d / 4) + 1)
  else U (2 * (d / 4) + 1)

/-- The term at index `x` (for `1 ≤ x < 16k`). -/
def spec (k x : ℕ) : Tm × Tm :=
  if x < 4 * k then tM (lowRole x)
  else if x < 8 * k then midRole (8 * k - 1 - x)
  else if x = 8 * k then tTop
  else if 16 * k - x < 4 * k then lowRole (16 * k - x)
  else tM (midRole (8 * k - 1 - (16 * k - x)))

/-- The iteration that writes `x`. -/
def lowIt (x : ℕ) : ℕ := if x % 4 = 3 then 2 * (x / 4) + 1 else 2 * (x / 4)
def midIt (d : ℕ) : ℕ := if d % 4 = 0 then 2 * (d / 4) else 2 * (d / 4) + 1

def iterOf (k x : ℕ) : ℕ :=
  if x < 4 * k then lowIt x
  else if x < 8 * k then midIt (8 * k - 1 - x)
  else if 16 * k - x < 4 * k then lowIt (16 * k - x)
  else midIt (8 * k - 1 - (16 * k - x))

/-- `x` has been written by the end of iteration `i`. -/
abbrev written (k i x : ℕ) : Prop := x ≠ 0 ∧ x ≠ 8 * k ∧ x < 16 * k ∧ iterOf k x ≤ i

instance (k i x : ℕ) : Decidable (written k i x) := by unfold written; infer_instance

/-- The loop invariant: the arrays hold `spec` exactly where they have been written. -/
def Inv (k i : ℕ) (A : TArr × TArr) : Prop :=
  ∀ x, (A.1 x, A.2 x) = if written k i x then spec k x else (zero, zero)

/-! ## Eight assignments -/

/-- Four assignments and their mirror images, as the loop body writes them
(`μ = neg` for the first coordinate, `μ = id` for the second). -/
def upd8 (μ : Tm → Tm) (a : TArr) (n j1 j2 j3 j4 : ℕ) (V X2 X3 X4 : Tm) : TArr :=
  let a := setS a j1 V
  let a := setS a (n - j1) (μ (a j1))
  let a := setS a j2 (sub (a j1) X2)
  let a := setS a (n - j2) (μ (a j2))
  let a := setS a j3 (sub (a j1) X3)
  let a := setS a (n - j3) (μ (a j3))
  let a := setS a j4 (sub (a j1) X4)
  let a := setS a (n - j4) (μ (a j4))
  a

lemma bodyS_eq (n : ℕ) (a b : TArr) (i : ℕ) :
    bodyS n (a, b) i =
      (upd8 neg a n ((n / 2 - 1 + i * (3 * n / 2 - 2)) % n) ((n - 1 + i * (3 * n / 2 - 2)) % n)
          ((n - 2 + i * (3 * n / 2 - 2)) % n) ((n + i * (3 * n / 2 - 2)) % n) (tXa i)
          (mul (pm i) (s42 i)) (mul (pm i) (s43 i)) (mul (pm i) (s41 i)),
       upd8 id b n ((n / 2 - 1 + i * (3 * n / 2 - 2)) % n) ((n - 1 + i * (3 * n / 2 - 2)) % n)
          ((n - 2 + i * (3 * n / 2 - 2)) % n) ((n + i * (3 * n / 2 - 2)) % n) (tXb i)
          (mul (pm i) (c42 i)) (mul (pm i) (c43 i)) (mul (pm i) (c41 i))) := rfl

lemma upd8_apply (μ : Tm → Tm) (a : TArr) (n j1 j2 j3 j4 : ℕ) (V X2 X3 X4 : Tm)
    (h1 : j1 ≠ n - j1) (h2 : j1 ≠ j2) (h3 : j1 ≠ n - j2) (h4 : j1 ≠ j3) (h5 : j1 ≠ n - j3)
    (h6 : j1 ≠ j4) (x : ℕ) :
    upd8 μ a n j1 j2 j3 j4 V X2 X3 X4 x =
      if x = n - j4 then μ (sub V X4) else if x = j4 then sub V X4
      else if x = n - j3 then μ (sub V X3) else if x = j3 then sub V X3
      else if x = n - j2 then μ (sub V X2) else if x = j2 then sub V X2
      else if x = n - j1 then μ V else if x = j1 then V else a x := by
  simp only [upd8, setS, Function.update_apply, h1, h2, h3, h4, h5, h6, if_true, if_false]

/-! ## The arithmetic of the indices -/

lemma mod_of_eq {N n r c : ℕ} (h : N = r + n * c) (hr : r < n) : N % n = r := by
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- The four indices of iteration `2s`. -/
lemma idx_even (k s : ℕ) (hk : 1 ≤ k) (hs1 : 1 ≤ s) (hs : 2 * s ≤ 2 * k - 1) :
    (16 * k / 2 - 1 + 2 * s * (3 * (16 * k) / 2 - 2)) % (16 * k) = 8 * k - 1 - 4 * s ∧
    (16 * k - 1 + 2 * s * (3 * (16 * k) / 2 - 2)) % (16 * k) = 16 * k - 1 - 4 * s ∧
    (16 * k - 2 + 2 * s * (3 * (16 * k) / 2 - 2)) % (16 * k) = 16 * k - 2 - 4 * s ∧
    (16 * k + 2 * s * (3 * (16 * k) / 2 - 2)) % (16 * k) = 16 * k - 4 * s := by
  have e : 3 * (16 * k) / 2 - 2 = 24 * k - 2 := by omega
  rw [e]
  have hP : 2 * s * (24 * k - 2) + 4 * s = 16 * k * (3 * s) := by
    have h2 : 2 ≤ 24 * k := by omega
    zify [h2]; ring
  exact ⟨mod_of_eq (c := 3 * s) (by omega) (by omega), mod_of_eq (c := 3 * s) (by omega) (by omega),
    mod_of_eq (c := 3 * s) (by omega) (by omega), mod_of_eq (c := 3 * s) (by omega) (by omega)⟩

/-- The four indices of iteration `2s + 1`. -/
lemma idx_odd (k s : ℕ) (hk : 1 ≤ k) (hs : 2 * s + 1 ≤ 2 * k - 1) :
    (16 * k / 2 - 1 + (2 * s + 1) * (3 * (16 * k) / 2 - 2)) % (16 * k) = 16 * k - 3 - 4 * s ∧
    (16 * k - 1 + (2 * s + 1) * (3 * (16 * k) / 2 - 2)) % (16 * k) = 8 * k - 3 - 4 * s ∧
    (16 * k - 2 + (2 * s + 1) * (3 * (16 * k) / 2 - 2)) % (16 * k) = 8 * k - 4 - 4 * s ∧
    (16 * k + (2 * s + 1) * (3 * (16 * k) / 2 - 2)) % (16 * k) = 8 * k - 2 - 4 * s := by
  have e : 3 * (16 * k) / 2 - 2 = 24 * k - 2 := by omega
  rw [e]
  have hP : (2 * s + 1) * (24 * k - 2) + 4 * s + 2 = 16 * k * (3 * s + 1) + 8 * k := by
    have h2 : 2 ≤ 24 * k := by omega
    zify [h2]; ring
  have hc : 16 * k * (3 * s + 2) = 16 * k * (3 * s + 1) + 16 * k := by ring
  exact ⟨mod_of_eq (c := 3 * s + 1) (by omega) (by omega), mod_of_eq (c := 3 * s + 2) (by omega) (by omega),
    mod_of_eq (c := 3 * s + 2) (by omega) (by omega), mod_of_eq (c := 3 * s + 2) (by omega) (by omega)⟩

/-! ## Which iteration writes which index -/

lemma iterOf_even (k s x : ℕ) (hk : 1 ≤ k) (hs1 : 1 ≤ s) (hs : 2 * s ≤ 2 * k - 1)
    (hx0 : x ≠ 0) (hxh : x ≠ 8 * k) (hxn : x < 16 * k) :
    iterOf k x = 2 * s ↔ (x = 8 * k - 1 - 4 * s ∨ x = 16 * k - (8 * k - 1 - 4 * s) ∨
      x = 16 * k - 1 - 4 * s ∨ x = 16 * k - (16 * k - 1 - 4 * s) ∨
      x = 16 * k - 2 - 4 * s ∨ x = 16 * k - (16 * k - 2 - 4 * s) ∨
      x = 16 * k - 4 * s ∨ x = 16 * k - (16 * k - 4 * s)) := by
  unfold iterOf
  split_ifs with h1 h2 h3
  · unfold lowIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega
  · generalize hd : 8 * k - 1 - x = d; unfold midIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega
  · generalize hd : 16 * k - x = d; unfold lowIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega
  · generalize hd : 8 * k - 1 - (16 * k - x) = d; unfold midIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega

lemma iterOf_odd (k s x : ℕ) (hk : 1 ≤ k) (hs : 2 * s + 1 ≤ 2 * k - 1)
    (hx0 : x ≠ 0) (hxh : x ≠ 8 * k) (hxn : x < 16 * k) :
    iterOf k x = 2 * s + 1 ↔ (x = 16 * k - 3 - 4 * s ∨ x = 16 * k - (16 * k - 3 - 4 * s) ∨
      x = 8 * k - 3 - 4 * s ∨ x = 16 * k - (8 * k - 3 - 4 * s) ∨
      x = 8 * k - 4 - 4 * s ∨ x = 16 * k - (8 * k - 4 - 4 * s) ∨
      x = 8 * k - 2 - 4 * s ∨ x = 16 * k - (8 * k - 2 - 4 * s)) := by
  unfold iterOf
  split_ifs with h1 h2 h3
  · unfold lowIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega
  · generalize hd : 8 * k - 1 - x = d; unfold midIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega
  · generalize hd : 16 * k - x = d; unfold lowIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega
  · generalize hd : 8 * k - 1 - (16 * k - x) = d; unfold midIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega

lemma iterOf_zero (k x : ℕ) (hk : 1 ≤ k) (hx0 : x ≠ 0) (hxh : x ≠ 8 * k) (hxn : x < 16 * k) :
    iterOf k x = 0 ↔ (x = 8 * k - 1 ∨ x = 8 * k + 1 ∨ x = 16 * k - 1 ∨ x = 1 ∨ x = 16 * k - 2 ∨ x = 2) := by
  unfold iterOf
  split_ifs with h1 h2 h3
  · unfold lowIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega
  · generalize hd : 8 * k - 1 - x = d; unfold midIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega
  · generalize hd : 16 * k - x = d; unfold lowIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega
  · generalize hd : 8 * k - 1 - (16 * k - x) = d; unfold midIt; split_ifs <;> constructor <;> intro <;> first | contradiction | omega

lemma iterOf_lt (k x : ℕ) (hk : 1 ≤ k) (hx0 : x ≠ 0) (hxn : x < 16 * k) : iterOf k x ≤ 2 * k - 1 := by
  unfold iterOf
  split_ifs with h1 h2 h3
  · unfold lowIt; split_ifs <;> omega
  · generalize hd : 8 * k - 1 - x = d; unfold midIt; split_ifs <;> omega
  · generalize hd : 16 * k - x = d; unfold lowIt; split_ifs <;> omega
  · generalize hd : 8 * k - 1 - (16 * k - x) = d; unfold midIt; split_ifs <;> omega

/-! ## `spec` at the indices each iteration writes -/

lemma Q_pos {i : ℕ} (h : i ≠ 0) : Q i = tq i := by simp [Q, h]
lemma Rr_pos {i : ℕ} (h : i ≠ 0) : Rr i = tr i := by simp [Rr, h]
lemma U_pos {i : ℕ} (h : i ≠ 0) : U i = tu i := by simp [U, h]
lemma T_pos {i : ℕ} (h : i ≠ 0) : T i = tt i := by simp [T, h]

lemma lowRole_eq (s c : ℕ) (hc : c < 4) : lowRole (4 * s + c) =
    if c = 0 then T (2 * s) else if c = 1 then Rr (2 * s) else if c = 2 then U (2 * s) else Q (2 * s + 1) := by
  have h1 : (4 * s + c) % 4 = c := by omega
  have h2 : (4 * s + c) / 4 = s := by omega
  simp only [lowRole, h1, h2]

lemma midRole_eq (s c : ℕ) (hc : c < 4) : midRole (4 * s + c) =
    if c = 0 then Q (2 * s) else if c = 1 then T (2 * s + 1) else if c = 2 then Rr (2 * s + 1)
    else U (2 * s + 1) := by
  have h1 : (4 * s + c) % 4 = c := by omega
  have h2 : (4 * s + c) / 4 = s := by omega
  simp only [midRole, h1, h2]

/-- `spec` in the four ranges. -/
lemma spec_low (k x : ℕ) (h : x < 4 * k) : spec k x = tM (lowRole x) := by simp [spec, h]
lemma spec_mid (k x : ℕ) (h1 : 4 * k ≤ x) (h2 : x < 8 * k) : spec k x = midRole (8 * k - 1 - x) := by
  simp [spec, h2]; omega
lemma spec_up_low (k x : ℕ) (h1 : 8 * k < x) (h2 : 16 * k - x < 4 * k) : spec k x = lowRole (16 * k - x) := by
  unfold spec; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]
lemma spec_up_mid (k x : ℕ) (h1 : 8 * k < x) (h2 : 4 * k ≤ 16 * k - x) :
    spec k x = tM (midRole (8 * k - 1 - (16 * k - x))) := by
  unfold spec; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]


/-! ## `spec` at the eight indices of an iteration -/

lemma spec_even (k s : ℕ) (hk : 1 ≤ k) (hs1 : 1 ≤ s) (hs : 2 * s ≤ 2 * k - 1) :
    spec k (8 * k - 1 - 4 * s) = tq (2 * s) ∧ spec k (16 * k - (8 * k - 1 - 4 * s)) = tM (tq (2 * s)) ∧
    spec k (16 * k - 1 - 4 * s) = tr (2 * s) ∧ spec k (16 * k - (16 * k - 1 - 4 * s)) = tM (tr (2 * s)) ∧
    spec k (16 * k - 2 - 4 * s) = tu (2 * s) ∧ spec k (16 * k - (16 * k - 2 - 4 * s)) = tM (tu (2 * s)) ∧
    spec k (16 * k - 4 * s) = tt (2 * s) ∧ spec k (16 * k - (16 * k - 4 * s)) = tM (tt (2 * s)) := by
  have h2 : 2 * s ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spec_mid k _ (by omega) (by omega), show 8 * k - 1 - (8 * k - 1 - 4 * s) = 4 * s + 0 by omega,
      midRole_eq s 0 (by norm_num)]; simp [Q_pos h2]
  · rw [spec_up_mid k _ (by omega) (by omega),
      show 8 * k - 1 - (16 * k - (16 * k - (8 * k - 1 - 4 * s))) = 4 * s + 0 by omega,
      midRole_eq s 0 (by norm_num)]; simp [Q_pos h2]
  · rw [spec_up_low k _ (by omega) (by omega), show 16 * k - (16 * k - 1 - 4 * s) = 4 * s + 1 by omega,
      lowRole_eq s 1 (by norm_num)]; simp [Rr_pos h2]
  · rw [spec_low k _ (by omega), show 16 * k - (16 * k - 1 - 4 * s) = 4 * s + 1 by omega,
      lowRole_eq s 1 (by norm_num)]; simp [Rr_pos h2]
  · rw [spec_up_low k _ (by omega) (by omega), show 16 * k - (16 * k - 2 - 4 * s) = 4 * s + 2 by omega,
      lowRole_eq s 2 (by norm_num)]; simp [U_pos h2]
  · rw [spec_low k _ (by omega), show 16 * k - (16 * k - 2 - 4 * s) = 4 * s + 2 by omega,
      lowRole_eq s 2 (by norm_num)]; simp [U_pos h2]
  · rw [spec_up_low k _ (by omega) (by omega), show 16 * k - (16 * k - 4 * s) = 4 * s + 0 by omega,
      lowRole_eq s 0 (by norm_num)]; simp [T_pos h2]
  · rw [spec_low k _ (by omega), show 16 * k - (16 * k - 4 * s) = 4 * s + 0 by omega,
      lowRole_eq s 0 (by norm_num)]; simp [T_pos h2]

lemma spec_odd (k s : ℕ) (hk : 1 ≤ k) (hs : 2 * s + 1 ≤ 2 * k - 1) :
    spec k (16 * k - 3 - 4 * s) = tq (2 * s + 1) ∧ spec k (16 * k - (16 * k - 3 - 4 * s)) = tM (tq (2 * s + 1)) ∧
    spec k (8 * k - 3 - 4 * s) = tr (2 * s + 1) ∧ spec k (16 * k - (8 * k - 3 - 4 * s)) = tM (tr (2 * s + 1)) ∧
    spec k (8 * k - 4 - 4 * s) = tu (2 * s + 1) ∧ spec k (16 * k - (8 * k - 4 - 4 * s)) = tM (tu (2 * s + 1)) ∧
    spec k (8 * k - 2 - 4 * s) = tt (2 * s + 1) ∧ spec k (16 * k - (8 * k - 2 - 4 * s)) = tM (tt (2 * s + 1)) := by
  have h2 : 2 * s + 1 ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spec_up_low k _ (by omega) (by omega), show 16 * k - (16 * k - 3 - 4 * s) = 4 * s + 3 by omega,
      lowRole_eq s 3 (by norm_num)]; simp [Q_pos h2]
  · rw [spec_low k _ (by omega), show 16 * k - (16 * k - 3 - 4 * s) = 4 * s + 3 by omega,
      lowRole_eq s 3 (by norm_num)]; simp [Q_pos h2]
  · rw [spec_mid k _ (by omega) (by omega), show 8 * k - 1 - (8 * k - 3 - 4 * s) = 4 * s + 2 by omega,
      midRole_eq s 2 (by norm_num)]; simp [Rr_pos h2]
  · rw [spec_up_mid k _ (by omega) (by omega),
      show 8 * k - 1 - (16 * k - (16 * k - (8 * k - 3 - 4 * s))) = 4 * s + 2 by omega,
      midRole_eq s 2 (by norm_num)]; simp [Rr_pos h2]
  · rw [spec_mid k _ (by omega) (by omega), show 8 * k - 1 - (8 * k - 4 - 4 * s) = 4 * s + 3 by omega,
      midRole_eq s 3 (by norm_num)]; simp [U_pos h2]
  · rw [spec_up_mid k _ (by omega) (by omega),
      show 8 * k - 1 - (16 * k - (16 * k - (8 * k - 4 - 4 * s))) = 4 * s + 3 by omega,
      midRole_eq s 3 (by norm_num)]; simp [U_pos h2]
  · rw [spec_mid k _ (by omega) (by omega), show 8 * k - 1 - (8 * k - 2 - 4 * s) = 4 * s + 1 by omega,
      midRole_eq s 1 (by norm_num)]; simp [T_pos h2]
  · rw [spec_up_mid k _ (by omega) (by omega),
      show 8 * k - 1 - (16 * k - (16 * k - (8 * k - 2 - 4 * s))) = 4 * s + 1 by omega,
      midRole_eq s 1 (by norm_num)]; simp [T_pos h2]

/-! ## The loop invariant -/

/-- Iteration `I` preserves the invariant, given the eight indices it writes,
their `spec`, and the fact that they are exactly the indices of `iterOf = I`. -/
lemma inv_step (k I : ℕ) (hk : 1 ≤ k) (hI : 1 ≤ I) (a b : TArr) (hA : Inv k (I - 1) (a, b))
    (j1 j2 j3 j4 : ℕ)
    (i1 : (16 * k / 2 - 1 + I * (3 * (16 * k) / 2 - 2)) % (16 * k) = j1)
    (i2 : (16 * k - 1 + I * (3 * (16 * k) / 2 - 2)) % (16 * k) = j2)
    (i3 : (16 * k - 2 + I * (3 * (16 * k) / 2 - 2)) % (16 * k) = j3)
    (i4 : (16 * k + I * (3 * (16 * k) / 2 - 2)) % (16 * k) = j4)
    (d1 : j1 ≠ 16 * k - j1) (d2 : j1 ≠ j2) (d3 : j1 ≠ 16 * k - j2) (d4 : j1 ≠ j3) (d5 : j1 ≠ 16 * k - j3)
    (d6 : j1 ≠ j4)
    (hit : ∀ x, x ≠ 0 → x ≠ 8 * k → x < 16 * k → (iterOf k x = I ↔ (x = j1 ∨ x = 16 * k - j1 ∨
      x = j2 ∨ x = 16 * k - j2 ∨ x = j3 ∨ x = 16 * k - j3 ∨ x = j4 ∨ x = 16 * k - j4)))
    (hbd : j1 ≠ 0 ∧ j1 ≠ 8 * k ∧ j1 < 16 * k ∧ 16 * k - j1 ≠ 0 ∧ 16 * k - j1 ≠ 8 * k ∧ 16 * k - j1 < 16 * k ∧
      j2 ≠ 0 ∧ j2 ≠ 8 * k ∧ j2 < 16 * k ∧ 16 * k - j2 ≠ 0 ∧ 16 * k - j2 ≠ 8 * k ∧ 16 * k - j2 < 16 * k ∧
      j3 ≠ 0 ∧ j3 ≠ 8 * k ∧ j3 < 16 * k ∧ 16 * k - j3 ≠ 0 ∧ 16 * k - j3 ≠ 8 * k ∧ 16 * k - j3 < 16 * k ∧
      j4 ≠ 0 ∧ j4 ≠ 8 * k ∧ j4 < 16 * k ∧ 16 * k - j4 ≠ 0 ∧ 16 * k - j4 ≠ 8 * k ∧ 16 * k - j4 < 16 * k)
    (e1 : spec k j1 = tq I) (e2 : spec k (16 * k - j1) = tM (tq I))
    (e3 : spec k j2 = tr I) (e4 : spec k (16 * k - j2) = tM (tr I))
    (e5 : spec k j3 = tu I) (e6 : spec k (16 * k - j3) = tM (tu I))
    (e7 : spec k j4 = tt I) (e8 : spec k (16 * k - j4) = tM (tt I)) :
    Inv k I (bodyS (16 * k) (a, b) I) := by
  intro x
  rw [bodyS_eq, i1, i2, i3, i4]
  simp only
  rw [upd8_apply _ _ _ _ _ _ _ _ _ _ _ d1 d2 d3 d4 d5 d6, upd8_apply _ _ _ _ _ _ _ _ _ _ _ d1 d2 d3 d4 d5 d6]
  have hAx := hA x
  simp only at hAx
  have hwr : (x = j1 ∨ x = 16 * k - j1 ∨ x = j2 ∨ x = 16 * k - j2 ∨ x = j3 ∨ x = 16 * k - j3 ∨ x = j4 ∨
      x = 16 * k - j4) → written k I x := by
    intro h
    have hx : x ≠ 0 ∧ x ≠ 8 * k ∧ x < 16 * k := by omega
    exact ⟨hx.1, hx.2.1, hx.2.2, ((hit x hx.1 hx.2.1 hx.2.2).mpr h).le⟩
  split_ifs
  all_goals first
    | exact absurd (hwr (by omega)) ‹¬ written k I x›
    | (subst x; simp only [e1, e2, e3, e4, e5, e6, e7, e8]; rfl)
    | (have hw : written k I x := ‹_›
       have hne : iterOf k x ≠ I := fun he => by
         have := (hit x hw.1 hw.2.1 hw.2.2.1).mp he; omega
       rw [hAx, if_pos (⟨hw.1, hw.2.1, hw.2.2.1, by have := hw.2.2.2; omega⟩ : written k (I - 1) x)])
    | (have hw : ¬ written k I x := ‹_›
       rw [hAx, if_neg (fun h => hw ⟨h.1, h.2.1, h.2.2.1, by have := h.2.2.2; omega⟩)])

/-- The twelve assignments before the loop: iteration `0`. -/
def upd6 (μ : Tm → Tm) (a : TArr) (j1 m1 j2 m2 j3 m3 : ℕ) (V X2 X3 : Tm) : TArr :=
  let a := setS a j1 V
  let a := setS a m1 (μ (a j1))
  let a := setS a j2 (sub (a j1) X2)
  let a := setS a m2 (μ (a j2))
  let a := setS a j3 (sub (a j1) X3)
  let a := setS a m3 (μ (a j3))
  a

lemma initS_eq (n : ℕ) :
    initS n = (upd6 neg (fun _ => zero) (n / 2 - 1) (n / 2 + 1) (n - 1) 1 (n - 2) 2 sinZ sin2Z sin3Z,
      upd6 id (fun _ => zero) (n / 2 - 1) (n / 2 + 1) (n - 1) 1 (n - 2) 2 cosZ cos2Z cos3Z) := rfl

lemma upd6_apply (μ : Tm → Tm) (a : TArr) (j1 m1 j2 m2 j3 m3 : ℕ) (V X2 X3 : Tm)
    (h1 : j1 ≠ m1) (h2 : j1 ≠ j2) (h3 : j1 ≠ m2) (x : ℕ) :
    upd6 μ a j1 m1 j2 m2 j3 m3 V X2 X3 x =
      if x = m3 then μ (sub V X3) else if x = j3 then sub V X3
      else if x = m2 then μ (sub V X2) else if x = j2 then sub V X2
      else if x = m1 then μ V else if x = j1 then V else a x := by
  simp only [upd6, setS, Function.update_apply, h1, h2, h3, if_true, if_false]

theorem inv_init (k : ℕ) (hk : 1 ≤ k) : Inv k 0 (initS (16 * k)) := by
  intro x
  have e : 16 * k / 2 = 8 * k := by omega
  rw [initS_eq, e]
  simp only
  rw [upd6_apply _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega),
    upd6_apply _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)]
  have hwr : (x = 8 * k - 1 ∨ x = 8 * k + 1 ∨ x = 16 * k - 1 ∨ x = 1 ∨ x = 16 * k - 2 ∨ x = 2) →
      written k 0 x := by
    intro h
    have hx : x ≠ 0 ∧ x ≠ 8 * k ∧ x < 16 * k := by omega
    exact ⟨hx.1, hx.2.1, hx.2.2, ((iterOf_zero k x hk hx.1 hx.2.1 hx.2.2).mpr h).le⟩
  split_ifs
  all_goals first
    | exact absurd (hwr (by omega)) ‹¬ written k 0 x›
    | (subst x
       first
         | (rw [spec_low k 2 (by omega), show 2 = 4 * 0 + 2 by rfl, lowRole_eq 0 2 (by norm_num)]; rfl)
         | (rw [spec_low k 1 (by omega), show 1 = 4 * 0 + 1 by rfl, lowRole_eq 0 1 (by norm_num)]; rfl)
         | (rw [spec_up_low k _ (by omega) (by omega), show 16 * k - (16 * k - 2) = 4 * 0 + 2 by omega,
              lowRole_eq 0 2 (by norm_num)]; rfl)
         | (rw [spec_up_low k _ (by omega) (by omega), show 16 * k - (16 * k - 1) = 4 * 0 + 1 by omega,
              lowRole_eq 0 1 (by norm_num)]; rfl)
         | (rw [spec_up_mid k _ (by omega) (by omega),
              show 8 * k - 1 - (16 * k - (8 * k + 1)) = 4 * 0 + 0 by omega, midRole_eq 0 0 (by norm_num)]; rfl)
         | (rw [spec_mid k _ (by omega) (by omega), show 8 * k - 1 - (8 * k - 1) = 4 * 0 + 0 by omega,
              midRole_eq 0 0 (by norm_num)]; rfl))
    | (have hw : written k 0 x := ‹_›
       exfalso
       have := (iterOf_zero k x hk hw.1 hw.2.1 hw.2.2.1).mp (by have := hw.2.2.2; omega)
       omega)
    | rfl

/-- Iterations `1, …, I`. -/
theorem inv_loop (k : ℕ) (hk : 1 ≤ k) :
    ∀ I, I ≤ 2 * k - 1 → Inv k I ((List.range' 1 I).foldl (bodyS (16 * k)) (initS (16 * k))) := by
  intro I
  induction I with
  | zero => intro _; exact inv_init k hk
  | succ I ih =>
    intro hI
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hprev := ih (by omega)
    set A := (List.range' 1 I).foldl (bodyS (16 * k)) (initS (16 * k))
    obtain ⟨a, b⟩ := A
    rw [show 1 + 1 * I = I + 1 by ring]
    rcases Nat.even_or_odd (I + 1) with ⟨s, hs⟩ | ⟨s, hs⟩
    · have hs' : I + 1 = 2 * s := by omega
      rw [hs'] at hI ⊢
      rw [show I = 2 * s - 1 by omega] at hprev
      obtain ⟨i1, i2, i3, i4⟩ := idx_even k s hk (by omega) hI
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := spec_even k s hk (by omega) hI
      exact inv_step k (2 * s) hk (by omega) a b hprev _ _ _ _ i1 i2 i3 i4
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun x h0 hh hn => iterOf_even k s x hk (by omega) hI h0 hh hn) (by omega)
        e1 e2 e3 e4 e5 e6 e7 e8
    · rw [hs] at hI ⊢
      rw [show I = 2 * s + 1 - 1 by omega] at hprev
      obtain ⟨i1, i2, i3, i4⟩ := idx_odd k s hk hI
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := spec_odd k s hk hI
      exact inv_step k (2 * s + 1) hk (by omega) a b hprev _ _ _ _ i1 i2 i3 i4
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun x h0 hh hn => iterOf_odd k s x hk hI h0 hh hn) (by omega)
        e1 e2 e3 e4 e5 e6 e7 e8

/-- **Every vertex of the published polygon, for `n = 16k`.** -/
theorem vertexS_eq (k : ℕ) (hk : 1 ≤ k) (x : ℕ) (hx0 : x ≠ 0) (hxn : x < 16 * k) :
    vertexS (16 * k) x = spec k x := by
  have hloop := inv_loop k hk (2 * k - 1) le_rfl x
  unfold vertexS abS
  rw [if_neg hx0, show 16 * k / 8 - 1 = 2 * k - 1 by omega, show 16 * k / 2 = 8 * k by omega]
  simp only [setS, Function.update_apply]
  split_ifs with hh
  · rw [hh]; unfold spec; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]; rfl
  · rw [hloop, if_pos ⟨hx0, hh, hxn, iterOf_lt k x hk hx0 hxn⟩]

end Chiquipoli.Family.Trig.Layout
