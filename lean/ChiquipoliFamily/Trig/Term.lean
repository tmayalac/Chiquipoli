/-
# The published constructor, run symbolically

`ChiquipoliFamily/Optigon.lean` transcribes the upstream OPTIGON constructor
`cstrt_audet_ngon` statement for statement, over `ℝ`. This file runs *the same
program* over a small syntax of terms, `Tm`, whose constructors are exactly the
real expressions that program writes: `sin z`, `cos (2 * z)`,
`sin ((i : ℝ) * (2 * z - π / 2))`, `(-1) ^ i`, `sin ((4 * (i : ℝ) + 2) * z)`, …,
combined by `+ - * /` and negation.

The one theorem, `ab_eval`, proved once for every `n`, says that evaluating the
symbolic arrays at `z` gives upstream's arrays: `(Optigon.ab n z).1 k` is
`((abS n).1 k).eval z`, and the same for `.2`. The symbolic run is computable,
so for a given `n` the kernel can *compute* which expression upstream stores at
every index (`decide`), with no polynomial expansion and no dependence on the
size of `n` beyond the length of the loop. That is what lets the family
certificate reach `n = 128, 256` (`ChiquipoliFamily/Trig/`).

Nothing here is trusted in the sense of the transcription: `Optigon.lean`
remains the object the theorems are about, and `ab_eval` is a kernel-checked
statement about it.
-/
import ChiquipoliFamily.Optigon

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real

/-- The terms the OPTIGON constructor writes. Each constructor evaluates to the
very expression upstream's code contains (`Tm.eval`). -/
inductive Tm where
  | zero
  | one
  | two
  | sinZ
  | cosZ
  | sin2Z
  | cos2Z
  | sin3Z
  | cos3Z
  /-- `sin ((i : ℝ) * (2 * z - π / 2))` -/
  | sQ (i : ℕ)
  /-- `sin (((i : ℝ) + 1) * (2 * z - π / 2))` -/
  | sQ1 (i : ℕ)
  /-- `cos (((i : ℝ) + 1) * (2 * z - π / 2))` -/
  | cQ1 (i : ℕ)
  /-- `sin ((4 * (i : ℝ) + 1) * z)`, and the same with `+ 2`, `+ 3`; `cos` likewise -/
  | s41 (i : ℕ)
  | s42 (i : ℕ)
  | s43 (i : ℕ)
  | c41 (i : ℕ)
  | c42 (i : ℕ)
  | c43 (i : ℕ)
  /-- `(-1) ^ i` -/
  | pm (i : ℕ)
  | neg (a : Tm)
  | sub (a b : Tm)
  | mul (a b : Tm)
  | div (a b : Tm)
  deriving DecidableEq, Repr, Inhabited

namespace Tm

/-- The value of a term at the parameter `z`: literally upstream's expression. -/
noncomputable def eval (z : ℝ) : Tm → ℝ
  | zero => 0
  | one => 1
  | two => 2
  | sinZ => sin z
  | cosZ => cos z
  | sin2Z => sin (2 * z)
  | cos2Z => cos (2 * z)
  | sin3Z => sin (3 * z)
  | cos3Z => cos (3 * z)
  | sQ i => sin ((i : ℝ) * (2 * z - π / 2))
  | sQ1 i => sin (((i : ℝ) + 1) * (2 * z - π / 2))
  | cQ1 i => cos (((i : ℝ) + 1) * (2 * z - π / 2))
  | s41 i => sin ((4 * (i : ℝ) + 1) * z)
  | s42 i => sin ((4 * (i : ℝ) + 2) * z)
  | s43 i => sin ((4 * (i : ℝ) + 3) * z)
  | c41 i => cos ((4 * (i : ℝ) + 1) * z)
  | c42 i => cos ((4 * (i : ℝ) + 2) * z)
  | c43 i => cos ((4 * (i : ℝ) + 3) * z)
  | pm i => (-1) ^ i
  | neg a => -(a.eval z)
  | sub a b => a.eval z - b.eval z
  | mul a b => a.eval z * b.eval z
  | div a b => a.eval z / b.eval z

end Tm

open Tm

/-- A symbolic array, indexed as upstream. -/
abbrev TArr := ℕ → Tm

/-- The symbolic assignment `a[j] = v`. -/
def setS (a : TArr) (j : ℕ) (v : Tm) : TArr := Function.update a j v

/-- Upstream's twelve assignments before the loop, symbolically
(`Optigon.init`, line for line). -/
def initS (n : ℕ) : TArr × TArr :=
  let a : TArr := fun _ => zero
  let b : TArr := fun _ => zero
  let a := setS a (n / 2 - 1) sinZ
  let a := setS a (n / 2 + 1) (neg (a (n / 2 - 1)))
  let b := setS b (n / 2 - 1) cosZ
  let b := setS b (n / 2 + 1) (b (n / 2 - 1))
  let a := setS a (n - 1) (sub (a (n / 2 - 1)) sin2Z)
  let a := setS a 1 (neg (a (n - 1)))
  let b := setS b (n - 1) (sub (b (n / 2 - 1)) cos2Z)
  let b := setS b 1 (b (n - 1))
  let a := setS a (n - 2) (sub (a (n / 2 - 1)) sin3Z)
  let a := setS a 2 (neg (a (n - 2)))
  let b := setS b (n - 2) (sub (b (n / 2 - 1)) cos3Z)
  let b := setS b 2 (b (n - 2))
  (a, b)

/-- Upstream's loop body, iteration `i`, symbolically (`Optigon.body`). -/
def bodyS (n : ℕ) (ab : TArr × TArr) (i : ℕ) : TArr × TArr :=
  let a := ab.1
  let b := ab.2
  let j1 := (n / 2 - 1 + i * (3 * n / 2 - 2)) % n
  let j2 := (n - 1 + i * (3 * n / 2 - 2)) % n
  let j3 := (n - 2 + i * (3 * n / 2 - 2)) % n
  let j4 := (n + i * (3 * n / 2 - 2)) % n
  let a := setS a j1 (sub sinZ (div (mul (mul (sub (mul two cosZ) one) (sQ i)) (sQ1 i)) cos2Z))
  let a := setS a (n - j1) (neg (a j1))
  let b := setS b j1 (sub cosZ (div (mul (mul (sub (mul two cosZ) one) (sQ i)) (cQ1 i)) cos2Z))
  let b := setS b (n - j1) (b j1)
  let a := setS a j2 (sub (a j1) (mul (pm i) (s42 i)))
  let a := setS a (n - j2) (neg (a j2))
  let b := setS b j2 (sub (b j1) (mul (pm i) (c42 i)))
  let b := setS b (n - j2) (b j2)
  let a := setS a j3 (sub (a j1) (mul (pm i) (s43 i)))
  let a := setS a (n - j3) (neg (a j3))
  let b := setS b j3 (sub (b j1) (mul (pm i) (c43 i)))
  let b := setS b (n - j3) (b j3)
  let a := setS a j4 (sub (a j1) (mul (pm i) (s41 i)))
  let a := setS a (n - j4) (neg (a j4))
  let b := setS b j4 (sub (b j1) (mul (pm i) (c41 i)))
  let b := setS b (n - j4) (b j4)
  (a, b)

/-- The loop and the two final assignments, symbolically (`Optigon.ab`). -/
def abS (n : ℕ) : TArr × TArr :=
  let r := (List.range' 1 (n / 8 - 1)).foldl (bodyS n) (initS n)
  (setS r.1 (n / 2) zero, setS r.2 (n / 2) one)

/-- Evaluate a symbolic array pointwise. -/
noncomputable def E (z : ℝ) (a : TArr) : Optigon.Arr := fun k => (a k).eval z

lemma E_setS (z : ℝ) (a : TArr) (j : ℕ) (v : Tm) :
    E z (setS a j v) = Optigon.set (E z a) j (v.eval z) := by
  funext k
  simp only [E, setS, Optigon.set, Function.update_apply]
  split_ifs <;> rfl

lemma eval_setS_apply (z : ℝ) (a : TArr) (j k : ℕ) (v : Tm) :
    ((setS a j v) k).eval z = Optigon.set (E z a) j (v.eval z) k := by
  rw [← E_setS]; rfl

lemma E_const_zero (z : ℝ) : E z (fun _ => zero) = fun _ => (0 : ℝ) := by
  funext k; rfl

theorem init_eval (n : ℕ) (z : ℝ) :
    Optigon.init n z = (E z (initS n).1, E z (initS n).2) := by
  simp only [Optigon.init, initS, E_setS, eval_setS_apply, E_const_zero, eval]

theorem body_eval (n : ℕ) (z : ℝ) (a b : TArr) (i : ℕ) :
    Optigon.body n z (E z a, E z b) i = (E z (bodyS n (a, b) i).1, E z (bodyS n (a, b) i).2) := by
  simp only [Optigon.body, bodyS, E_setS, eval_setS_apply, eval]

theorem fold_eval (n : ℕ) (z : ℝ) (l : List ℕ) (a b : TArr) :
    l.foldl (Optigon.body n z) (E z a, E z b)
      = (E z (l.foldl (bodyS n) (a, b)).1, E z (l.foldl (bodyS n) (a, b)).2) := by
  induction l generalizing a b with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [body_eval]
    exact ih _ _

/-- **Upstream's arrays are the symbolic run, evaluated.** For every `n` and `z`. -/
theorem ab_eval (n : ℕ) (z : ℝ) :
    Optigon.ab n z = (E z (abS n).1, E z (abS n).2) := by
  unfold Optigon.ab abS
  rw [init_eval, fold_eval]
  simp only [E_setS, eval]

/-- The symbolic vertex `k`: the origin for `k = 0`, as upstream. -/
def vertexS (n k : ℕ) : Tm × Tm :=
  if k = 0 then (zero, zero) else ((abS n).1 k, (abS n).2 k)

/-- **Every vertex of the published polygon is its symbolic vertex, evaluated.** -/
theorem vertex_eval (n : ℕ) (z : ℝ) (k : ℕ) :
    Optigon.vertex n z k = ((vertexS n k).1.eval z, (vertexS n k).2.eval z) := by
  unfold Optigon.vertex vertexS
  split_ifs with h
  · simp [eval]
  · rw [ab_eval]; rfl

end Chiquipoli.Family.Trig
