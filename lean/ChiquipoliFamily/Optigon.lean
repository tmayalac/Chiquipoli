/-
# The published Bingane–Audet constructor, transcribed from its source

This file is the upstream OPTIGON constructor `cstrt_audet_ngon` — the code
that accompanies C. Bingane and C. Audet, *Tight bounds on the maximal
perimeter of convex equilateral small polygons*, Arch. Math. 119 (2022) — written
in Lean, **statement for statement**, for every `n`:

    upstream  https://github.com/cbingane/optigon, cstrt_ngon/cstrt_audet_ngon.jl
    vendored  test/fixtures/optigon_reference.jl  (MIT, SHA-256 of upstream recorded there)

The correspondence is textual, so that a reader can check it line by line
against the vendored file:

| upstream (Julia)                                      | here                        |
|-------------------------------------------------------|-----------------------------|
| `x(t) = sin(t) - (2cos(t)-1)cos((n/4-2)t)sin(nt/4)/cos(2t)` | `x`                   |
| `F(t) = (2x(t)+sin((n/2-1)t))^2 + cos((n/2-1)t)^2 - 4sin(t/2)^2` | `F`             |
| `a = zeros(T, n-1)`, then twelve assignments          | `init`                      |
| `for i = 1:Int(n/8-1)` … `end`, sixteen assignments   | `body`, folded over `i`     |
| `a[Int(n/2)] = 0`, `b[Int(n/2)] = 1`                  | the last two `set`s of `ab` |
| vertex `k` is `(a[k], b[k])`, the remaining one the origin | `vertex`               |

Arrays are functions `ℕ → ℝ`; `set a j v` is the assignment `a[j] = v`, and
reads (`a j`) see every earlier assignment, exactly as in the loop. The only
deviation is the one the vendored reference already makes: upstream locates the
root with `find_zero` on the bracket `(2 asin(sin(π/n)/2), π/n)`; here the root
is not computed but *characterised* — the theorems of `A<n>/Published.lean`
state that `F` has exactly one zero there and describe the polygon built at it.

Nothing in the certificate is defined from this file. The per-case files prove
that it produces, vertex for vertex, the configuration the certificate is
about, which is what ties the certified object to the published one inside the
kernel rather than through a numerical test.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Optigon

open Real

/-- Upstream `x(t)`. -/
noncomputable def x (n : ℕ) (t : ℝ) : ℝ :=
  sin t - (2 * cos t - 1) * cos (((n : ℝ) / 4 - 2) * t) * sin ((n : ℝ) * t / 4) / cos (2 * t)

/-- Upstream `F(t)`, the constructor equation: the polygon is built at a root. -/
noncomputable def F (n : ℕ) (t : ℝ) : ℝ :=
  (2 * x n t + sin (((n : ℝ) / 2 - 1) * t)) ^ 2 + cos (((n : ℝ) / 2 - 1) * t) ^ 2
    - 4 * sin (t / 2) ^ 2

/-- Upstream's search bracket `(2 asin(sin(π/n)/2), π/n)`. -/
noncomputable def lo (n : ℕ) : ℝ := 2 * arcsin (sin (π / n) / 2)
noncomputable def hi (n : ℕ) : ℝ := π / n

/-- An array, indexed as upstream (`1 … n-1`); unassigned entries are `0`. -/
abbrev Arr := ℕ → ℝ

/-- The assignment `a[j] = v`. -/
def set (a : Arr) (j : ℕ) (v : ℝ) : Arr := Function.update a j v

/-- Upstream, before the loop:
```
a[Int(n/2-1)] = sin(z);              a[Int(n/2+1)] = -a[Int(n/2-1)]
b[Int(n/2-1)] = cos(z);              b[Int(n/2+1)] =  b[Int(n/2-1)]
a[n-1] = a[Int(n/2-1)] - sin(2*z);   a[1] = -a[n-1]
b[n-1] = b[Int(n/2-1)] - cos(2*z);   b[1] =  b[n-1]
a[n-2] = a[Int(n/2-1)] - sin(3*z);   a[2] = -a[n-2]
b[n-2] = b[Int(n/2-1)] - cos(3*z);   b[2] =  b[n-2]
``` -/
noncomputable def init (n : ℕ) (z : ℝ) : Arr × Arr :=
  let a : Arr := fun _ => 0
  let b : Arr := fun _ => 0
  let a := set a (n / 2 - 1) (sin z)
  let a := set a (n / 2 + 1) (-(a (n / 2 - 1)))
  let b := set b (n / 2 - 1) (cos z)
  let b := set b (n / 2 + 1) (b (n / 2 - 1))
  let a := set a (n - 1) (a (n / 2 - 1) - sin (2 * z))
  let a := set a 1 (-(a (n - 1)))
  let b := set b (n - 1) (b (n / 2 - 1) - cos (2 * z))
  let b := set b 1 (b (n - 1))
  let a := set a (n - 2) (a (n / 2 - 1) - sin (3 * z))
  let a := set a 2 (-(a (n - 2)))
  let b := set b (n - 2) (b (n / 2 - 1) - cos (3 * z))
  let b := set b 2 (b (n - 2))
  (a, b)

/-- Upstream, iteration `i` of `for i = 1:Int(n/8-1)`:
```
j1 = Int(mod(n/2 - 1 + i*(3*n/2 - 2), n))
j2 = Int(mod(n - 1   + i*(3*n/2 - 2), n))
j3 = Int(mod(n - 2   + i*(3*n/2 - 2), n))
j4 = Int(mod(n       + i*(3*n/2 - 2), n))
a[j1] = sin(z) - (2*cos(z) - 1)*sin(i*(2*z - pi/2))*sin((i+1)*(2*z - pi/2))/cos(2*z);  a[n-j1] = -a[j1]
b[j1] = cos(z) - (2*cos(z) - 1)*sin(i*(2*z - pi/2))*cos((i+1)*(2*z - pi/2))/cos(2*z);  b[n-j1] =  b[j1]
a[j2] = a[j1] - (-1)^i*sin((4*i+2)*z);   a[n-j2] = -a[j2]
b[j2] = b[j1] - (-1)^i*cos((4*i+2)*z);   b[n-j2] =  b[j2]
a[j3] = a[j1] - (-1)^i*sin((4*i+3)*z);   a[n-j3] = -a[j3]
b[j3] = b[j1] - (-1)^i*cos((4*i+3)*z);   b[n-j3] =  b[j3]
a[j4] = a[j1] - (-1)^i*sin((4*i+1)*z);   a[n-j4] = -a[j4]
b[j4] = b[j1] - (-1)^i*cos((4*i+1)*z);   b[n-j4] =  b[j4]
```
For `n` a multiple of 8 every index is a natural number, and `n/2`, `3n/2` are
exact in `ℕ`. -/
noncomputable def body (n : ℕ) (z : ℝ) (ab : Arr × Arr) (i : ℕ) : Arr × Arr :=
  let a := ab.1
  let b := ab.2
  let j1 := (n / 2 - 1 + i * (3 * n / 2 - 2)) % n
  let j2 := (n - 1 + i * (3 * n / 2 - 2)) % n
  let j3 := (n - 2 + i * (3 * n / 2 - 2)) % n
  let j4 := (n + i * (3 * n / 2 - 2)) % n
  let a := set a j1 (sin z - (2 * cos z - 1) * sin ((i : ℝ) * (2 * z - π / 2)) *
                      sin (((i : ℝ) + 1) * (2 * z - π / 2)) / cos (2 * z))
  let a := set a (n - j1) (-(a j1))
  let b := set b j1 (cos z - (2 * cos z - 1) * sin ((i : ℝ) * (2 * z - π / 2)) *
                      cos (((i : ℝ) + 1) * (2 * z - π / 2)) / cos (2 * z))
  let b := set b (n - j1) (b j1)
  let a := set a j2 (a j1 - (-1) ^ i * sin ((4 * (i : ℝ) + 2) * z))
  let a := set a (n - j2) (-(a j2))
  let b := set b j2 (b j1 - (-1) ^ i * cos ((4 * (i : ℝ) + 2) * z))
  let b := set b (n - j2) (b j2)
  let a := set a j3 (a j1 - (-1) ^ i * sin ((4 * (i : ℝ) + 3) * z))
  let a := set a (n - j3) (-(a j3))
  let b := set b j3 (b j1 - (-1) ^ i * cos ((4 * (i : ℝ) + 3) * z))
  let b := set b (n - j3) (b j3)
  let a := set a j4 (a j1 - (-1) ^ i * sin ((4 * (i : ℝ) + 1) * z))
  let a := set a (n - j4) (-(a j4))
  let b := set b j4 (b j1 - (-1) ^ i * cos ((4 * (i : ℝ) + 1) * z))
  let b := set b (n - j4) (b j4)
  (a, b)

/-- The loop `for i = 1:Int(n/8-1)`, then `a[Int(n/2)] = 0; b[Int(n/2)] = 1`. -/
noncomputable def ab (n : ℕ) (z : ℝ) : Arr × Arr :=
  let r := (List.range' 1 (n / 8 - 1)).foldl (body n z) (init n z)
  (set r.1 (n / 2) 0, set r.2 (n / 2) 1)

/-- Vertex `k` of the published polygon: `(a[k], b[k])` for `1 ≤ k ≤ n-1`, and
the origin for `k = 0` ("the remaining vertex at the origin"). -/
noncomputable def vertex (n : ℕ) (z : ℝ) (k : ℕ) : ℝ × ℝ :=
  if k = 0 then (0, 0) else ((ab n z).1 k, (ab n z).2 k)

/-! ### Two facts every case uses

The quarter-turn shifts `sin(i(2z - π/2))`, `cos(i(2z - π/2))` of the loop are
`± sin(2iz)` or `± cos(2iz)`, with the sign and the function fixed by `i mod 4`. -/

/-- `sin (y - i·π/2)` and `cos (y - i·π/2)`, by `i mod 4`. -/
noncomputable def rs (r : ℕ) (y : ℝ) : ℝ :=
  match r with | 0 => sin y | 1 => -cos y | 2 => -sin y | _ => cos y
noncomputable def rc (r : ℕ) (y : ℝ) : ℝ :=
  match r with | 0 => cos y | 1 => sin y | 2 => -cos y | _ => -sin y

theorem shift (i : ℕ) (y : ℝ) :
    sin (y - i * (π / 2)) = rs (i % 4) y ∧ cos (y - i * (π / 2)) = rc (i % 4) y := by
  induction i with
  | zero => simp [rs, rc]
  | succ k ih =>
    have e : y - ((k + 1 : ℕ) : ℝ) * (π / 2) = (y - k * (π / 2)) - π / 2 := by push_cast; ring
    rw [e, sin_sub_pi_div_two, cos_sub_pi_div_two, ih.1, ih.2]
    have h4 : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hs : (k + 1) % 4 = (k % 4 + 1) % 4 := by omega
    rw [hs]
    interval_cases (k % 4) <;> simp [rs, rc]

theorem sin_quarter (i : ℕ) (t : ℝ) : sin ((i : ℝ) * (t - π / 2)) = rs (i % 4) (i * t) := by
  have : (i : ℝ) * (t - π / 2) = i * t - i * (π / 2) := by ring
  rw [this]; exact (shift i _).1

theorem cos_quarter (i : ℕ) (t : ℝ) : cos ((i : ℝ) * (t - π / 2)) = rc (i % 4) (i * t) := by
  have : (i : ℝ) * (t - π / 2) = i * t - i * (π / 2) := by ring
  rw [this]; exact (shift i _).2

theorem sin_quarter_succ (i : ℕ) (t : ℝ) :
    sin (((i : ℝ) + 1) * (t - π / 2)) = rs ((i + 1) % 4) (((i : ℝ) + 1) * t) := by
  have := sin_quarter (i + 1) t; push_cast at this; exact this

theorem cos_quarter_succ (i : ℕ) (t : ℝ) :
    cos (((i : ℝ) + 1) * (t - π / 2)) = rc ((i + 1) % 4) (((i : ℝ) + 1) * t) := by
  have := cos_quarter (i + 1) t; push_cast at this; exact this

/-- On upstream's bracket, `z < π/n ≤ π/16`, so `cos 2z > 0`: every division in
the constructor is by a nonzero number. -/
theorem cos_two_pos {n : ℕ} (hn : 16 ≤ n) {z : ℝ} (h0 : 0 < z) (h1 : z < hi n) :
    0 < cos (2 * z) := by
  have hnr : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := pi_pos
  have : z < π / 16 := by
    unfold hi at h1
    calc z < π / n := h1
      _ ≤ π / 16 := div_le_div_of_nonneg_left hpi.le (by norm_num) hnr
  apply cos_pos_of_mem_Ioo; constructor <;> linarith

end Chiquipoli.Family.Optigon
