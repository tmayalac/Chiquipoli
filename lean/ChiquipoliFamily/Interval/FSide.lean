/-
# The two closing sides, and upstream's equation `F`

For `n = 8m` with `m` even, the two sides upstream closes last,
`{2m − 1, 2m}` and `{6m, 6m + 1}`, have squared length `F_n(z) + (2 sin (z/2))²`
(`closing`, `closing'`): they are equal to the others exactly at a zero of
upstream's `F`. The identity rests on
`sin((m−1)(2z − π/2)) sin(m(2z − π/2)) = cos((2m − 2)z) sin(2mz)`, which is where
`m` even is used (`quarter_product`).

The rest of the file encloses `F` and its derivative in interval arithmetic from
a table of `(cos kz, sin kz)` (`encF`, `encFd`), with soundness proofs, and gives
the derivative of `F` (`hasDerivAt_F`).
-/
import ChiquipoliFamily.Interval.Shapes
import ChiquipoliFamily.Interval.Interp

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real Tm FI Chiquipoli.FirstOrder Chiquipoli.Feasible

/-- For `m = 2k`: `sin((m−1)θ) sin(mθ) = cos((2m−2)z) sin(2mz)`, `θ = 2z − π/2`. -/
lemma quarter_product (z : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    sin (((2 * k - 1 : ℕ) : ℝ) * (2 * z - π / 2)) * sin ((((2 * k - 1 : ℕ) : ℝ) + 1) * (2 * z - π / 2))
      = cos (((4 * k - 2 : ℕ) : ℝ) * z) * sin (((4 * k : ℕ) : ℝ) * z) := by
  have c1 : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c2 : ((4 * k - 2 : ℕ) : ℝ) = 4 * (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [c1, c2]
  push_cast
  -- (2k − 1)θ = (4k − 2)z + π/2 − kπ,   2kθ = 4kz − kπ
  have e1 : (2 * (k : ℝ) - 1) * (2 * z - π / 2) = ((4 * (k : ℝ) - 2) * z + π / 2) - (k : ℝ) * π := by ring
  have e2 : (2 * (k : ℝ) - 1 + 1) * (2 * z - π / 2) = 4 * (k : ℝ) * z - (k : ℝ) * π := by ring
  rw [e1, e2, sin_sub_nat_mul_pi, sin_sub_nat_mul_pi, sin_add_pi_div_two]
  have : ((-1 : ℝ) ^ k) * ((-1) ^ k) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (cos ((4 * (k : ℝ) - 2) * z) * sin (4 * (k : ℝ) * z)) * this

/-- The first coordinate of `X_{m−1}` is upstream's `x(z)`, for `n = 8m`, `m = 2k`. -/
lemma tXa_last (z : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (tXa (2 * k - 1)).eval z = Optigon.x (8 * (2 * k)) z := by
  rw [eval_tXa, mul_assoc (2 * cos z - 1), quarter_product z k hk]
  unfold Optigon.x
  have a : (((8 * (2 * k) : ℕ) : ℝ) / 4 - 2) = ((4 * k - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have b : ((8 * (2 * k) : ℕ) : ℝ) * z / 4 = ((4 * k : ℕ) : ℝ) * z := by push_cast; ring
  rw [a, b]; ring

lemma pm_odd (k : ℕ) (hk : 1 ≤ k) : ((-1 : ℝ) ^ (2 * k - 1)) = -1 := by
  have : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  rw [this, pow_succ, pow_mul]; simp

/-- **The closing side `{2m − 1, 2m}`.** -/
theorem closing (z : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    nsq (ev z (tu (2 * k - 1)) - ev z (tM (tq (2 * k - 1))))
      = Optigon.F (8 * (2 * k)) z + (2 * sin (z / 2)) ^ 2 := by
  simp only [nsq_eq, ev, tu, tq, tM, Tm.eval]
  rw [tXa_last z k hk, pm_odd k hk]
  unfold Optigon.F
  have a : (((8 * (2 * k) : ℕ) : ℝ) / 2 - 1) = 4 * ((2 * k - 1 : ℕ) : ℝ) + 3 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [a]
  ring

/-- **The closing side `{6m, 6m + 1}`.** -/
theorem closing' (z : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    nsq (ev z (tq (2 * k - 1)) - ev z (tM (tu (2 * k - 1))))
      = Optigon.F (8 * (2 * k)) z + (2 * sin (z / 2)) ^ 2 := by
  simp only [nsq_eq, ev, tu, tq, tM, Tm.eval]
  rw [tXa_last z k hk, pm_odd k hk]
  unfold Optigon.F
  have a : (((8 * (2 * k) : ℕ) : ℝ) / 2 - 1) = 4 * ((2 * k - 1 : ℕ) : ℝ) + 3 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [a]
  ring

/-! ## `F` in interval arithmetic -/

/-- `F_n` at the point (or interval) the table describes, `n = 8m`. -/
def encF (m : ℕ) (tab : List (FI × FI)) : Option FI := do
  let e1 ← look tab 1
  let e2 ← look tab 2
  let eb ← look tab (2 * m - 2)
  let ec ← look tab (2 * m)
  let ea ← look tab (4 * m - 1)
  let two := ofInt 2
  let K := sub (mul two e1.1) (ofInt 1)
  let x ← div (mul (mul K eb.1) ec.2) e2.1
  let x := sub e1.2 x
  let u := add (mul two x) ea.2
  some (sub (add (mul u u) (mul ea.1 ea.1)) (sub two (mul two e1.1)))

lemma look_cs {z : ℝ} {tab : List (FI × FI)} (hv : TabValid z tab) {k : ℕ} {cs : FI × FI}
    (h : look tab k = some cs) : FI.mem (cos (k * z)) cs.1 ∧ FI.mem (sin (k * z)) cs.2 :=
  look_sound hv h

/-- **Soundness of `encF`.** -/
theorem encF_sound {z : ℝ} {tab : List (FI × FI)} (hv : TabValid z tab) (m : ℕ) (hm : 1 ≤ m)
    {I : FI} (h : encF m tab = some I) : FI.mem (Optigon.F (8 * m) z) I := by
  unfold encF at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨e1, h1, e2, h2, eb, hb, ec, hc, ea, ha, x, hx, hI⟩ := h
  simp only [Option.some.injEq] at hI
  subst hI
  have c1 := look_cs hv h1; have c2 := look_cs hv h2
  have cb := look_cs hv hb; have cc := look_cs hv hc; have ca := look_cs hv ha
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at c1 c2
  have htwo : FI.mem (2 : ℝ) (ofInt 2) := by simpa using mem_ofInt 2
  have hone : FI.mem (1 : ℝ) (ofInt 1) := by simpa using mem_ofInt 1
  have hK := mem_sub (mem_mul htwo c1.1) hone
  have hxdiv := mem_div (mem_mul (mem_mul hK cb.1) cc.2) c2.1 hx
  have hxx := mem_sub c1.2 hxdiv
  have hu := mem_add (mem_mul htwo hxx) ca.2
  have hF := mem_sub (mem_add (mem_mul hu hu) (mem_mul ca.1 ca.1)) (mem_sub htwo (mem_mul htwo c1.1))
  convert hF using 1
  unfold Optigon.F Optigon.x
  have a : (((8 * m : ℕ) : ℝ) / 4 - 2) = ((2 * m - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have b : ((8 * m : ℕ) : ℝ) * z / 4 = ((2 * m : ℕ) : ℝ) * z := by push_cast; ring
  have c : (((8 * m : ℕ) : ℝ) / 2 - 1) = ((4 * m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have d : 4 * sin (z / 2) ^ 2 = 2 - 2 * cos z := by rw [← sq_two_sin_half']; ring
  rw [a, b, c, d]
  ring

end Chiquipoli.Family.Trig
