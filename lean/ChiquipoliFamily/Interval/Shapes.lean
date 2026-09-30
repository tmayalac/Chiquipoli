/-
# The exact identities of the constructor, proved once for every block

Upstream's loop writes, at iteration `i`, a base point `X_i` and three points
`X_i − (−1)^i Φ_{4i+c}(z)`, `c = 1, 2, 3`, with `Φ_k(z) = (sin kz, cos kz)`; the
twelve assignments before the loop write the same pattern for `i = 0` with
`X_0 = Φ_1`. We name these points by their role, as terms (`tq i`, `tr i`,
`tu i`, `tt i`; `tq0`, …), and prove here, for every `i`:

* the four points of a block and the two neighbouring blocks realise every edge
  of Ayala Hoffmann's graph `G_n` as a chord of length exactly `1` (`fan_*`,
  `cross_*`), and every side except two has squared length `2 − 2 cos z`
  (`side_*`); the key step is his block increment
  `X_{i+1} − X_i = (−1)^{i+1}(2cos z − 1) Φ_{4i+4}(z)` (`blockA`, `blockB`);
* the two remaining sides have squared length `F_n(z) + (2 sin(z/2))²`
  (`closing`), for `n = 8m` with `m` even.

Which role each index carries for a given `n` is not proved here: the kernel
computes it from the symbolic run (`vertexS n k = tr i` by `decide`), so these
lemmas are applied, per case, exactly where the published code puts the points.
-/
import ChiquipoliFamily.Interval.Term
import ChiquipoliLean.Theory.Feasible

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real Tm Chiquipoli.FirstOrder Chiquipoli.Feasible

/-! ## The roles, as terms (exactly what `bodyS` and `initS` write) -/

/-- `2 cos z − 1` -/
def tK : Tm := sub (mul two cosZ) one
def tXa (i : ℕ) : Tm := sub sinZ (div (mul (mul tK (sQ i)) (sQ1 i)) cos2Z)
def tXb (i : ℕ) : Tm := sub cosZ (div (mul (mul tK (sQ i)) (cQ1 i)) cos2Z)
def tq (i : ℕ) : Tm × Tm := (tXa i, tXb i)
def tr (i : ℕ) : Tm × Tm := (sub (tXa i) (mul (pm i) (s42 i)), sub (tXb i) (mul (pm i) (c42 i)))
def tu (i : ℕ) : Tm × Tm := (sub (tXa i) (mul (pm i) (s43 i)), sub (tXb i) (mul (pm i) (c43 i)))
def tt (i : ℕ) : Tm × Tm := (sub (tXa i) (mul (pm i) (s41 i)), sub (tXb i) (mul (pm i) (c41 i)))
def tq0 : Tm × Tm := (sinZ, cosZ)
def tr0 : Tm × Tm := (sub sinZ sin2Z, sub cosZ cos2Z)
def tu0 : Tm × Tm := (sub sinZ sin3Z, sub cosZ cos3Z)
def tOrigin : Tm × Tm := (zero, zero)
def tTop : Tm × Tm := (zero, one)
/-- The mirror image under `σ(j) = n − j`: upstream writes `a[n−j] = −a[j]`, `b[n−j] = b[j]`. -/
def tM (p : Tm × Tm) : Tm × Tm := (neg p.1, p.2)

/-- A symbolic point, evaluated. -/
noncomputable def ev (z : ℝ) (p : Tm × Tm) : ℝ × ℝ := (p.1.eval z, p.2.eval z)

/-! ## Generic facts -/

lemma nsq_eq (a b : ℝ × ℝ) : nsq (a - b) = (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 := by
  simp only [nsq, ip, Prod.fst_sub, Prod.snd_sub]; ring

lemma nsq_comm (a b : ℝ × ℝ) : nsq (a - b) = nsq (b - a) := by
  rw [nsq_eq, nsq_eq]; ring

lemma nsq_mirror (z : ℝ) (p q : Tm × Tm) : nsq (ev z (tM p) - ev z (tM q)) = nsq (ev z p - ev z q) := by
  simp only [nsq_eq, ev, tM, Tm.eval]; ring

lemma pm_sq (i : ℕ) : ((-1 : ℝ) ^ i) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]; simp

lemma sq_two_sin_half' (z : ℝ) : (2 * sin (z / 2)) ^ 2 = 2 - 2 * cos z := by
  have h : cos z = 2 * cos (z / 2) ^ 2 - 1 := by rw [← cos_two_mul]; ring_nf
  have hs := sin_sq_add_cos_sq (z / 2)
  linear_combination 4 * hs + 2 * h

/-- `|Φ_a − Φ_b|² = 2 − 2 cos (a − b)`. -/
lemma phi_dist (x y : ℝ) : (sin x - sin y) ^ 2 + (cos x - cos y) ^ 2 = 2 - 2 * cos (x - y) := by
  rw [cos_sub]
  linear_combination sin_sq_add_cos_sq x + sin_sq_add_cos_sq y

/-! ## Chords inside a block -/

lemma fan_gen (A B s x : ℝ) (hs : s ^ 2 = 1) :
    (A - s * sin x - A) ^ 2 + (B - s * cos x - B) ^ 2 = 1 := by
  have := sin_sq_add_cos_sq x
  linear_combination s ^ 2 * this + hs

theorem fan_qr (z : ℝ) (i : ℕ) : nsq (ev z (tr i) - ev z (tq i)) = 1 := by
  simp only [nsq_eq, ev, tr, tq, Tm.eval]; exact fan_gen _ _ _ _ (pm_sq i)
theorem fan_qu (z : ℝ) (i : ℕ) : nsq (ev z (tu i) - ev z (tq i)) = 1 := by
  simp only [nsq_eq, ev, tu, tq, Tm.eval]; exact fan_gen _ _ _ _ (pm_sq i)
theorem fan_qt (z : ℝ) (i : ℕ) : nsq (ev z (tt i) - ev z (tq i)) = 1 := by
  simp only [nsq_eq, ev, tt, tq, Tm.eval]; exact fan_gen _ _ _ _ (pm_sq i)

theorem fan0_qr (z : ℝ) : nsq (ev z tr0 - ev z tq0) = 1 := by
  simp only [nsq_eq, ev, tr0, tq0, Tm.eval]
  have := sin_sq_add_cos_sq (2 * z); linear_combination this
theorem fan0_qu (z : ℝ) : nsq (ev z tu0 - ev z tq0) = 1 := by
  simp only [nsq_eq, ev, tu0, tq0, Tm.eval]
  have := sin_sq_add_cos_sq (3 * z); linear_combination this
theorem fan0_qt (z : ℝ) : nsq (ev z tOrigin - ev z tq0) = 1 := by
  simp only [nsq_eq, ev, tOrigin, tq0, Tm.eval]
  have := sin_sq_add_cos_sq z; linear_combination this
theorem origin_top (z : ℝ) : nsq (ev z tTop - ev z tOrigin) = 1 := by
  simp only [nsq_eq, ev, tTop, tOrigin, Tm.eval]; norm_num

/-! ## Sides inside a block -/

lemma side_gen (A B s x y : ℝ) (hs : s ^ 2 = 1) :
    ((A - s * sin x) - (A - s * sin y)) ^ 2 + ((B - s * cos x) - (B - s * cos y)) ^ 2
      = 2 - 2 * cos (x - y) := by
  have h := phi_dist x y
  have e : ((A - s * sin x) - (A - s * sin y)) ^ 2 + ((B - s * cos x) - (B - s * cos y)) ^ 2
      = s ^ 2 * ((sin x - sin y) ^ 2 + (cos x - cos y) ^ 2) := by ring
  rw [e, hs, one_mul, h]

theorem side_ur (z : ℝ) (i : ℕ) : nsq (ev z (tr i) - ev z (tu i)) = (2 * sin (z / 2)) ^ 2 := by
  simp only [nsq_eq, ev, tr, tu, Tm.eval]
  rw [side_gen _ _ _ _ _ (pm_sq i), sq_two_sin_half']
  have : (4 * (i : ℝ) + 2) * z - (4 * (i : ℝ) + 3) * z = -z := by ring
  rw [this, cos_neg]
theorem side_rt (z : ℝ) (i : ℕ) : nsq (ev z (tt i) - ev z (tr i)) = (2 * sin (z / 2)) ^ 2 := by
  simp only [nsq_eq, ev, tt, tr, Tm.eval]
  rw [side_gen _ _ _ _ _ (pm_sq i), sq_two_sin_half']
  have : (4 * (i : ℝ) + 1) * z - (4 * (i : ℝ) + 2) * z = -z := by ring
  rw [this, cos_neg]
theorem side0_ur (z : ℝ) : nsq (ev z tr0 - ev z tu0) = (2 * sin (z / 2)) ^ 2 := by
  simp only [nsq_eq, ev, tr0, tu0, Tm.eval]
  have h := phi_dist (3 * z) (2 * z)
  have e : (sin z - sin (2 * z) - (sin z - sin (3 * z))) ^ 2 + (cos z - cos (2 * z) - (cos z - cos (3 * z))) ^ 2
      = (sin (3 * z) - sin (2 * z)) ^ 2 + (cos (3 * z) - cos (2 * z)) ^ 2 := by ring
  rw [e, h, sq_two_sin_half']; ring_nf
theorem side0_rt (z : ℝ) : nsq (ev z tOrigin - ev z tr0) = (2 * sin (z / 2)) ^ 2 := by
  simp only [nsq_eq, ev, tOrigin, tr0, Tm.eval]
  have h := phi_dist z (2 * z)
  have e : (0 - (sin z - sin (2 * z))) ^ 2 + (0 - (cos z - cos (2 * z))) ^ 2
      = (sin z - sin (2 * z)) ^ 2 + (cos z - cos (2 * z)) ^ 2 := by ring
  rw [e, h, sq_two_sin_half']
  have : z - 2 * z = -z := by ring
  rw [this, cos_neg]
theorem side0_top (z : ℝ) : nsq (ev z tTop - ev z tq0) = (2 * sin (z / 2)) ^ 2 := by
  simp only [nsq_eq, ev, tTop, tq0, Tm.eval]
  rw [sq_two_sin_half']
  have := sin_sq_add_cos_sq z; linear_combination this

/-! ## Ayala Hoffmann's block increment -/

/-- With `θ = 2z − π/2`: `sin θ = −cos 2z`. -/
lemma sin_theta (z : ℝ) : sin (2 * z - π / 2) = -cos (2 * z) := by rw [sin_sub_pi_div_two]

lemma eval_tXa (z : ℝ) (i : ℕ) : (tXa i).eval z
    = sin z - (2 * cos z - 1) * sin ((i : ℝ) * (2 * z - π / 2)) * sin (((i : ℝ) + 1) * (2 * z - π / 2)) / cos (2 * z) := by
  simp only [tXa, tK, Tm.eval]
lemma eval_tXb (z : ℝ) (i : ℕ) : (tXb i).eval z
    = cos z - (2 * cos z - 1) * sin ((i : ℝ) * (2 * z - π / 2)) * cos (((i : ℝ) + 1) * (2 * z - π / 2)) / cos (2 * z) := by
  simp only [tXb, tK, Tm.eval]

theorem blockA (z : ℝ) (i : ℕ) (hc : cos (2 * z) ≠ 0) :
    (tXa (i + 1)).eval z - (tXa i).eval z = (-1) ^ (i + 1) * (2 * cos z - 1) * sin ((4 * (i : ℝ) + 4) * z) := by
  rw [eval_tXa, eval_tXa]
  set θ := 2 * z - π / 2 with hθ
  have c1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [c1]
  -- sin((i+2)θ) − sin(iθ) = 2 sin θ cos((i+1)θ), and 2 sin A cos A = sin 2A
  have h1 : sin (((i : ℝ) + 1 + 1) * θ) - sin ((i : ℝ) * θ) = 2 * sin θ * cos (((i : ℝ) + 1) * θ) := by
    rw [sin_sub_sin]
    have a : (((i : ℝ) + 1 + 1) * θ - (i : ℝ) * θ) / 2 = θ := by ring
    have b : (((i : ℝ) + 1 + 1) * θ + (i : ℝ) * θ) / 2 = ((i : ℝ) + 1) * θ := by ring
    rw [a, b]
  have h2 : 2 * sin (((i : ℝ) + 1) * θ) * cos (((i : ℝ) + 1) * θ) = sin ((2 * (i : ℝ) + 2) * θ) := by
    rw [← sin_two_mul]; ring_nf
  have h3 : sin ((2 * (i : ℝ) + 2) * θ) = (-1) ^ (i + 1) * sin ((4 * (i : ℝ) + 4) * z) := by
    have e : (2 * (i : ℝ) + 2) * θ = (4 * (i : ℝ) + 4) * z - ((i + 1 : ℕ) : ℝ) * π := by
      rw [hθ]; push_cast; ring
    rw [e, sin_sub_nat_mul_pi]
  have hs := sin_theta z
  rw [← hθ] at hs
  have key : sin (((i : ℝ) + 1) * θ) * (sin (((i : ℝ) + 1 + 1) * θ) - sin ((i : ℝ) * θ))
      = sin θ * sin ((2 * (i : ℝ) + 2) * θ) := by
    rw [h1, ← h2]; ring
  rw [hs, h3] at key
  have hd : sin z - (2 * cos z - 1) * sin (((i : ℝ) + 1) * θ) * sin (((i : ℝ) + 1 + 1) * θ) / cos (2 * z) -
        (sin z - (2 * cos z - 1) * sin ((i : ℝ) * θ) * sin (((i : ℝ) + 1) * θ) / cos (2 * z))
      = -(2 * cos z - 1) * (sin (((i : ℝ) + 1) * θ) * (sin (((i : ℝ) + 1 + 1) * θ) - sin ((i : ℝ) * θ))) / cos (2 * z) := by
    ring
  rw [hd, key]
  field_simp

theorem blockB (z : ℝ) (i : ℕ) (hc : cos (2 * z) ≠ 0) :
    (tXb (i + 1)).eval z - (tXb i).eval z = (-1) ^ (i + 1) * (2 * cos z - 1) * cos ((4 * (i : ℝ) + 4) * z) := by
  rw [eval_tXb, eval_tXb]
  set θ := 2 * z - π / 2 with hθ
  have c1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [c1]
  -- 2 sin A cos B = sin (A − B) + sin (A + B), twice
  have h1 : 2 * sin (((i : ℝ) + 1) * θ) * cos (((i : ℝ) + 1 + 1) * θ)
      = sin (-θ) + sin ((2 * (i : ℝ) + 3) * θ) := by
    rw [two_mul_sin_mul_cos]; ring_nf
  have h2 : 2 * sin ((i : ℝ) * θ) * cos (((i : ℝ) + 1) * θ) = sin (-θ) + sin ((2 * (i : ℝ) + 1) * θ) := by
    rw [two_mul_sin_mul_cos]; ring_nf
  have h3 : sin ((2 * (i : ℝ) + 3) * θ) - sin ((2 * (i : ℝ) + 1) * θ) = 2 * sin θ * cos ((2 * (i : ℝ) + 2) * θ) := by
    rw [sin_sub_sin]
    have a : ((2 * (i : ℝ) + 3) * θ - (2 * (i : ℝ) + 1) * θ) / 2 = θ := by ring
    have b : ((2 * (i : ℝ) + 3) * θ + (2 * (i : ℝ) + 1) * θ) / 2 = (2 * (i : ℝ) + 2) * θ := by ring
    rw [a, b]
  have h4 : cos ((2 * (i : ℝ) + 2) * θ) = (-1) ^ (i + 1) * cos ((4 * (i : ℝ) + 4) * z) := by
    have e : (2 * (i : ℝ) + 2) * θ = (4 * (i : ℝ) + 4) * z - ((i + 1 : ℕ) : ℝ) * π := by
      rw [hθ]; push_cast; ring
    rw [e, cos_sub_nat_mul_pi]
  have hs := sin_theta z
  rw [← hθ] at hs
  have key : sin (((i : ℝ) + 1) * θ) * cos (((i : ℝ) + 1 + 1) * θ) - sin ((i : ℝ) * θ) * cos (((i : ℝ) + 1) * θ)
      = sin θ * cos ((2 * (i : ℝ) + 2) * θ) := by
    linear_combination (1 / 2) * h1 - (1 / 2) * h2 + (1 / 2) * h3
  rw [hs, h4] at key
  have hd : cos z - (2 * cos z - 1) * sin (((i : ℝ) + 1) * θ) * cos (((i : ℝ) + 1 + 1) * θ) / cos (2 * z) -
        (cos z - (2 * cos z - 1) * sin ((i : ℝ) * θ) * cos (((i : ℝ) + 1) * θ) / cos (2 * z))
      = -(2 * cos z - 1) * (sin (((i : ℝ) + 1) * θ) * cos (((i : ℝ) + 1 + 1) * θ) - sin ((i : ℝ) * θ) * cos (((i : ℝ) + 1) * θ)) / cos (2 * z) := by
    ring
  rw [hd, key]
  field_simp

/-- `X_0`, as upstream writes it before the loop, is the block formula at `i = 0`. -/
lemma tXa_zero (z : ℝ) : (tXa 0).eval z = sin z := by
  rw [eval_tXa]; simp
lemma tXb_zero (z : ℝ) : (tXb 0).eval z = cos z := by
  rw [eval_tXb]; simp

/-! ## Chords and sides between consecutive blocks -/

lemma sin_add_sub_z (A z : ℝ) : sin (A + z) + sin (A - z) = 2 * cos z * sin A := by
  rw [sin_add, sin_sub]; ring
lemma cos_add_sub_z (A z : ℝ) : cos (A + z) + cos (A - z) = 2 * cos z * cos A := by
  rw [cos_add, cos_sub]; ring

/-- The cross chord `{u_i, t_{i+1}}`, from the block increment: its vector is
`(−1)^i Φ_{4i+4}`. Stated with the base points as real numbers. -/
lemma cross_gen (A0 B0 A1 B1 z : ℝ) (i : ℕ)
    (hA : A1 - A0 = (-1) ^ (i + 1) * (2 * cos z - 1) * sin ((4 * (i : ℝ) + 4) * z))
    (hB : B1 - B0 = (-1) ^ (i + 1) * (2 * cos z - 1) * cos ((4 * (i : ℝ) + 4) * z)) :
    ((A1 - (-1) ^ (i + 1) * sin ((4 * (i : ℝ) + 5) * z)) - (A0 - (-1) ^ i * sin ((4 * (i : ℝ) + 3) * z))) ^ 2
      + ((B1 - (-1) ^ (i + 1) * cos ((4 * (i : ℝ) + 5) * z)) - (B0 - (-1) ^ i * cos ((4 * (i : ℝ) + 3) * z))) ^ 2 = 1 := by
  set A := (4 * (i : ℝ) + 4) * z
  have e5 : (4 * (i : ℝ) + 5) * z = A + z := by ring
  have e3 : (4 * (i : ℝ) + 3) * z = A - z := by ring
  rw [e5, e3]
  have hs := sin_add_sub_z A z
  have hc := cos_add_sub_z A z
  have p : ((-1 : ℝ) ^ (i + 1)) = -((-1) ^ i) := by rw [pow_succ]; ring
  have x : (A1 - (-1) ^ (i + 1) * sin (A + z)) - (A0 - (-1) ^ i * sin (A - z)) = (-1) ^ i * sin A := by
    rw [p] at hA ⊢; linear_combination hA + ((-1) ^ i) * hs
  have y : (B1 - (-1) ^ (i + 1) * cos (A + z)) - (B0 - (-1) ^ i * cos (A - z)) = (-1) ^ i * cos A := by
    rw [p] at hB ⊢; linear_combination hB + ((-1) ^ i) * hc
  rw [x, y]
  have := sin_sq_add_cos_sq A
  linear_combination ((-1 : ℝ) ^ i) ^ 2 * this + pm_sq i

theorem cross_ut (z : ℝ) (i : ℕ) (hc : cos (2 * z) ≠ 0) : nsq (ev z (tt (i + 1)) - ev z (tu i)) = 1 := by
  simp only [nsq_eq, ev, tt, tu, Tm.eval]
  have hA := blockA z i hc
  have hB := blockB z i hc
  have c : (4 * ((i + 1 : ℕ) : ℝ) + 1) = 4 * (i : ℝ) + 5 := by push_cast; ring
  rw [c]
  exact cross_gen _ _ _ _ z i hA hB

theorem cross0_ut (z : ℝ) (hc : cos (2 * z) ≠ 0) : nsq (ev z (tt 1) - ev z tu0) = 1 := by
  simp only [nsq_eq, ev, tt, tu0, Tm.eval]
  have hA := blockA z 0 hc
  have hB := blockB z 0 hc
  rw [tXa_zero] at hA; rw [tXb_zero] at hB
  have := cross_gen (sin z) (cos z) ((tXa 1).eval z) ((tXb 1).eval z) z 0 (by simpa using hA) (by simpa using hB)
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_zero, one_mul, pow_one, Nat.cast_one] at this ⊢
  convert this using 3 <;> ring_nf

/-- `|s((2c − 1)Φ_A − Φ_w)|² = 2 − 2c` when `cos (A − w) = c = cos z`. -/
lemma side_cross_gen (A w z s : ℝ) (hs : s ^ 2 = 1) (hw : cos (A - w) = cos z) :
    (s * ((2 * cos z - 1) * sin A - sin w)) ^ 2 + (s * ((2 * cos z - 1) * cos A - cos w)) ^ 2
      = 2 - 2 * cos z := by
  rw [cos_sub] at hw
  have e : (s * ((2 * cos z - 1) * sin A - sin w)) ^ 2 + (s * ((2 * cos z - 1) * cos A - cos w)) ^ 2
      = s ^ 2 * ((2 * cos z - 1) ^ 2 * (sin A ^ 2 + cos A ^ 2)
          - 2 * (2 * cos z - 1) * (cos A * cos w + sin A * sin w) + (sin w ^ 2 + cos w ^ 2)) := by ring
  rw [e, hs, sin_sq_add_cos_sq, sin_sq_add_cos_sq, hw]
  ring

theorem side_qt (z : ℝ) (i : ℕ) (hc : cos (2 * z) ≠ 0) :
    nsq (ev z (tt (i + 1)) - ev z (tq i)) = (2 * sin (z / 2)) ^ 2 := by
  simp only [nsq_eq, ev, tt, tq, Tm.eval]
  have hA := blockA z i hc
  have hB := blockB z i hc
  set A := (4 * (i : ℝ) + 4) * z
  have c : (4 * ((i + 1 : ℕ) : ℝ) + 1) * z = A + z := by push_cast; ring
  rw [c]
  have x : (tXa (i + 1)).eval z - (-1) ^ (i + 1) * sin (A + z) - (tXa i).eval z
      = (-1) ^ (i + 1) * ((2 * cos z - 1) * sin A - sin (A + z)) := by linear_combination hA
  have y : (tXb (i + 1)).eval z - (-1) ^ (i + 1) * cos (A + z) - (tXb i).eval z
      = (-1) ^ (i + 1) * ((2 * cos z - 1) * cos A - cos (A + z)) := by linear_combination hB
  rw [x, y, side_cross_gen _ _ _ _ (pm_sq (i + 1)) (by rw [show A - (A + z) = -z by ring, cos_neg]),
    sq_two_sin_half']

theorem side_uq (z : ℝ) (i : ℕ) (hc : cos (2 * z) ≠ 0) :
    nsq (ev z (tq (i + 1)) - ev z (tu i)) = (2 * sin (z / 2)) ^ 2 := by
  simp only [nsq_eq, ev, tq, tu, Tm.eval]
  have hA := blockA z i hc
  have hB := blockB z i hc
  set A := (4 * (i : ℝ) + 4) * z
  have c : (4 * (i : ℝ) + 3) * z = A - z := by ring
  rw [c]
  have p : ((-1 : ℝ) ^ i) = -((-1) ^ (i + 1)) := by rw [pow_succ]; ring
  have x : (tXa (i + 1)).eval z - ((tXa i).eval z - (-1) ^ i * sin (A - z))
      = (-1) ^ (i + 1) * ((2 * cos z - 1) * sin A - sin (A - z)) := by rw [p]; linear_combination hA
  have y : (tXb (i + 1)).eval z - ((tXb i).eval z - (-1) ^ i * cos (A - z))
      = (-1) ^ (i + 1) * ((2 * cos z - 1) * cos A - cos (A - z)) := by rw [p]; linear_combination hB
  rw [x, y, side_cross_gen _ _ _ _ (pm_sq (i + 1)) (by rw [show A - (A - z) = z by ring]),
    sq_two_sin_half']

theorem side0_qt (z : ℝ) (hc : cos (2 * z) ≠ 0) :
    nsq (ev z (tt 1) - ev z tq0) = (2 * sin (z / 2)) ^ 2 := by
  have h := side_qt z 0 hc
  simp only [nsq_eq, ev, tq, tq0, Tm.eval] at h ⊢
  rw [tXa_zero, tXb_zero] at h
  simpa [tt, Tm.eval] using h

theorem side0_uq (z : ℝ) (hc : cos (2 * z) ≠ 0) :
    nsq (ev z (tq 1) - ev z tu0) = (2 * sin (z / 2)) ^ 2 := by
  have h := side_uq z 0 hc
  simp only [nsq_eq, ev, tu, tu0, Tm.eval] at h ⊢
  rw [tXa_zero, tXb_zero] at h
  convert h using 3 <;> simp

end Chiquipoli.Family.Trig
