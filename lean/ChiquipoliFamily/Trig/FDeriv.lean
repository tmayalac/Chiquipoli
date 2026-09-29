/-
# The derivative of upstream's `F`, and its sign in interval arithmetic

`hasDerivAt_F`: wherever `cos 2t ≠ 0`, `F_n` has derivative `Fd n t`, an explicit
trigonometric expression. `encFd` encloses `Fd` from a table of `(cos kt, sin kt)`
valid on a whole interval of `t`, and `F_strictAnti` turns a negative upper
bound into strict monotonicity of `F_n` there: so `F_n` has at most one zero in
the interval. This is how uniqueness of the root in upstream's bracket is proved
without expanding any polynomial.
-/
import ChiquipoliFamily.Trig.FSide

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real Tm FI

/-- The derivative of `x_n`. With `K = 2cos t − 1`, `g = cos(bt) sin(ct)`,
`D = cos 2t`, `b = n/4 − 2`, `c = n/4`: `x' = cos t − ((K' g + K g') D − K g D') / D²`. -/
noncomputable def xd (n : ℕ) (t : ℝ) : ℝ :=
  let b := (n : ℝ) / 4 - 2
  let c := (n : ℝ) / 4
  let K := 2 * cos t - 1
  let g := cos (b * t) * sin (c * t)
  let g' := -(sin (b * t) * b) * sin (c * t) + cos (b * t) * (cos (c * t) * c)
  cos t - (((-(2 * sin t)) * g + K * g') * cos (2 * t) - K * g * (-(sin (2 * t) * 2))) / cos (2 * t) ^ 2

/-- The derivative of `F_n`. -/
noncomputable def Fd (n : ℕ) (t : ℝ) : ℝ :=
  let a := (n : ℝ) / 2 - 1
  2 * (2 * Optigon.x n t + sin (a * t)) * (2 * xd n t + cos (a * t) * a)
    + 2 * cos (a * t) * (-(sin (a * t) * a)) - 2 * sin t

lemma x_eq (n : ℕ) : Optigon.x n = fun t =>
    sin t - (2 * cos t - 1) * (cos (((n : ℝ) / 4 - 2) * t) * sin ((n : ℝ) / 4 * t)) / cos (2 * t) := by
  funext t; unfold Optigon.x; ring_nf

theorem hasDerivAt_x (n : ℕ) (t : ℝ) (hD : cos (2 * t) ≠ 0) : HasDerivAt (Optigon.x n) (xd n t) t := by
  rw [x_eq]
  have hK : HasDerivAt (fun t => 2 * cos t - 1) (-(2 * sin t)) t := by
    have := ((Real.hasDerivAt_cos t).const_mul 2).sub_const 1
    simpa using this
  have hb : HasDerivAt (fun t => cos (((n : ℝ) / 4 - 2) * t)) (-(sin (((n : ℝ) / 4 - 2) * t) * ((n : ℝ) / 4 - 2))) t := by
    have := ((hasDerivAt_id t).const_mul ((n : ℝ) / 4 - 2)).cos
    simpa using this
  have hc : HasDerivAt (fun t => sin ((n : ℝ) / 4 * t)) (cos ((n : ℝ) / 4 * t) * ((n : ℝ) / 4)) t := by
    have := ((hasDerivAt_id t).const_mul ((n : ℝ) / 4)).sin
    simpa using this
  have hDd : HasDerivAt (fun t => cos (2 * t)) (-(sin (2 * t) * 2)) t := by
    have := ((hasDerivAt_id t).const_mul (2 : ℝ)).cos
    simpa using this
  have hg := hb.mul hc
  have hq := (hK.mul hg).div hDd hD
  have hx := (Real.hasDerivAt_sin t).sub hq
  have hfun : (fun t => sin t - (2 * cos t - 1) * (cos (((n : ℝ) / 4 - 2) * t) * sin ((n : ℝ) / 4 * t)) / cos (2 * t))
      = (sin - (fun t => 2 * cos t - 1) * ((fun t => cos (((n : ℝ) / 4 - 2) * t)) * fun t => sin ((n : ℝ) / 4 * t))
          / fun t => cos (2 * t)) := by
    funext s; simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply]
  rw [hfun]
  refine hx.congr_deriv ?_
  unfold xd; simp only [Pi.mul_apply]

theorem hasDerivAt_F (n : ℕ) (t : ℝ) (hD : cos (2 * t) ≠ 0) : HasDerivAt (Optigon.F n) (Fd n t) t := by
  have hx := hasDerivAt_x n t hD
  let a := (n : ℝ) / 2 - 1
  have hsa : HasDerivAt (fun t => sin (a * t)) (cos (a * t) * a) t := by
    have := ((hasDerivAt_id t).const_mul a).sin
    simpa using this
  have hca : HasDerivAt (fun t => cos (a * t)) (-(sin (a * t) * a)) t := by
    have := ((hasDerivAt_id t).const_mul a).cos
    simpa using this
  have hh : HasDerivAt (fun t => sin (t / 2)) (cos (t / 2) * (1 / 2)) t := by
    have := ((hasDerivAt_id t).div_const (2 : ℝ)).sin
    simpa [div_eq_mul_inv] using this
  have hu := (hx.const_mul 2).add hsa
  have hF := ((hu.pow 2).add (hca.pow 2)).sub ((hh.pow 2).const_mul 4)
  have e : Optigon.F n = fun t => (2 * Optigon.x n t + sin (a * t)) ^ 2 + cos (a * t) ^ 2 - 4 * sin (t / 2) ^ 2 := by
    funext s; unfold Optigon.F; rfl
  rw [e]
  refine hF.congr_deriv ?_
  simp only [Fd, Pi.add_apply, a]
  have : 2 * sin t = 4 * (2 * sin (t / 2) * cos (t / 2)) * (1 / 2) := by
    rw [← sin_two_mul]; ring_nf
  rw [this]; push_cast; ring

/-- **Strict monotonicity from a negative derivative.** -/
theorem F_strictAnti (n : ℕ) (a b : ℝ) (hD : ∀ t ∈ Set.Icc a b, cos (2 * t) ≠ 0)
    (hneg : ∀ t ∈ Set.Icc a b, Fd n t < 0) : StrictAntiOn (Optigon.F n) (Set.Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b)
  · intro t ht
    exact (hasDerivAt_F n t (hD t ht)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' := interior_subset ht
    rw [(hasDerivAt_F n t (hD t ht')).deriv]
    exact hneg t ht'

theorem F_continuousOn (n : ℕ) (a b : ℝ) (hD : ∀ t ∈ Set.Icc a b, cos (2 * t) ≠ 0) :
    ContinuousOn (Optigon.F n) (Set.Icc a b) := fun t ht =>
  (hasDerivAt_F n t (hD t ht)).continuousAt.continuousWithinAt

/-! ## `Fd` in interval arithmetic -/

/-- `Fd` at `n = 8m` from the table (an interval of `t`). The constants `n/4 − 2`,
`n/4`, `n/2 − 1` are the integers `2m − 2`, `2m`, `4m − 1`. -/
def encFd (m : ℕ) (tab : List (FI × FI)) : Option FI := do
  let e1 ← look tab 1
  let e2 ← look tab 2
  let eb ← look tab (2 * m - 2)
  let ec ← look tab (2 * m)
  let ea ← look tab (4 * m - 1)
  let two := ofInt 2
  let bI := ofInt (2 * (m : ℤ) - 2)
  let cI := ofInt (2 * (m : ℤ))
  let aI := ofInt (4 * (m : ℤ) - 1)
  let K := sub (mul two e1.1) (ofInt 1)
  let g := mul eb.1 ec.2
  let g' := add (neg (mul (mul eb.2 bI) ec.2)) (mul eb.1 (mul ec.1 cI))
  let num := sub (mul (add (mul (neg (mul two e1.2)) g) (mul K g')) e2.1) (mul (mul K g) (neg (mul e2.2 two)))
  let q ← div num (mul e2.1 e2.1)
  let xdI := sub e1.1 q
  let x ← div (mul K g) e2.1
  let x := sub e1.2 x
  let u := add (mul two x) ea.2
  some (sub (add (mul (mul two u) (add (mul two xdI) (mul ea.1 aI))) (mul (mul two ea.1) (neg (mul ea.2 aI))))
    (mul two e1.2))

/-- **Soundness of `encFd`.** -/
theorem encFd_sound {z : ℝ} {tab : List (FI × FI)} (hv : TabValid z tab) (m : ℕ) (hm : 1 ≤ m)
    {I : FI} (h : encFd m tab = some I) : FI.mem (Fd (8 * m) z) I := by
  unfold encFd at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨e1, h1, e2, h2, eb, hb, ec, hc, ea, ha, q, hq, x, hx, hI⟩ := h
  simp only [Option.some.injEq] at hI
  subst hI
  have c1 := look_sound hv h1; have c2 := look_sound hv h2
  have cb := look_sound hv hb; have cc := look_sound hv hc; have ca := look_sound hv ha
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at c1 c2
  have htwo : FI.mem (2 : ℝ) (ofInt 2) := by simpa using mem_ofInt 2
  have hone : FI.mem (1 : ℝ) (ofInt 1) := by simpa using mem_ofInt 1
  have hbI : FI.mem ((2 * (m : ℝ) - 2)) (ofInt (2 * (m : ℤ) - 2)) := by simpa using mem_ofInt (2 * (m : ℤ) - 2)
  have hcI : FI.mem ((2 * (m : ℝ))) (ofInt (2 * (m : ℤ))) := by simpa using mem_ofInt (2 * (m : ℤ))
  have haI : FI.mem ((4 * (m : ℝ) - 1)) (ofInt (4 * (m : ℤ) - 1)) := by simpa using mem_ofInt (4 * (m : ℤ) - 1)
  have hK := mem_sub (mem_mul htwo c1.1) hone
  have hg := mem_mul cb.1 cc.2
  have hg' := mem_add (mem_neg (mem_mul (mem_mul cb.2 hbI) cc.2)) (mem_mul cb.1 (mem_mul cc.1 hcI))
  have hnum := mem_sub (mem_mul (mem_add (mem_mul (mem_neg (mem_mul htwo c1.2)) hg) (mem_mul hK hg')) c2.1)
    (mem_mul (mem_mul hK hg) (mem_neg (mem_mul c2.2 htwo)))
  have hqq := mem_div hnum (mem_mul c2.1 c2.1) hq
  have hxd := mem_sub c1.1 hqq
  have hxx := mem_sub c1.2 (mem_div (mem_mul hK hg) c2.1 hx)
  have hu := mem_add (mem_mul htwo hxx) ca.2
  have hF := mem_sub (mem_add (mem_mul (mem_mul htwo hu) (mem_add (mem_mul htwo hxd) (mem_mul ca.1 haI)))
    (mem_mul (mem_mul htwo ca.1) (mem_neg (mem_mul ca.2 haI)))) (mem_mul htwo c1.2)
  convert hF using 1
  unfold Fd xd Optigon.x
  simp only
  have b0 : (((8 * m : ℕ) : ℝ) / 4 - 2) = ((2 * m - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have b1 : (((8 * m : ℕ) : ℝ) / 4 - 2) = 2 * (m : ℝ) - 2 := by push_cast; ring
  have c0 : ((8 * m : ℕ) : ℝ) / 4 = ((2 * m : ℕ) : ℝ) := by push_cast; ring
  have c1' : ((8 * m : ℕ) : ℝ) * z / 4 = ((2 * m : ℕ) : ℝ) * z := by push_cast; ring
  have a0 : (((8 * m : ℕ) : ℝ) / 2 - 1) = ((4 * m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have a1 : (((8 * m : ℕ) : ℝ) / 2 - 1) = 4 * (m : ℝ) - 1 := by push_cast; ring
  rw [c1']
  -- rewrite the angles to the table's integer multiples, and the coefficients to reals
  conv_lhs => rw [show ((8 * m : ℕ) : ℝ) / 4 * z = ((2 * m : ℕ) : ℝ) * z by push_cast; ring]
  rw [b0, a0]
  have eb2 : ((2 * m - 2 : ℕ) : ℝ) = 2 * (m : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have ea4 : ((4 * m - 1 : ℕ) : ℝ) = 4 * (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have ec2 : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  simp only [eb2, ea4, ec2]
  push_cast
  ring_nf

end Chiquipoli.Family.Trig
