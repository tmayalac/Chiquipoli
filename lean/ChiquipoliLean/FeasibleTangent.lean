/-
**The tangent cone is contained in the linearised cone — step C of Theorem 3.5.**

This is the analytic heart of the paper's proof:

  "For each side, `|q^k_{i+1} − q^k_i| = ℓ_k` and `|p_{i+1} − p_i| = ℓ`.
   Subtracting, dividing by `t_k`, and passing to the limit gives
   `⟪sᵢ, v_{i+1} − v_i⟫ = η`. For every active diameter edge,
   `|q^k_i − q^k_j| ≤ 1 = |p_i − p_j|`, and the corresponding first order limit
   gives `⟪u_ij, v_j − v_i⟫ ≤ 0`. Thus `(v, η) ∈ K_eq(p, ℓ)`."

TAYLOR IS EXACT HERE, AND THAT IS THE WHOLE POINT.

The general version of this step is a genuine piece of analysis: one writes
`f(x + u) − f(x) = f'[u] + o(‖u‖)`, divides by `t_k`, and has to show the
remainder still vanishes after division — which means converting the `o(‖u‖)`
of `HasFDerivAt` into a statement about the sequence `t_k`. Mathlib supports
that (`HasFDerivWithinAt.lim`), but it is the fiddliest part of the argument.

None of it is needed. The squared constraints chosen in `Feasible.lean` are
*quadratic polynomials*, so their Taylor expansion terminates:

  `eC i (x + w) = eC i x + eD[w] + eQ[w]`   (`eC_expand`)
  `dC i j (q + w) = dC i j q + dD[w] + dQ[w]` (`dC_expand`)

with `eQ`, `dQ` the quadratic parts and *no remainder at all*. These are ring
identities, proved by `ring`. Dividing by `t_k` and using homogeneity —
`eD` degree one, `eQ` degree two — gives

  `t_k⁻¹ (eC i (x + u_k) − eC i x) = eD[z_k] + t_k · eQ[z_k]`,  `z_k = t_k⁻¹ u_k`,

and the second term vanishes because `t_k → 0` and `eQ[z_k] → eQ[v]`. There is
no little-o and no derivative in the argument: only `ring` and continuity of two
polynomials.

The unsquared constraints would not permit this. It is the payoff of the design
decision recorded in the header of `Feasible.lean`.
-/
import ChiquipoliLean.FeasibleOpen

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder Filter Topology

variable {n : ℕ} [NeZero n]

/-! ## Bilinearity of `nsq` -/

omit [NeZero n] in
lemma ip_comm (a b : ℝ × ℝ) : ip a b = ip b a := by simp [ip]; ring

omit [NeZero n] in
lemma nsq_add (a h : ℝ × ℝ) : nsq (a + h) = nsq a + 2 * ip a h + nsq h := by
  simp [nsq, ip, Prod.fst_add, Prod.snd_add]; ring

omit [NeZero n] in
lemma nsq_smul (c : ℝ) (a : ℝ × ℝ) : nsq (c • a) = c ^ 2 * nsq a := by
  simp [nsq, ip, Prod.smul_fst, Prod.smul_snd]; ring

omit [NeZero n] in
lemma ip_smul_right (c : ℝ) (a b : ℝ × ℝ) : ip a (c • b) = c * ip a b := by
  simp [ip, Prod.smul_fst, Prod.smul_snd]; ring

/-! ## The quadratic parts -/

/-- The quadratic part of the side constraint. -/
def eQ (w : Cfg n) (eta : ℝ) (i : Fin n) : ℝ := nsq (w (i + 1) - w i) - eta ^ 2

omit [NeZero n] in
/-- The quadratic part of the diameter constraint. -/
def dQ (w : Cfg n) (i j : Fin n) : ℝ := nsq (w j - w i)

/-! ## Exact second-order expansion

No remainder: these are ring identities, not approximations. -/

lemma eC_expand (x w : Amb n) (i : Fin n) :
    eC i (x + w) = eC i x + eD x.1 x.2 w.1 w.2 i + eQ w.1 w.2 i := by
  have hsplit : (x + w).1 (i + 1) - (x + w).1 i
      = (x.1 (i + 1) - x.1 i) + (w.1 (i + 1) - w.1 i) := by
    simp [Prod.fst_add, Pi.add_apply]; abel
  simp only [eC, eD, eQ, hsplit, nsq_add, Prod.snd_add]
  ring

omit [NeZero n] in
lemma dC_expand (q w : Cfg n) (i j : Fin n) :
    dC i j (q + w) = dC i j q + dD q w i j + dQ w i j := by
  have hsplit : (q + w) j - (q + w) i = (q j - q i) + (w j - w i) := by
    simp [Pi.add_apply]; abel
  simp only [dC, dD, dQ, hsplit, nsq_add]
  ring

/-! ## Homogeneity -/

lemma eD_smul (p : Cfg n) (l c : ℝ) (v : Cfg n) (eta : ℝ) (i : Fin n) :
    eD p l (c • v) (c * eta) i = c * eD p l v eta i := by
  have h : (c • v) (i + 1) - (c • v) i = c • (v (i + 1) - v i) := by
    simp [Pi.smul_apply, smul_sub]
  simp only [eD, h, ip_smul_right]
  ring

lemma eQ_smul (c : ℝ) (w : Cfg n) (eta : ℝ) (i : Fin n) :
    eQ (c • w) (c * eta) i = c ^ 2 * eQ w eta i := by
  have h : (c • w) (i + 1) - (c • w) i = c • (w (i + 1) - w i) := by
    simp [Pi.smul_apply, smul_sub]
  simp only [eQ, h, nsq_smul]
  ring

omit [NeZero n] in
lemma dD_smul (q : Cfg n) (c : ℝ) (v : Cfg n) (i j : Fin n) :
    dD q (c • v) i j = c * dD q v i j := by
  have h : (c • v) j - (c • v) i = c • (v j - v i) := by
    simp [Pi.smul_apply, smul_sub]
  simp only [dD, h, ip_smul_right]
  ring

omit [NeZero n] in
lemma dQ_smul (c : ℝ) (w : Cfg n) (i j : Fin n) :
    dQ (c • w) i j = c ^ 2 * dQ w i j := by
  have h : (c • w) j - (c • w) i = c • (w j - w i) := by
    simp [Pi.smul_apply, smul_sub]
  simp only [dQ, h, nsq_smul]

/-! ## Continuity of the two polynomials -/

lemma continuous_eD (p : Cfg n) (l : ℝ) (i : Fin n) :
    Continuous fun z : Amb n => eD p l z.1 z.2 i := by
  unfold eD ip
  simp only [Prod.fst_sub, Prod.snd_sub]
  fun_prop

lemma continuous_eQ (i : Fin n) : Continuous fun z : Amb n => eQ z.1 z.2 i := by
  unfold eQ nsq ip
  simp only [Prod.fst_sub, Prod.snd_sub]
  fun_prop

omit [NeZero n] in
lemma continuous_dD (q : Cfg n) (i j : Fin n) :
    Continuous fun z : Amb n => dD q z.1 i j := by
  unfold dD ip
  simp only [Prod.fst_sub, Prod.snd_sub]
  fun_prop

omit [NeZero n] in
lemma continuous_dQ (i j : Fin n) : Continuous fun z : Amb n => dQ z.1 i j := by
  unfold dQ nsq ip
  simp only [Prod.fst_sub, Prod.snd_sub]
  fun_prop

/-! ## The blow-up limit

A *blow-up at `x`* is a sequence of competitors `x + u k` together with the
scales `t k = ‖u k‖` and the normalised directions `z k = (t k)⁻¹ • u k`. The
paper's `(v^k, η_k)` is our `z k`, and its `(v, η)` is the limit `z`. -/

/-- **The exact difference quotient.** No approximation: an identity between the
rescaled constraint increment and `eD[z k] + t k · eQ[z k]`. -/
lemma quotient_eC {x : Amb n} {u : ℕ → Amb n} {t : ℕ → ℝ} (ht : ∀ k, t k ≠ 0)
    (i : Fin n) (k : ℕ) :
    (t k)⁻¹ * (eC i (x + u k) - eC i x)
      = eD x.1 x.2 ((t k)⁻¹ • u k).1 ((t k)⁻¹ • u k).2 i
        + t k * eQ ((t k)⁻¹ • u k).1 ((t k)⁻¹ • u k).2 i := by
  have hu : u k = t k • (t k)⁻¹ • u k := (smul_inv_smul₀ (ht k) (u k)).symm
  set z := (t k)⁻¹ • u k with hz
  have hzsmul : (t k • z).1 = t k • z.1 := rfl
  have hzsmul2 : (t k • z).2 = t k * z.2 := rfl
  rw [hu, eC_expand]
  rw [hzsmul, hzsmul2, eD_smul, eQ_smul]
  have h0 : t k ≠ 0 := ht k
  field_simp
  ring

omit [NeZero n] in
/-- The same identity for the diameter constraint. -/
lemma quotient_dC {q : Cfg n} {u : ℕ → Amb n} {t : ℕ → ℝ} (ht : ∀ k, t k ≠ 0)
    (i j : Fin n) (k : ℕ) :
    (t k)⁻¹ * (dC i j (q + (u k).1) - dC i j q)
      = dD q ((t k)⁻¹ • u k).1 i j + t k * dQ ((t k)⁻¹ • u k).1 i j := by
  have hu : u k = t k • (t k)⁻¹ • u k := (smul_inv_smul₀ (ht k) (u k)).symm
  set z := (t k)⁻¹ • u k with hz
  have hzsmul : (t k • z).1 = t k • z.1 := rfl
  have huk : (u k).1 = t k • z.1 := by rw [hu]; rfl
  rw [huk, dC_expand, dD_smul, dQ_smul]
  have h0 : t k ≠ 0 := ht k
  field_simp
  ring

/-- **A side equality passes to the limit as an equality.**

If every competitor has the same side length relation as `x` — which is what
`Equilateral` says for both — then the limit direction satisfies the linearised
side equation. -/
theorem eD_eq_zero_of_blowup {x : Amb n} {u : ℕ → Amb n} {t : ℕ → ℝ} {z : Amb n}
    (ht : ∀ k, t k ≠ 0) (htz : Tendsto t atTop (𝓝 0))
    (hz : Tendsto (fun k => (t k)⁻¹ • u k) atTop (𝓝 z))
    (i : Fin n) (heq : ∀ k, eC i (x + u k) = eC i x) :
    eD x.1 x.2 z.1 z.2 i = 0 := by
  have hconst : Tendsto (fun k : ℕ => (t k)⁻¹ * (eC i (x + u k) - eC i x)) atTop (𝓝 0) := by
    simp only [heq, sub_self, mul_zero]
    exact tendsto_const_nhds
  have hlim : Tendsto (fun k : ℕ => (t k)⁻¹ * (eC i (x + u k) - eC i x)) atTop
      (𝓝 (eD x.1 x.2 z.1 z.2 i + 0 * eQ z.1 z.2 i)) := by
    simp only [quotient_eC ht i]
    exact ((continuous_eD x.1 x.2 i).tendsto z).comp hz |>.add
      (htz.mul (((continuous_eQ i).tendsto z).comp hz))
  rw [zero_mul, add_zero] at hlim
  exact (tendsto_nhds_unique hlim hconst)

omit [NeZero n] in
/-- **An active diameter inequality passes to the limit as an inequality.**

If the constraint is active at `x` (`dC i j q = 0`) and every competitor is
feasible (`dC i j (q + ·) ≤ 0`), the limit direction points weakly inward. -/
theorem dD_nonpos_of_blowup {q : Cfg n} {u : ℕ → Amb n} {t : ℕ → ℝ} {z : Amb n}
    (ht : ∀ k, 0 < t k) (htz : Tendsto t atTop (𝓝 0))
    (hz : Tendsto (fun k => (t k)⁻¹ • u k) atTop (𝓝 z))
    (i j : Fin n) (hact : dC i j q = 0) (hle : ∀ k, dC i j (q + (u k).1) ≤ 0) :
    dD q z.1 i j ≤ 0 := by
  have ht' : ∀ k, t k ≠ 0 := fun k => (ht k).ne'
  have hnonpos : ∀ k, (t k)⁻¹ * (dC i j (q + (u k).1) - dC i j q) ≤ 0 := by
    intro k
    have h1 : (0 : ℝ) ≤ (t k)⁻¹ := (inv_pos.mpr (ht k)).le
    have h2 : dC i j (q + (u k).1) - dC i j q ≤ 0 := by rw [hact]; simpa using hle k
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  have hlim : Tendsto (fun k : ℕ => (t k)⁻¹ * (dC i j (q + (u k).1) - dC i j q)) atTop
      (𝓝 (dD q z.1 i j + 0 * dQ z.1 i j)) := by
    simp only [quotient_dC ht' i j]
    exact ((continuous_dD q i j).tendsto z).comp hz |>.add
      (htz.mul (((continuous_dQ i j).tendsto z).comp hz))
  rw [zero_mul, add_zero] at hlim
  exact le_of_tendsto hlim (Eventually.of_forall hnonpos)

end Chiquipoli.Feasible
