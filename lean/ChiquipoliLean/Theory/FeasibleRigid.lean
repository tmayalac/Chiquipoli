/-
**Invariance of the constraints under Euclidean motions — step D of Theorem 3.5,
part one.**

The paper's proof normalises each competitor by a motion:

  "Apply Lemma 3.4 to each `q^k`. ... After replacing `q^k` by `g(q^k)q^k`, the
   configurations remain feasible, equilateral, and noncongruent to `p`, still
   converge to `p`, and satisfy `q^k − p ∈ R(p)^⊥`."

"Remain feasible, equilateral" is the content of this file: the constraint
functions of `Feasible.lean` do not see an orientation-preserving Euclidean
motion. The motion `gmove` is the one `SliceIFT.lean` already uses, so the two
halves of step D compose without a translation layer.

The mechanism is two lines of trigonometry. A motion acts on a *difference* of
two points as the rotation alone — the translation cancels (`gmove_sub`) — and
a rotation preserves the inner product (`ip_rot`, the only place
`sin² + cos² = 1` is used). Everything else follows: `nsq`, hence `eC` and `dC`,
hence `IsFeasible`.

Orientation is preserved as well (`cross_move`), because `J` commutes with
rotation (`J_rot`). So the labelled cyclic order survives too, and
`IsFeasibleConvex` is invariant — which is what lets the normalisation be
applied to the paper's convex competitors and not only to the wider class of
`IsFeasible`.
-/
import ChiquipoliLean.Theory.FeasibleTangent
import ChiquipoliLean.Theory.SliceIFT

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder

variable {n : ℕ} [NeZero n]

/-! ## Rotations -/

omit [NeZero n] in
/-- A rotation is linear on differences. -/
lemma rot_sub (t : ℝ) (x y : ℝ × ℝ) : rot t x - rot t y = rot t (x - y) := by
  simp [rot, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]; constructor <;> ring

omit [NeZero n] in
/-- A rotation preserves the Euclidean inner product. This is the only place the
Pythagorean identity is used. -/
lemma ip_rot (t : ℝ) (a b : ℝ × ℝ) : ip (rot t a) (rot t b) = ip a b := by
  have h := Real.sin_sq_add_cos_sq t
  simp only [ip, rot]
  linear_combination (a.1 * b.1 + a.2 * b.2) * h

omit [NeZero n] in
lemma nsq_rot (t : ℝ) (a : ℝ × ℝ) : nsq (rot t a) = nsq a := ip_rot t a a

omit [NeZero n] in
/-- `J` commutes with rotation: rotating then turning left is turning left then
rotating. This is what makes orientation a rotation invariant. -/
lemma J_rot (t : ℝ) (a : ℝ × ℝ) : J (rot t a) = rot t (J a) := by
  simp [J, rot, Prod.ext_iff]; constructor <;> ring

/-! ## Motions

A motion acts on a difference of two points as its rotation part: the
translation cancels. -/

omit [NeZero n] in
lemma gmove_sub (c : ℝ × ℝ × ℝ) (x y : ℝ × ℝ) :
    gmove c x - gmove c y = rot c.2.2 (x - y) := by
  simp [gmove, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, rot]
  constructor <;> ring

omit [NeZero n] in
lemma nsq_gmove_sub (c : ℝ × ℝ × ℝ) (x y : ℝ × ℝ) :
    nsq (gmove c x - gmove c y) = nsq (x - y) := by
  rw [gmove_sub, nsq_rot]

/-- The motion `c` applied to every vertex of a configuration. -/
noncomputable def moveCfg (c : ℝ × ℝ × ℝ) (q : Cfg n) : Cfg n := fun i => gmove c (q i)

omit [NeZero n] in
@[simp] lemma moveCfg_zero (q : Cfg n) : moveCfg (0, 0, 0) q = q := by
  funext i; simp [moveCfg]

/-! ## The constraints are invariant -/

@[simp] lemma eC_move (c : ℝ × ℝ × ℝ) (x : Amb n) (i : Fin n) :
    eC i (moveCfg c x.1, x.2) = eC i x := by
  simp only [eC, moveCfg, nsq_gmove_sub]

omit [NeZero n] in
@[simp] lemma dC_move (c : ℝ × ℝ × ℝ) (q : Cfg n) (i j : Fin n) :
    dC i j (moveCfg c q) = dC i j q := by
  simp only [dC, moveCfg, nsq_gmove_sub]

omit [NeZero n] in
/-- Orientation is preserved, so the labelled cyclic order is too. -/
@[simp] lemma cross_move (c : ℝ × ℝ × ℝ) (x y z : ℝ × ℝ) :
    cross (gmove c x) (gmove c y) (gmove c z) = cross x y z := by
  simp only [cross, gmove_sub, J_rot, ip_rot]

/-! ## Feasibility is invariant -/

omit [NeZero n] in
@[simp] lemma small_move (c : ℝ × ℝ × ℝ) (q : Cfg n) : Small (moveCfg c q) ↔ Small q := by
  simp [Small]

@[simp] lemma equilateral_move (c : ℝ × ℝ × ℝ) (x : Amb n) :
    Equilateral (moveCfg c x.1, x.2) ↔ Equilateral x := by
  simp [Equilateral]

@[simp] lemma convexOrdered_move (c : ℝ × ℝ × ℝ) (q : Cfg n) :
    ConvexOrdered (moveCfg c q) ↔ ConvexOrdered q := by
  simp [ConvexOrdered, moveCfg]

/-- **The normalisation preserves feasibility.** The paper's "the configurations
remain feasible, equilateral". -/
@[simp] theorem isFeasible_move (c : ℝ × ℝ × ℝ) (x : Amb n) :
    IsFeasible (moveCfg c x.1, x.2) ↔ IsFeasible x := by
  simp [IsFeasible]

/-- The same for the paper's convex feasible set. -/
@[simp] theorem isFeasibleConvex_move (c : ℝ × ℝ × ℝ) (x : Amb n) :
    IsFeasibleConvex (moveCfg c x.1, x.2) ↔ IsFeasibleConvex x := by
  simp [IsFeasibleConvex]

/-! ## The normalisation, step D part two

`SliceIFT.g` sends a configuration near `p` to the motion parameters that put it
in `R(p)^⊥`. Applying that motion is the paper's "replacing `q^k` by
`g(q^k)q^k`". Three things must survive: feasibility (above), convergence to
`p`, and the slice condition itself. -/

section Normalise

open Filter Topology

variable {p : Cfg n} {ii jj : Fin n}

/-- A rigid motion depends continuously on its parameters and its argument. -/
lemma continuous_gmove : Continuous fun x : (ℝ × ℝ × ℝ) × (ℝ × ℝ) => gmove x.1 x.2 := by
  unfold gmove rot
  fun_prop

omit [NeZero n] in
lemma continuous_moveCfg :
    Continuous fun x : (ℝ × ℝ × ℝ) × Cfg n => moveCfg x.1 x.2 := by
  refine continuous_pi fun k => ?_
  exact continuous_gmove.comp
    (Continuous.prodMk continuous_fst ((continuous_apply k).comp continuous_snd))

/-- The competitor after normalisation: `g(q)·q`. -/
noncomputable def normCfg (hij : p ii ≠ p jj) (q : Cfg n) : Cfg n :=
  moveCfg (g hij q) q

omit [NeZero n] in
@[simp] lemma normCfg_at_p (hij : p ii ≠ p jj) : normCfg hij p = p := by
  simp [normCfg, g_at_p hij]

omit [NeZero n] in
/-- **The normalisation is continuous at `p` and fixes it.** With `g(p) = id`
this is the paper's "`g(q^k) → id`, so the replaced configurations still
converge to `p`". -/
theorem tendsto_normCfg (hij : p ii ≠ p jj) :
    Tendsto (normCfg hij) (𝓝 p) (𝓝 p) := by
  have hpair : Tendsto (fun q => (g hij q, q)) (𝓝 p) (𝓝 ((0, 0, 0), p)) := by
    rw [nhds_prod_eq]; exact (g_tendsto hij).prodMk tendsto_id
  have hcomp := (continuous_moveCfg.tendsto ((0, 0, 0), p)).comp hpair
  unfold normCfg
  simpa [Function.comp_def] using hcomp

omit [NeZero n] in
/-- **The normalised competitor satisfies the slice equation.** This is the
`Φ = 0` that `SliceIFT` solves, read geometrically: `g(q)q − p` pairs to zero
against each of `T₁, T₂, T₃`. -/
theorem eventually_phiGeom_zero (hij : p ii ≠ p jj) :
    ∀ᶠ q in 𝓝 p, PhiGeom p q (g hij q) = 0 := by
  have hbase : Phi p p (0, 0, 0) = 0 := by
    rw [← Phi_eq_geometric]
    simp [PhiGeom, cip, ip]
  have hmap : Tendsto (fun q : Cfg n => ((q : Cfg n), g hij q)) (𝓝 p) (𝓝 (u0 p)) := by
    have h : Tendsto (fun q : Cfg n => ((q : Cfg n), g hij q)) (𝓝 p) (𝓝 (p, (0, 0, 0))) := by
      rw [nhds_prod_eq]; exact tendsto_id.prodMk (g_tendsto hij)
    simpa [u0] using h
  refine (hmap.eventually (g_eventually_iff hij)).mono fun q hq => ?_
  rw [Phi_eq_geometric]
  rw [← hbase]
  exact hq.mpr rfl

end Normalise

/-! ## From the slice equation to the slice condition

`PhiGeom = 0` says the normalised displacement pairs to zero against the three
generators. `no_admissible_direction` wants it to pair to zero against *every*
infinitesimal rigid motion. The two are the same statement, because `rigidOf` is
by definition the linear combination of the generators (`rigidOf_eq_comb`) and
`cip` is bilinear. -/

omit [NeZero n] in
lemma cip_rigidOf_right (w p : Cfg n) (c : ℝ × ℝ × ℝ) :
    cip w (rigidOf p c)
      = c.1 * cip w (T1 n) + c.2.1 * cip w (T2 n) + c.2.2 * cip w (T3 p) := by
  simp only [cip, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [rigidOf, T1, T2, T3, J, ip]
  ring

omit [NeZero n] in
/-- Orthogonality to the three generators is orthogonality to all of `R(p)`. -/
theorem slice_of_generators {w p : Cfg n} {iota : Type*} [Fintype iota]
    {D : Data n iota} (hDp : D.p = p)
    (h1 : cip w (T1 n) = 0) (h2 : cip w (T2 n) = 0) (h3 : cip w (T3 p) = 0) :
    ∀ r, D.R r → cip w r = 0 := by
  rintro r ⟨t, om, hr⟩
  have hrig : r = rigidOf p (t.1, t.2, om) := by
    funext k
    rw [hr k, hDp]
    simp only [rigidOf, J, Prod.smul_mk, smul_eq_mul]
    rw [Prod.ext_iff]
    constructor <;> (simp only [Prod.fst_add, Prod.snd_add]; try ring)
  rw [hrig, cip_rigidOf_right, h1, h2, h3]
  ring

end Chiquipoli.Feasible
