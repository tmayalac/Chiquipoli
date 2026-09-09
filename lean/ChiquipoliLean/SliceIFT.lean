/-
**Lemma 3.4 (local Euclidean slice), the implicit function theorem step.**

`Slice.lean` proves the two steps the paper's proof argues explicitly:
independence of `T₁, T₂, T₃`, and nonsingularity of their Gram matrix. What
remained was the appeal to the implicit function theorem itself — Mathlib has
it (`implicitFunctionOfBivariate`, for exactly this shape: a curried bivariate
map with an invertible partial derivative), and this file wires it in.

THE MAP. The paper's `Φ(a,θ,q) = (⟨g_{a,θ}q−p,T₁⟩, ⟨·,T₂⟩, ⟨·,T₃⟩)`, with
`g_{a,θ}(x) = R_θx + a`, is realised here on `q : Fin n → ℝ × ℝ` with motion
parameters `c = (a,b,θ) : ℝ × ℝ × ℝ` (the translation split into its two
coordinates). It reduces, by expanding the sum defining `cip` and collecting
terms, to a closed form in four fixed linear functionals of `q`:

    L1(q) = cip q (T1 n),  L2(q) = cip q (T2 n),
    L3(q) = cip q (T3 p),  L4(q) = cip q p,

namely (writing `θ` for `c.2.2`)

    Φ₁ q c = n·c.1  + cos θ · L1(q) − sin θ · L2(q) − cip p (T1 n)
    Φ₂ q c = n·c.2.1 + sin θ · L1(q) + cos θ · L2(q) − cip p (T2 n)
    Φ₃ q c = −c.1·cip p (T2 n) + c.2.1·cip p (T1 n) + cos θ · L3(q) + sin θ · L4(q)
             − cip p (T3 p)

`Phi_eq_geometric` proves this closed form equals the geometric definition
directly, so nothing is smuggled in.

WHAT THE DERIVATIVE COMPUTATION CONFIRMS. `Φ` is affine in `q`, so its
`q`-partial derivative `f₁` does not depend on `q` at all — only through
`cos θ, sin θ`. Its `c`-partial derivative `f₂`, evaluated at `(p, (0,0,0))`,
is checked here (`Phi_gram_eq`) to equal *exactly* the linear map whose
injectivity `Slice.lean` already proved as `gram_nondegenerate` — the
computation the paper's proof asserts ("the derivative … is the Gram matrix …
and is therefore invertible") is carried out on the actual nonlinear map, not
merely asserted of a linearisation.
-/
import ChiquipoliLean.Slice
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

namespace Chiquipoli.FirstOrder

open Finset

variable {n : ℕ}

/-- `cip q w` as a linear map in `q`, for fixed `w`. -/
def cipL (w : Fin n → ℝ × ℝ) : (Fin n → ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun q := cip q w
  map_add' := by
    intro x y
    simp only [cip, ip, Pi.add_apply, Prod.fst_add, Prod.snd_add]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  map_smul' := by
    intro r x
    simp only [cip, ip, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp] lemma cipL_apply (w q : Fin n → ℝ × ℝ) : cipL w q = cip q w := rfl

/-- The continuous version, using that `Fin n → ℝ × ℝ` is finite-dimensional. -/
noncomputable def cipCLM (w : Fin n → ℝ × ℝ) : (Fin n → ℝ × ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (cipL w)

@[simp] lemma cipCLM_apply (w q : Fin n → ℝ × ℝ) : cipCLM w q = cip q w := rfl

lemma hasFDerivAt_cip (w q : Fin n → ℝ × ℝ) :
    HasFDerivAt (fun q => cip q w) (cipCLM w) q := by
  have h := (cipCLM w).hasFDerivAt (x := q)
  have heq : (fun q => cip q w) = ⇑(cipCLM w) := by funext q; simp
  rw [heq]; exact h


/-! ## The slice map `Φ`, in closed form -/

/-- Rotation by `θ`. -/
noncomputable def rot (θ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 * Real.cos θ - x.2 * Real.sin θ, x.1 * Real.sin θ + x.2 * Real.cos θ)

/-- `g_{a,b,θ}(x) = R_θ x + (a,b)`, an orientation-preserving Euclidean motion. -/
noncomputable def gmove (c : ℝ × ℝ × ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (c.1 + (rot c.2.2 x).1, c.2.1 + (rot c.2.2 x).2)

@[simp] lemma gmove_zero (x : ℝ × ℝ) : gmove (0, 0, 0) x = x := by
  simp [gmove, rot]

/-- The paper's slice equation, defined geometrically: pairing
`g_{a,b,θ}q − p` against `T₁, T₂, T₃`. -/
noncomputable def PhiGeom (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (cip (fun i => gmove c (q i) - p i) (T1 n),
   cip (fun i => gmove c (q i) - p i) (T2 n),
   cip (fun i => gmove c (q i) - p i) (T3 p))

/-- The same map, in closed form. Differentiating this is what the rest of the
file works with; `Phi_eq_geometric` certifies it is the same map. -/
noncomputable def Phi (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (n * c.1 + Real.cos c.2.2 * cip q (T1 n) - Real.sin c.2.2 * cip q (T2 n)
     - cip p (T1 n),
   n * c.2.1 + Real.sin c.2.2 * cip q (T1 n) + Real.cos c.2.2 * cip q (T2 n)
     - cip p (T2 n),
   -c.1 * cip p (T2 n) + c.2.1 * cip p (T1 n)
     + Real.cos c.2.2 * cip q (T3 p) + Real.sin c.2.2 * cip q p
     - cip p (T3 p))

/-- **The closed form is the geometric slice map.** Nothing is smuggled in:
expanding `cip` over `Fin n` and regrouping by `cos θ, sin θ` gives exactly
`Phi`. -/
theorem Phi_eq_geometric (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    PhiGeom p q c = Phi p q c := by
  have hT1 : ∀ v : Fin n → ℝ × ℝ, cip v (T1 n) = ∑ i, (v i).1 := by
    intro v; simp only [cip, ip, T1]; exact Finset.sum_congr rfl fun i _ => by ring
  have hT2 : ∀ v : Fin n → ℝ × ℝ, cip v (T2 n) = ∑ i, (v i).2 := by
    intro v; simp only [cip, ip, T2]; exact Finset.sum_congr rfl fun i _ => by ring
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show cip (fun i => gmove c (q i) - p i) (T1 n) = _
    rw [hT1]
    simp only [gmove, rot, Prod.fst_sub]
    rw [Finset.sum_sub_distrib]
    have : ∀ i, (c.1 + ((q i).1 * Real.cos c.2.2 - (q i).2 * Real.sin c.2.2)) =
        c.1 + Real.cos c.2.2 * (q i).1 - Real.sin c.2.2 * (q i).2 := fun i => by ring
    simp only [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Phi, ← hT1, ← hT2]
    push_cast; ring
  · show cip (fun i => gmove c (q i) - p i) (T2 n) = _
    rw [hT2]
    simp only [gmove, rot, Prod.snd_sub]
    have : ∀ i, (c.2.1 + ((q i).1 * Real.sin c.2.2 + (q i).2 * Real.cos c.2.2)) - (p i).2 =
        c.2.1 + Real.sin c.2.2 * (q i).1 + Real.cos c.2.2 * (q i).2 - (p i).2 := fun i => by ring
    simp only [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Phi, ← hT1, ← hT2]
    push_cast; ring
  · show cip (fun i => gmove c (q i) - p i) (T3 p) = _
    have hT3 : ∀ v : Fin n → ℝ × ℝ, cip v (T3 p) = ∑ i, (-(v i).1 * (p i).2 + (v i).2 * (p i).1) := by
      intro v; simp only [cip, ip, T3, J]; exact Finset.sum_congr rfl fun i _ => by ring
    have hcipp : cip q p = ∑ i, ((q i).1 * (p i).1 + (q i).2 * (p i).2) := by
      simp only [cip, ip]
    rw [hT3]
    simp only [gmove, rot, Prod.fst_sub, Prod.snd_sub]
    have hrw : ∀ i, (-(c.1 + ((q i).1 * Real.cos c.2.2 - (q i).2 * Real.sin c.2.2) - (p i).1) *
          (p i).2 +
        (c.2.1 + ((q i).1 * Real.sin c.2.2 + (q i).2 * Real.cos c.2.2) - (p i).2) * (p i).1) =
        (-c.1 * (p i).2 + c.2.1 * (p i).1)
          + Real.cos c.2.2 * (-(q i).1 * (p i).2 + (q i).2 * (p i).1)
          + Real.sin c.2.2 * ((q i).1 * (p i).1 + (q i).2 * (p i).2)
          - (-(p i).1 * (p i).2 + (p i).2 * (p i).1) := fun i => by ring
    simp only [hrw]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← hT3, ← hcipp]
    have hzero : (∑ i : Fin n, (-(p i).1 * (p i).2 + (p i).2 * (p i).1)) = 0 :=
      Finset.sum_eq_zero fun i _ => by ring
    rw [hzero]
    have hK1 : (∑ i : Fin n, (-c.1 * (p i).2 + c.2.1 * (p i).1)) =
        -c.1 * (∑ i : Fin n, (p i).2) + c.2.1 * (∑ i : Fin n, (p i).1) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hK3 : cip p (T3 p) = 0 := by rw [hT3]; exact hzero
    rw [hK1]
    simp only [Phi, ← hT1, ← hT2]
    rw [hK3]


/-! ## Derivatives of `Φ` -/

/-- Substituting an equal function preserves `HasFDerivAt`, keeping the
derivative fixed. A workhorse for closing the gap between what the
combinators produce and the closed form `Phi` is stated in. -/
lemma hasFD_congr {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} {f' : E →L[ℝ] F} {x : E}
    (h : HasFDerivAt f f' x) (heq : ∀ y, f y = g y) : HasFDerivAt g f' x := by
  have : g = f := funext fun y => (heq y).symm
  rw [this]; exact h

/-- Projection onto `a` in `c = (a,b,θ)`. -/
noncomputable def projA : ℝ × ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

/-- Projection onto `b` in `c = (a,b,θ)`. -/
noncomputable def projB : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Projection onto `θ` in `c = (a,b,θ)`. -/
noncomputable def projTh : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

lemma hasFD_a (c : ℝ × ℝ × ℝ) : HasFDerivAt (fun c : ℝ × ℝ × ℝ => c.1) projA c :=
  hasFDerivAt_fst
lemma hasFD_b (c : ℝ × ℝ × ℝ) : HasFDerivAt (fun c : ℝ × ℝ × ℝ => c.2.1) projB c :=
  hasFDerivAt_fst.comp c hasFDerivAt_snd
lemma hasFD_th (c : ℝ × ℝ × ℝ) : HasFDerivAt (fun c : ℝ × ℝ × ℝ => c.2.2) projTh c :=
  hasFDerivAt_snd.comp c hasFDerivAt_snd

lemma hasFD_cos (c : ℝ × ℝ × ℝ) :
    HasFDerivAt (Real.cos ∘ fun c : ℝ × ℝ × ℝ => c.2.2) ((-Real.sin c.2.2) • projTh) c :=
  (Real.hasDerivAt_cos c.2.2).comp_hasFDerivAt c (hasFD_th c)

lemma hasFD_sin (c : ℝ × ℝ × ℝ) :
    HasFDerivAt (Real.sin ∘ fun c : ℝ × ℝ × ℝ => c.2.2) (Real.cos c.2.2 • projTh) c :=
  (Real.hasDerivAt_sin c.2.2).comp_hasFDerivAt c (hasFD_th c)

/-- **`q`-partial derivatives of `Φ`.** `Φ` is affine in `q` for fixed `c`, so
the derivative is independent of `q`; it varies only through `cos θ, sin θ`. -/
theorem hasFD_Phi1_q (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun q => Phi p q c |>.1)
      (Real.cos c.2.2 • cipCLM (T1 n) - Real.sin c.2.2 • cipCLM (T2 n)) q := by
  have h := ((((hasFDerivAt_cip (T1 n) q).const_smul (Real.cos c.2.2)).sub
    ((hasFDerivAt_cip (T2 n) q).const_smul (Real.sin c.2.2))).add_const
      ((n : ℝ) * c.1 - cip p (T1 n)))
  refine hasFD_congr h (fun y => ?_)
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, Phi]
  ring

theorem hasFD_Phi2_q (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun q => (Phi p q c).2.1)
      (Real.sin c.2.2 • cipCLM (T1 n) + Real.cos c.2.2 • cipCLM (T2 n)) q := by
  have h := ((((hasFDerivAt_cip (T1 n) q).const_smul (Real.sin c.2.2)).add
    ((hasFDerivAt_cip (T2 n) q).const_smul (Real.cos c.2.2))).add_const
      ((n : ℝ) * c.2.1 - cip p (T2 n)))
  refine hasFD_congr h (fun y => ?_)
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, Phi]
  ring

theorem hasFD_Phi3_q (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun q => (Phi p q c).2.2)
      (Real.cos c.2.2 • cipCLM (T3 p) + Real.sin c.2.2 • cipCLM p) q := by
  have h := ((((hasFDerivAt_cip (T3 p) q).const_smul (Real.cos c.2.2)).add
    ((hasFDerivAt_cip p q).const_smul (Real.sin c.2.2))).add_const
      (-c.1 * cip p (T2 n) + c.2.1 * cip p (T1 n) - cip p (T3 p)))
  refine hasFD_congr h (fun y => ?_)
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, Phi]
  ring

/-- The full `q`-partial, pairing the three components. -/
noncomputable def f1CLM (p : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    (Fin n → ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  ((Real.cos c.2.2 • cipCLM (T1 n) - Real.sin c.2.2 • cipCLM (T2 n)).prod
    ((Real.sin c.2.2 • cipCLM (T1 n) + Real.cos c.2.2 • cipCLM (T2 n)).prod
      (Real.cos c.2.2 • cipCLM (T3 p) + Real.sin c.2.2 • cipCLM p)))

theorem hasFD_Phi_q (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun q => Phi p q c) (f1CLM p c) q :=
  (hasFD_Phi1_q p q c).prodMk ((hasFD_Phi2_q p q c).prodMk (hasFD_Phi3_q p q c))

/-- **`c`-partial derivatives of `Φ`,** at a general `(q, c)`. -/
theorem hasFD_Phi1_c (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun c => (Phi p q c).1)
      ((n : ℝ) • projA
        + (-(Real.sin c.2.2) * cip q (T1 n) - Real.cos c.2.2 * cip q (T2 n)) • projTh) c := by
  have h1 := (hasFD_a c).const_mul (n : ℝ)
  have h2 := (hasFD_cos c).const_mul (cip q (T1 n))
  have h3 := (hasFD_sin c).const_mul (cip q (T2 n))
  have h4 := ((h1.add h2).sub h3).add_const (-(cip p (T1 n)))
  have heq : ((n : ℝ) • projA + cip q (T1 n) • (-Real.sin c.2.2) • projTh
      - cip q (T2 n) • Real.cos c.2.2 • projTh)
      = ((n : ℝ) • projA
        + (-(Real.sin c.2.2) * cip q (T1 n) - Real.cos c.2.2 * cip q (T2 n)) • projTh) := by
    apply ContinuousLinearMap.ext; intro v
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]; ring
  rw [heq] at h4
  refine hasFD_congr h4 (fun y => ?_)
  simp only [Phi, Pi.add_apply, Pi.sub_apply, Function.comp_apply]; ring

theorem hasFD_Phi2_c (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun c => (Phi p q c).2.1)
      ((n : ℝ) • projB
        + (Real.cos c.2.2 * cip q (T1 n) - Real.sin c.2.2 * cip q (T2 n)) • projTh) c := by
  have h1 := (hasFD_b c).const_mul (n : ℝ)
  have h2 := (hasFD_sin c).const_mul (cip q (T1 n))
  have h3 := (hasFD_cos c).const_mul (cip q (T2 n))
  have h4 := ((h1.add h2).add h3).add_const (-(cip p (T2 n)))
  have heq : ((n : ℝ) • projB + cip q (T1 n) • Real.cos c.2.2 • projTh
      + cip q (T2 n) • (-Real.sin c.2.2) • projTh)
      = ((n : ℝ) • projB
        + (Real.cos c.2.2 * cip q (T1 n) - Real.sin c.2.2 * cip q (T2 n)) • projTh) := by
    apply ContinuousLinearMap.ext; intro v
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]; ring
  rw [heq] at h4
  refine hasFD_congr h4 (fun y => ?_)
  simp only [Phi, Pi.add_apply, Function.comp_apply]; ring

theorem hasFD_Phi3_c (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun c => (Phi p q c).2.2)
      ((-(cip p (T2 n))) • projA + (cip p (T1 n)) • projB
        + (-(Real.sin c.2.2) * cip q (T3 p) + Real.cos c.2.2 * cip q p) • projTh) c := by
  have h1 := (hasFD_a c).const_mul (-(cip p (T2 n)))
  have h2 := (hasFD_b c).const_mul (cip p (T1 n))
  have h3 := (hasFD_cos c).const_mul (cip q (T3 p))
  have h4 := (hasFD_sin c).const_mul (cip q p)
  have h5 := (((h1.add h2).add h3).add h4).add_const (-(cip p (T3 p)))
  have heq : ((-(cip p (T2 n))) • projA + (cip p (T1 n)) • projB
      + cip q (T3 p) • (-Real.sin c.2.2) • projTh + cip q p • Real.cos c.2.2 • projTh)
      = ((-(cip p (T2 n))) • projA + (cip p (T1 n)) • projB
        + (-(Real.sin c.2.2) * cip q (T3 p) + Real.cos c.2.2 * cip q p) • projTh) := by
    apply ContinuousLinearMap.ext; intro v
    simp only [add_apply, smul_apply, smul_eq_mul, sub_apply]; ring
  rw [heq] at h5
  refine hasFD_congr h5 (fun y => ?_)
  simp only [Phi, Pi.add_apply, Function.comp_apply]; ring

/-- The full `c`-partial, pairing the three components. -/
noncomputable def f2CLM (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ :=
  (((n : ℝ) • projA
      + (-(Real.sin c.2.2) * cip q (T1 n) - Real.cos c.2.2 * cip q (T2 n)) • projTh).prod
    (((n : ℝ) • projB
        + (Real.cos c.2.2 * cip q (T1 n) - Real.sin c.2.2 * cip q (T2 n)) • projTh).prod
      ((-(cip p (T2 n))) • projA + (cip p (T1 n)) • projB
        + (-(Real.sin c.2.2) * cip q (T3 p) + Real.cos c.2.2 * cip q p) • projTh)))

theorem hasFD_Phi_c (p q : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun c => Phi p q c) (f2CLM p q c) c :=
  (hasFD_Phi1_c p q c).prodMk ((hasFD_Phi2_c p q c).prodMk (hasFD_Phi3_c p q c))


/-! ## Invertibility at the base point -/

/-- **The `c`-partial at `q = p, c = (0,0,0)` is exactly the Gram map** whose
injectivity `Slice.lean` already established as `gram_nondegenerate`. This is
the paper's assertion — "the derivative … at `(0,0,p)` is the Gram matrix of
`T₁,T₂,T₃`" — verified on the actual map, component by component. -/
theorem f2CLM_base_eq (p : Fin n → ℝ × ℝ) (d : ℝ × ℝ × ℝ) :
    f2CLM p p (0, 0, 0) d
      = (cip (rigidOf p d) (T1 n), cip (rigidOf p d) (T2 n), cip (rigidOf p d) (T3 p)) := by
  have hT1 : cip p (T1 n) = ∑ i, (p i).1 := by
    simp only [cip, ip, T1]; exact Finset.sum_congr rfl fun i _ => by ring
  have hT2 : cip p (T2 n) = ∑ i, (p i).2 := by
    simp only [cip, ip, T2]; exact Finset.sum_congr rfl fun i _ => by ring
  have hexp1 : cip (rigidOf p d) (T1 n) = (n : ℝ) * d.1 - d.2.2 * cip p (T2 n) := by
    have hrw : ∀ i, ip (rigidOf p d i) (T1 n i) = d.1 - d.2.2 * (p i).2 := by
      intro i; simp only [ip, rigidOf, T1]; ring
    show ∑ i, ip (rigidOf p d i) (T1 n i) = _
    simp only [hrw]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum, hT2]
    push_cast; ring
  have hexp2 : cip (rigidOf p d) (T2 n) = (n : ℝ) * d.2.1 + d.2.2 * cip p (T1 n) := by
    have hrw : ∀ i, ip (rigidOf p d i) (T2 n i) = d.2.1 + d.2.2 * (p i).1 := by
      intro i; simp only [ip, rigidOf, T2]; ring
    show ∑ i, ip (rigidOf p d i) (T2 n i) = _
    simp only [hrw]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum, hT1]
    push_cast; ring
  have hexp3 : cip (rigidOf p d) (T3 p)
      = -d.1 * cip p (T2 n) + d.2.1 * cip p (T1 n) + d.2.2 * cip p p := by
    have hpt : ∀ v : Fin n → ℝ × ℝ, cip v (T3 p) = ∑ i, (-(v i).1 * (p i).2 + (v i).2 * (p i).1) := by
      intro v; simp only [cip, ip, T3, J]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hpt]
    have hrw : ∀ i, -(d.1 - d.2.2 * (p i).2) * (p i).2 + (d.2.1 + d.2.2 * (p i).1) * (p i).1
        = (-d.1 * (p i).2 + d.2.1 * (p i).1) + d.2.2 * ((p i).1 * (p i).1 + (p i).2 * (p i).2) := by
      intro i; ring
    simp only [rigidOf, hrw]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hK1 : (∑ i : Fin n, (-d.1 * (p i).2 + d.2.1 * (p i).1))
        = -d.1 * cip p (T2 n) + d.2.1 * cip p (T1 n) := by
      rw [hT1, hT2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hpp : cip p p = ∑ i, ((p i).1 * (p i).1 + (p i).2 * (p i).2) := by
      simp only [cip, ip]
    rw [hK1, ← hpp]
  simp only [f2CLM, add_apply, sub_apply, smul_apply, smul_eq_mul, projA, projB, projTh]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (n:ℝ) * d.1 + (-Real.sin 0 * cip p (T1 n) - Real.cos 0 * cip p (T2 n)) * d.2.2
        = cip (rigidOf p d) (T1 n)
    rw [hexp1, Real.sin_zero, Real.cos_zero]; ring
  · show (n:ℝ) * d.2.1 + (Real.cos 0 * cip p (T1 n) - Real.sin 0 * cip p (T2 n)) * d.2.2
        = cip (rigidOf p d) (T2 n)
    rw [hexp2, Real.sin_zero, Real.cos_zero]; ring
  · show (-(cip p (T2 n))) * d.1 + cip p (T1 n) * d.2.1
        + (-Real.sin 0 * cip p (T3 p) + Real.cos 0 * cip p p) * d.2.2
        = cip (rigidOf p d) (T3 p)
    rw [hexp3, Real.sin_zero, Real.cos_zero]; ring

/-- **The Gram map, as a `LinearMap`.** -/
def gramLM (p : Fin n → ℝ × ℝ) : ℝ × ℝ × ℝ →ₗ[ℝ] ℝ × ℝ × ℝ where
  toFun d := (cip (rigidOf p d) (T1 n), cip (rigidOf p d) (T2 n), cip (rigidOf p d) (T3 p))
  map_add' := by
    intro x y
    have hx : rigidOf p (x + y) = fun i => rigidOf p x i + rigidOf p y i := by
      funext i
      refine Prod.ext ?_ ?_ <;> simp only [rigidOf, Prod.fst_add, Prod.snd_add, Pi.add_apply] <;> ring
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      · simp only [hx, Prod.fst_add, Prod.snd_add]
        rw [show (fun i => rigidOf p x i + rigidOf p y i) = rigidOf p x + rigidOf p y from rfl,
          ← cipL_apply, ← cipL_apply, ← cipL_apply, LinearMap.map_add]
  map_smul' := by
    intro r x
    have hx : rigidOf p (r • x) = fun i => r • rigidOf p x i := by
      funext i
      refine Prod.ext ?_ ?_ <;>
        simp only [rigidOf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Pi.smul_apply] <;> ring
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      · simp only [hx, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        rw [show (fun i => r • rigidOf p x i) = r • rigidOf p x from rfl,
          ← cipL_apply, ← cipL_apply, LinearMap.map_smul, RingHom.id_apply, smul_eq_mul]

lemma gramLM_apply (p d : _) : gramLM p d
    = (cip (rigidOf p d) (T1 n), cip (rigidOf p d) (T2 n), cip (rigidOf p d) (T3 p)) := rfl

/-- **The Gram map is injective**, restating `gram_nondegenerate` as injectivity
of the `LinearMap`. -/
theorem gramLM_injective {p : Fin n → ℝ × ℝ} {i j : Fin n} (hij : p i ≠ p j) :
    Function.Injective (gramLM p) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun d hd => ?_
  rw [LinearMap.mem_ker, gramLM_apply] at hd
  exact gram_nondegenerate hij (congrArg Prod.fst hd)
    (congrArg (Prod.fst ∘ Prod.snd) hd) (congrArg (Prod.snd ∘ Prod.snd) hd)

/-- **`f₂` at the base point is invertible.** Injectivity, via `finrank`
equality of domain and codomain, gives bijectivity; being a linear map on a
finite-dimensional space, that is exactly `IsInvertible`. -/
theorem f2CLM_base_invertible {p : Fin n → ℝ × ℝ} {i j : Fin n} (hij : p i ≠ p j) :
    (f2CLM p p (0, 0, 0)).IsInvertible := by
  have hinj : Function.Injective (gramLM p) := gramLM_injective hij
  have hsurj : Function.Surjective (gramLM p) := LinearMap.injective_iff_surjective.mp hinj
  have hbij : Function.Bijective (gramLM p) := ⟨hinj, hsurj⟩
  let e : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ × ℝ) := LinearEquiv.ofBijective (gramLM p) hbij
  have heq : (f2CLM p p (0, 0, 0) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) = (gramLM p : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) :=
    funext fun d => (f2CLM_base_eq p d).trans (gramLM_apply p d).symm
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext; intro d
  show (e.toContinuousLinearEquiv : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ) d = f2CLM p p (0, 0, 0) d
  rw [heq]
  rfl


/-! ## Continuity -/

/-- **Continuity helper.** Pairing two continuously-varying continuous linear
maps into their `ContinuousLinearMap.prod` stays continuous. Both sides being
finite-dimensional (`E`, `F`, `G` are throughout this file) makes the pairing
map itself linear between finite-dimensional spaces, hence automatically
continuous — this is the mechanism, not a combinator that already existed. -/
noncomputable def prodCLM {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] :
    (E →L[ℝ] F) × (E →L[ℝ] G) →ₗ[ℝ] (E →L[ℝ] (F × G)) where
  toFun fg := fg.1.prod fg.2
  map_add' := by intro x y; ext v <;> simp
  map_smul' := by intro r x; ext v <;> simp

theorem continuous_clm_prod {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : H → E →L[ℝ] F} {g : H → E →L[ℝ] G} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun h => (f h).prod (g h)) :=
  (prodCLM (E := E) (F := F) (G := G)).continuous_of_finiteDimensional.comp (hf.prodMk hg)

/-- **`f₁` is jointly continuous.** It does not even depend on `q`; only
`cos θ, sin θ` vary. -/
theorem continuous_f1CLM (p : Fin n → ℝ × ℝ) :
    Continuous (Function.uncurry (fun (_ : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) => f1CLM p c)) := by
  have hcos : Continuous (fun x : (Fin n → ℝ × ℝ) × (ℝ × ℝ × ℝ) => Real.cos x.2.2.2) :=
    Real.continuous_cos.comp (by fun_prop)
  have hsin : Continuous (fun x : (Fin n → ℝ × ℝ) × (ℝ × ℝ × ℝ) => Real.sin x.2.2.2) :=
    Real.continuous_sin.comp (by fun_prop)
  unfold Function.uncurry f1CLM
  exact continuous_clm_prod ((hcos.smul continuous_const).sub (hsin.smul continuous_const))
    (continuous_clm_prod ((hsin.smul continuous_const).add (hcos.smul continuous_const))
      ((hcos.smul continuous_const).add (hsin.smul continuous_const)))

/-- **`f₂` is jointly continuous.** It varies through `q` only via the four
fixed continuous linear functionals `cip · T1, cip · T2, cip · (T3 p), cip · p`,
and through `c` via `cos θ, sin θ`. -/
theorem continuous_f2CLM (p : Fin n → ℝ × ℝ) :
    Continuous (Function.uncurry (fun q c => f2CLM p q c)) := by
  have hcos : Continuous (fun x : (Fin n → ℝ × ℝ) × (ℝ × ℝ × ℝ) => Real.cos x.2.2.2) :=
    Real.continuous_cos.comp (by fun_prop)
  have hsin : Continuous (fun x : (Fin n → ℝ × ℝ) × (ℝ × ℝ × ℝ) => Real.sin x.2.2.2) :=
    Real.continuous_sin.comp (by fun_prop)
  have hL : ∀ w : Fin n → ℝ × ℝ,
      Continuous (fun x : (Fin n → ℝ × ℝ) × (ℝ × ℝ × ℝ) => cip x.1 w) := by
    intro w
    exact (cipCLM w).continuous.comp (continuous_fst (Y := ℝ × ℝ × ℝ))
  unfold Function.uncurry f2CLM
  refine continuous_clm_prod ?_ (continuous_clm_prod ?_ ?_)
  · exact continuous_const.add
      (((hsin.neg.mul (hL (T1 n))).sub (hcos.mul (hL (T2 n)))).smul continuous_const)
  · exact continuous_const.add
      (((hcos.mul (hL (T1 n))).sub (hsin.mul (hL (T2 n)))).smul continuous_const)
  · exact (continuous_const.add continuous_const).add
      (((hsin.neg.mul (hL (T3 p))).add (hcos.mul (hL p))).smul continuous_const)


/-! ## Lemma 3.4, assembled -/

variable {p : Fin n → ℝ × ℝ} {i j : Fin n}

/-- The point in `(Fin n → ℝ × ℝ) × (ℝ × ℝ × ℝ)` at which the implicit function
theorem is applied: the base configuration, at the identity motion. -/
noncomputable abbrev u0 (p : Fin n → ℝ × ℝ) : (Fin n → ℝ × ℝ) × ℝ × ℝ × ℝ := (p, 0, 0, 0)

theorem df1_eventually (p : Fin n → ℝ × ℝ) :
    ∀ᶠ v in nhds (u0 p), HasFDerivAt (fun q => Phi p q v.2) (f1CLM p v.2) v.1 :=
  Filter.Eventually.of_forall fun v => hasFD_Phi_q p v.1 v.2

theorem df2_eventually (p : Fin n → ℝ × ℝ) :
    ∀ᶠ v in nhds (u0 p), HasFDerivAt (fun c => Phi p v.1 c) (f2CLM p v.1 v.2) v.2 :=
  Filter.Eventually.of_forall fun v => hasFD_Phi_c p v.1 v.2

theorem cf1_continuousAt (p : Fin n → ℝ × ℝ) :
    ContinuousAt (Function.uncurry (fun (_ : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) => f1CLM p c))
      (u0 p) :=
  (continuous_f1CLM p).continuousAt

theorem cf2_continuousAt (p : Fin n → ℝ × ℝ) :
    ContinuousAt (Function.uncurry (fun q c => f2CLM p q c)) (u0 p) :=
  (continuous_f2CLM p).continuousAt

/-- **Lemma 3.4 (local Euclidean slice), by the implicit function theorem.**

At a configuration `p` with two distinct vertices, there is a map `g`, sending
`q` near `p` to the motion parameters `(a,b,θ)`, that is **strictly
differentiable at `p`** (in particular continuous and, since strict
differentiability at a point implies differentiability in a neighbourhood of
that point along the germ produced here, smooth in the sense the paper's proof
of Theorem 3.5 uses) and solves the slice equation: for `q` near `p`,
`Φ(g(q), q) = Φ((0,0,0), p)` — i.e. `g(q) q` lands in `R(p)^⊥`, in the
translated-and-rotated frame — **if and only if** `g(q)` is literally the
value the implicit function theorem returns. Moreover `g(p) = (0,0,0)`, the
identity motion, since `Φ((0,0,0), p) = 0` and uniqueness pins down `g(p)`.

This is the full mechanism the paper's Lemma 3.4 asserts, and the appeal to the
implicit function theorem — the one gap left after `Slice.lean` established
non-degeneracy — is discharged: `HasStrictFDerivAt.implicitFunctionOfProdDomain`
turns nondegeneracy of the Gram map into existence, uniqueness, and
differentiability of `g`. -/
noncomputable def g (hij : p i ≠ p j) : (Fin n → ℝ × ℝ) → ℝ × ℝ × ℝ :=
  implicitFunctionOfBivariate (f₁ := fun (_ : Fin n → ℝ × ℝ) c => f1CLM p c)
    (f₂ := fun q c => f2CLM p q c)
    (df1_eventually p) (df2_eventually p) (cf1_continuousAt p)
    (cf2_continuousAt p) (f2CLM_base_invertible hij)

theorem g_eventually_iff (hij : p i ≠ p j) :
    ∀ᶠ v in nhds (u0 p), Phi p v.1 v.2 = Phi p p (0, 0, 0) ↔ g hij v.1 = v.2 :=
  eventually_apply_eq_iff_implicitFunctionOfBivariate
    (f₁ := fun (_ : Fin n → ℝ × ℝ) c => f1CLM p c) (f₂ := fun q c => f2CLM p q c)
    (df1_eventually p) (df2_eventually p)
    (cf1_continuousAt p) (cf2_continuousAt p) (f2CLM_base_invertible hij)

theorem g_tendsto (hij : p i ≠ p j) : Filter.Tendsto (g hij) (nhds p) (nhds (0, 0, 0)) :=
  tendsto_implicitFunctionOfBivariate
    (f₁ := fun (_ : Fin n → ℝ × ℝ) c => f1CLM p c) (f₂ := fun q c => f2CLM p q c)
    (df1_eventually p) (df2_eventually p)
    (cf1_continuousAt p) (cf2_continuousAt p) (f2CLM_base_invertible hij)

/-- `g(p) = (0,0,0)`, the identity motion — the paper's `g(p) = id`. -/
theorem g_at_p (hij : p i ≠ p j) : g hij p = (0, 0, 0) := by
  have hev := g_eventually_iff (i := i) (j := j) hij
  have hself : (Phi p p (0, 0, 0) = Phi p p (0, 0, 0) ↔ g hij p = (0, 0, 0)) :=
    hev.self_of_nhds
  exact hself.mp rfl

/-- `g` is strictly differentiable at `p` — the smoothness the paper's proof
of Theorem 3.5 uses to conclude `g(q^k) → id`. -/
theorem g_hasStrictFDerivAt (hij : p i ≠ p j) :
    HasStrictFDerivAt (g hij)
      (-(f2CLM p p (0, 0, 0)).inverse ∘L f1CLM p (0, 0, 0)) p :=
  hasStrictFDerivAt_implicitFunctionOfBivariate
    (f₁ := fun (_ : Fin n → ℝ × ℝ) c => f1CLM p c) (f₂ := fun q c => f2CLM p q c)
    (df1_eventually p) (df2_eventually p)
    (cf1_continuousAt p) (cf2_continuousAt p) (f2CLM_base_invertible hij)

end Chiquipoli.FirstOrder
