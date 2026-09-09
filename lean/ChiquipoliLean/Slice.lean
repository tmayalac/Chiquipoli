/-
**Lemma 3.4 (local Euclidean slice): the linear algebra it rests on.**

The paper's proof has three steps. Two are argued in detail and are formalised
here, for arbitrary `n`:

  1. `T₁ = ((1,0),…)`, `T₂ = ((0,1),…)`, `T₃ = (Jp₀,…,Jpₙ₋₁)` are linearly
     independent as soon as two vertices are distinct — so they are a basis of
     `R(p)`, which they visibly span. That is `rigid_indep`.

  2. The derivative of the slice equation with respect to the motion parameters
     `(a, θ)` at the identity is the Gram matrix of `T₁, T₂, T₃`, and a Gram
     matrix of independent vectors is invertible. That is `gram_injective`.

The third step is the citation: the implicit function theorem then produces the
smooth `q ↦ g(q)`. That application is **not** formalised — it needs the smooth
structure on the orientation-preserving Euclidean group and the Fréchet
derivative of `θ ↦ R_θ q`. See `lean/README.md`; it is part of the same analytic
half of Theorem 3.5 that remains outstanding.

What this file therefore establishes is that the slice equation is
*nondegenerate at the identity* — the hypothesis the implicit function theorem
consumes. Nondegeneracy is the mathematical content; the rest is machinery.
-/
import ChiquipoliLean.FirstOrder

namespace Chiquipoli.FirstOrder

open Finset

variable {n : ℕ}

/-- `T₁`: the infinitesimal translation in the first coordinate. -/
def T1 (n : ℕ) : Fin n → ℝ × ℝ := fun _ => (1, 0)

/-- `T₂`: the infinitesimal translation in the second coordinate. -/
def T2 (n : ℕ) : Fin n → ℝ × ℝ := fun _ => (0, 1)

/-- `T₃`: the infinitesimal rotation about the origin. -/
def T3 (p : Fin n → ℝ × ℝ) : Fin n → ℝ × ℝ := fun i => J (p i)

/-- A general infinitesimal rigid motion, `a·T₁ + b·T₂ + ω·T₃`. -/
def rigidOf (p : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) : Fin n → ℝ × ℝ :=
  fun i => (c.1 - c.2.2 * (p i).2, c.2.1 + c.2.2 * (p i).1)

/-- `rigidOf` really is the linear combination it is named for. -/
lemma rigidOf_eq_comb (p : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) (i : Fin n) :
    rigidOf p c i = c.1 • T1 n i + c.2.1 • T2 n i + c.2.2 • T3 p i := by
  simp only [rigidOf, T1, T2, T3, J, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
    Prod.mk.injEq]
  constructor <;> ring

/-- **Step 1: `T₁, T₂, T₃` are linearly independent** as soon as two vertices
are distinct. This is the paper's "subtraction at two distinct vertices gives
`ω J(pᵢ − pⱼ) = 0`, hence `ω = 0`, and then `a = 0`". -/
theorem rigid_indep {p : Fin n → ℝ × ℝ} {i j : Fin n} (hij : p i ≠ p j)
    {c : ℝ × ℝ × ℝ} (h : rigidOf p c = 0) : c = 0 := by
  have hi1 : c.1 - c.2.2 * (p i).2 = 0 := by
    have := congrArg Prod.fst (congrFun h i); simpa [rigidOf] using this
  have hi2 : c.2.1 + c.2.2 * (p i).1 = 0 := by
    have := congrArg Prod.snd (congrFun h i); simpa [rigidOf] using this
  have hj1 : c.1 - c.2.2 * (p j).2 = 0 := by
    have := congrArg Prod.fst (congrFun h j); simpa [rigidOf] using this
  have hj2 : c.2.1 + c.2.2 * (p j).1 = 0 := by
    have := congrArg Prod.snd (congrFun h j); simpa [rigidOf] using this
  -- subtracting at the two vertices kills the translation, leaving ω·J(pᵢ−pⱼ)=0
  have hom : c.2.2 = 0 := by
    by_contra hne
    refine hij (Prod.ext ?_ ?_)
    · have hz : c.2.2 * ((p i).1 - (p j).1) = 0 := by linarith
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' hne
      · linarith
    · have hz : c.2.2 * ((p i).2 - (p j).2) = 0 := by linarith
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' hne
      · linarith
  have ha : c.1 = 0 := by rw [hom] at hi1; linarith
  have hb : c.2.1 = 0 := by rw [hom] at hi2; linarith
  exact Prod.ext ha (Prod.ext hb hom)

/-- The pairing of a rigid motion with itself, decomposed along the generators.
This is the identity that makes the Gram matrix nondegenerate. -/
lemma cip_rigidOf_self (p : Fin n → ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    cip (rigidOf p c) (rigidOf p c)
      = c.1 * cip (rigidOf p c) (T1 n) + c.2.1 * cip (rigidOf p c) (T2 n)
        + c.2.2 * cip (rigidOf p c) (T3 p) := by
  simp only [cip, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [rigidOf, T1, T2, T3, J, ip]
  ring

/-- **Step 2: the Gram matrix of `T₁, T₂, T₃` is nonsingular.** A rigid motion
pairing to zero against all three generators pairs to zero against itself,
hence vanishes, hence has zero coefficients.

This is exactly the nondegeneracy hypothesis the implicit function theorem
consumes in the paper's proof: the derivative of the slice equation with
respect to the motion parameters at the identity is this Gram matrix. -/
theorem gram_nondegenerate {p : Fin n → ℝ × ℝ} {i j : Fin n} (hij : p i ≠ p j)
    {c : ℝ × ℝ × ℝ}
    (h1 : cip (rigidOf p c) (T1 n) = 0)
    (h2 : cip (rigidOf p c) (T2 n) = 0)
    (h3 : cip (rigidOf p c) (T3 p) = 0) : c = 0 := by
  have hself : cip (rigidOf p c) (rigidOf p c) = 0 := by
    rw [cip_rigidOf_self, h1, h2, h3]; ring
  exact rigid_indep hij (eq_zero_of_cip_self hself)

/-- The slice condition is exactly orthogonality to every rigid motion, and
`gram_nondegenerate` says the only rigid motion orthogonal to all of them is
zero — so `R(p)` meets `R(p)^⊥` only in `0`, which is what makes the slice a
genuine transversal. -/
theorem rigid_inter_perp {p : Fin n → ℝ × ℝ} {i j : Fin n} (hij : p i ≠ p j)
    {c : ℝ × ℝ × ℝ} (h : ∀ d : ℝ × ℝ × ℝ, cip (rigidOf p c) (rigidOf p d) = 0) :
    c = 0 := by
  refine gram_nondegenerate hij ?_ ?_ ?_
  · have := h (1, 0, 0); simpa [rigidOf, T1, cip, ip] using this
  · have := h (0, 1, 0); simpa [rigidOf, T2, cip, ip] using this
  · have := h (0, 0, 1); simpa [rigidOf, T3, J, cip, ip] using this

end Chiquipoli.FirstOrder
