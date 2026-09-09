/-
**Proposition 6.2(6): `rank D(e,d) = 30`, kernel-checked.**

The development already proves the statement Proposition 6.2(6) is *used* for —
`I_eq = R_eq`, as `kernel_is_rigid` — and deliberately avoids `Matrix.det` and
the rank API to do it. That leaves the paper's headline number, `rank = 30`,
without a Lean counterpart.

It is recovered here for free, by rank–nullity rather than by any new
computation. The active equality Jacobian is a linear map

    D : (ℝ²)¹⁶ × ℝ  →  ℝ¹⁶ × ℝ¹⁵ ,        dim domain = 33,

`kernel_is_rigid` together with `dsq_rigid` identifies its kernel exactly with
the infinitesimal rigid motions, and those form a 3-dimensional space because
the map `(a,b,e) ↦ (a − e·y_i, b + e·x_i)ᵢ` is injective — which needs only that
some vertex has nonzero first coordinate, supplied by `p1_fst_ne`. Hence

    rank D = 33 − 3 = 30.

Note what this does **not** re-do: the paper certifies `rank ≥ 30` by exhibiting
a preconditioner with `‖Id − CM‖∞ ≤ 1.42·10⁻²⁵` for a selected 30×30 minor, and
`rank ≤ 30` by the rigid kernel. That interval computation is not repeated in
Lean; the lower bound is obtained instead from the exact kernel characterisation,
which is a different and stronger route — it needs no minor selection and no
preconditioner.
-/
import ChiquipoliLean.FirstOrderA16
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Chiquipoli.FirstOrder

open Module

/-- `A16s` is the doubled edge vector, at every index. -/
lemma A16s_eq (z : ℝ) (i : Fin 16) : A16s z i = twice (A16p z i) (A16p z (i + 1)) := by
  fin_cases i <;> rfl

/-- `A16u` is the doubled diameter vector, at every index. -/
lemma A16u_eq (z : ℝ) (e : Fin 15) :
    A16u z e = twice (A16p z (A16a e)) (A16p z (A16b e)) := by
  fin_cases e <;> rfl

/-- The infinitesimal rigid motions of the `A16` configuration, as a linear map
out of the 3-dimensional parameter space `(a, b, e)`. -/
noncomputable def rigidMap (z : ℝ) : (ℝ × ℝ × ℝ) →ₗ[ℝ] ((Fin 16 → ℝ × ℝ) × ℝ) where
  toFun c := (fun i => rigid c.1 c.2.1 c.2.2 (A16p z i), 0)
  map_add' := by
    intro x y
    refine Prod.ext (funext fun i => ?_) (by simp)
    simp only [rigid, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.ext_iff]
    constructor <;> simp <;> ring
  map_smul' := by
    intro r x
    refine Prod.ext (funext fun i => ?_) (by simp)
    simp only [rigid, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk,
      RingHom.id_apply, Prod.ext_iff]
    constructor <;> simp <;> ring

/-- The active equality Jacobian `D(e,d)`, as a linear map. The first block is
the sixteen side differentials, the second the fifteen active-diameter ones. -/
noncomputable def jacA16 (z : ℝ) :
    ((Fin 16 → ℝ × ℝ) × ℝ) →ₗ[ℝ] ((Fin 16 → ℝ) × (Fin 15 → ℝ)) where
  toFun w := (fun i => (A16Data z).sideD w.1 w.2 i,
              fun e => (A16Data z).diamD w.1 e)
  map_add' := by
    intro x y
    refine Prod.ext (funext fun i => ?_) (funext fun e => ?_) <;>
      simp only [Data.sideD, Data.diamD, ip, Prod.fst_add, Prod.snd_add,
        Pi.add_apply, Prod.fst_sub, Prod.snd_sub, Prod.mk_add_mk] <;> ring
  map_smul' := by
    intro r x
    refine Prod.ext (funext fun i => ?_) (funext fun e => ?_) <;>
      simp only [Data.sideD, Data.diamD, ip, Prod.smul_fst, Prod.smul_snd,
        Pi.smul_apply, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
        RingHom.id_apply, Prod.smul_mk] <;> ring

/-- The domain has dimension `33 = 2·16 + 1`. -/
lemma finrank_domain : finrank ℝ ((Fin 16 → ℝ × ℝ) × ℝ) = 33 := by
  simp [Module.finrank_pi_fintype]

/-- **The rigid motions are 3-dimensional.** Injectivity needs only that some
vertex has nonzero first coordinate: `p₀ = (0,0)` forces the translation part to
vanish, and then `(p₁)¹ ≠ 0` forces the rotation rate to vanish. -/
theorem rigidMap_injective (z : ℝ) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) : Function.Injective (rigidMap z) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun c hc => ?_
  rw [LinearMap.mem_ker] at hc
  have hfun := congrArg Prod.fst hc
  have h0 : rigid c.1 c.2.1 c.2.2 (A16p z 0) = 0 := by
    have := congrFun hfun 0; simpa [rigidMap] using this
  have h1 : rigid c.1 c.2.1 c.2.2 (A16p z 1) = 0 := by
    have := congrFun hfun 1; simpa [rigidMap] using this
  have hp0 : A16p z 0 = (0, 0) := by show p0 z = (0, 0); rw [p0]
  have ha : c.1 = 0 := by
    have := congrArg Prod.fst h0; rw [hp0] at this; simpa [rigid] using this
  have hb : c.2.1 = 0 := by
    have := congrArg Prod.snd h0; rw [hp0] at this; simpa [rigid] using this
  have hp1 : (p1 z).1 ≠ 0 := p1_fst_ne z hsz hcb
  have he : c.2.2 = 0 := by
    have h := congrArg Prod.snd h1
    have hA : A16p z 1 = p1 z := rfl
    rw [hA] at h
    simp only [rigid, Prod.snd_zero] at h
    rcases mul_eq_zero.mp (by linarith : c.2.2 * (p1 z).1 = 0) with h' | h'
    · exact h'
    · exact absurd h' hp1
  exact Prod.ext ha (Prod.ext hb he)

/-- **The kernel of the Jacobian is exactly the rigid motions.** `⊇` is
`dsq_rigid`, an unconditional ring identity; `⊆` is `A16_kernel`, the certified
rank gate. -/
theorem ker_jacA16 (z : ℝ) (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) :
    LinearMap.ker (jacA16 z) = LinearMap.range (rigidMap z) := by
  apply le_antisymm
  · rintro ⟨w, dt⟩ hw
    rw [LinearMap.mem_ker] at hw
    have hs : ∀ i, (A16Data z).sideD w dt i = 0 :=
      fun i => congrFun (congrArg Prod.fst hw) i
    have hd : ∀ e, (A16Data z).diamD w e = 0 :=
      fun e => congrFun (congrArg Prod.snd hw) e
    obtain ⟨hdt, t, om, hr⟩ := A16_kernel z hF hsz hcb w dt hs hd
    refine ⟨(t.1, t.2, om), Prod.ext (funext fun i => ?_) hdt.symm⟩
    show rigid t.1 t.2 om (A16p z i) = w i
    rw [hr i]
    simp only [rigid, J, Prod.smul_mk, smul_eq_mul, Prod.ext_iff]
    constructor <;> simp [A16Data] <;> ring
  · rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    refine Prod.ext (funext fun i => ?_) (funext fun e => ?_)
    · show (A16Data z).sideD (fun i => rigid c.1 c.2.1 c.2.2 (A16p z i)) 0 i = 0
      simp only [Data.sideD, A16Data, A16s_eq z i, ip_twice, dsq_rigid, sub_zero]
    · show (A16Data z).diamD (fun i => rigid c.1 c.2.1 c.2.2 (A16p z i)) e = 0
      simp only [Data.diamD, A16Data, A16u_eq z e, ip_twice, dsq_rigid]

/-- **Proposition 6.2(6): `rank D(e,d) = 30`.** Rank–nullity applied to the two
theorems above: the domain is 33-dimensional and the kernel is exactly the
3-dimensional space of infinitesimal rigid motions. -/
theorem rank_eq_thirty (z : ℝ) (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) :
    finrank ℝ (LinearMap.range (jacA16 z)) = 30 := by
  have hker : finrank ℝ (LinearMap.ker (jacA16 z)) = 3 := by
    rw [ker_jacA16 z hF hsz hcb,
        LinearMap.finrank_range_of_inj (rigidMap_injective z hsz hcb)]
    simp
  have h := LinearMap.finrank_range_add_finrank_ker (jacA16 z)
  rw [hker, finrank_domain] at h
  omega

end Chiquipoli.FirstOrder
