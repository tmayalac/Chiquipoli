/-
**Theorem 3.5, the blow-up half — step E of the formalisation.**

Steps A–D built the pieces the paper's proof uses:

  * `Feasible.lean`      the feasible set and its constraints (A)
  * `FeasibleOpen.lean`  openness of convexity and the inactive margin (B)
  * `FeasibleTangent.lean` the first-order limits (C)
  * `FeasibleRigid.lean` rigid invariance and the slice normalisation (D)

and `FirstOrder.no_admissible_direction` — proved before any of this — is the
algebraic core: it consumes exactly `(v,η) ∈ K_eq`, `η ≥ 0`, `v ⊥ R(p)` and
returns `v = 0 ∧ η = 0`.

This file assembles them. The paper's proof, line by line:

  set `t_k = ‖(q^k − p, ℓ_k − ℓ)‖ > 0` and `(v^k, η_k) = (q^k − p, ℓ_k − ℓ)/t_k`;
  since `‖(v^k,η_k)‖ = 1`, compactness gives a convergent subsequence;
  the side equalities and active diameter inequalities pass to the limit (C);
  `ℓ_k ≥ ℓ` gives `η ≥ 0`; the slice gives `v ⊥ R(p)` (D);
  `no_admissible_direction` gives `(v,η) = 0`, contradicting `‖(v,η)‖ = 1`.

Compactness of the unit sphere is available because the ambient space
`(ℝ²)ⁿ × ℝ` is finite dimensional, hence proper.
-/
import ChiquipoliLean.FeasibleRigid

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder Filter Topology

variable {n : ℕ} [NeZero n]

/-! ## `cip` is linear in its first argument, and continuous there -/

omit [NeZero n] in
lemma cip_smul_left (c : ℝ) (v w : Cfg n) : cip (c • v) w = c * cip v w := by
  simp only [cip, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by
    simp [Pi.smul_apply, ip_smul_left]

omit [NeZero n] in
lemma continuous_cip_left (w : Cfg n) : Continuous fun v : Cfg n => cip v w := by
  unfold cip ip
  fun_prop

/-! ## The blow-up

`hslice` below is what step D delivers for the *normalised* competitors: their
displacement from `p` is orthogonal to every infinitesimal rigid motion. -/

/-- **No blow-up sequence exists.**

Given hypotheses (i) and (ii) of Theorem 3.5 at `(p, ℓ)`, there is no sequence of
feasible competitors converging to `(p, ℓ)`, distinct from it, with side length
at least `ℓ`, and normalised into the slice. This is the contradiction the
paper's proof reaches, and every hypothesis here is one the proof states. -/
theorem no_blowup_sequence_gen
    {iota : Type*} [Fintype iota] {p : Cfg n} {l : ℝ} (hl : 0 < l)
    {D : Data n iota} {a b : iota → Fin n}
    {sc : ℝ} (hsc : 0 < sc)
    (hbridge : ∀ (v : Cfg n) (eta : ℝ),
      (∀ i, eD p l v eta i = 0) → (∀ e, dD p v (a e) (b e) ≤ 0) → D.Keq v (sc * eta))
    {kap : ℝ} (hkap : 0 < kap)
    {al : Fin n → ℝ} {lam : iota → ℝ}
    (hm : D.MultiplierIdentity kap al lam) (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Cfg n, D.Ieq w 0 → D.R w)
    (hpeq : ∀ i : Fin n, eC i (p, l) = 0)
    (hpact : ∀ e : iota, dC (a e) (b e) p = 0)
    {x : ℕ → Amb n}
    (hfeas : ∀ k, IsFeasible (x k))
    (hne : ∀ k, x k ≠ (p, l))
    (hconv : Tendsto x atTop (𝓝 (p, l)))
    (hge : ∀ k, l ≤ (x k).2)
    (hslice : ∀ k, ∀ r : Cfg n, D.R r → cip ((x k).1 - p) r = 0) :
    False := by
  classical
  -- Displacements, scales, and normalised directions.
  set u : ℕ → Amb n := fun k => x k - (p, l) with hu
  set t : ℕ → ℝ := fun k => ‖u k‖ with ht
  have htpos : ∀ k, 0 < t k := fun k => by
    simp only [ht, hu, norm_pos_iff, sub_ne_zero]
    exact hne k
  have htne : ∀ k, t k ≠ 0 := fun k => (htpos k).ne'
  set z : ℕ → Amb n := fun k => (t k)⁻¹ • u k with hzdef
  have hznorm : ∀ k, ‖z k‖ = 1 := by
    intro k
    have hexp : ‖z k‖ = (t k)⁻¹ * ‖u k‖ := by
      simp [hzdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (htpos k)]
    have hnu : ‖u k‖ = t k := rfl
    rw [hexp, hnu, inv_mul_cancel₀ (htne k)]
  -- The scales tend to zero.
  have htz : Tendsto t atTop (𝓝 0) := by
    have h1 : Tendsto u atTop (𝓝 0) := by
      simpa [hu] using hconv.sub (tendsto_const_nhds (x := ((p, l) : Amb n)))
    simpa [ht] using h1.norm
  -- Compactness of the unit sphere gives a convergent subsequence.
  obtain ⟨v, hvmem, phi, hphi, hlim⟩ :=
    (isCompact_sphere (0 : Amb n) 1).tendsto_subseq (x := z)
      (fun k => by simpa [Metric.mem_sphere] using hznorm k)
  have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere] using hvmem
  -- Set up the subsequence in the form step C consumes.
  set u' : ℕ → Amb n := fun k => u (phi k) with hu'
  set t' : ℕ → ℝ := fun k => t (phi k) with ht'
  have ht'pos : ∀ k, 0 < t' k := fun k => htpos (phi k)
  have ht'ne : ∀ k, t' k ≠ 0 := fun k => htne (phi k)
  have ht'z : Tendsto t' atTop (𝓝 0) := htz.comp hphi.tendsto_atTop
  have hz' : Tendsto (fun k => (t' k)⁻¹ • u' k) atTop (𝓝 v) := hlim
  -- Step C, sides: every side equality passes to the limit as an equality.
  have hside : ∀ i : Fin n, eD p l v.1 v.2 i = 0 := by
    intro i
    refine eD_eq_zero_of_blowup (x := ((p, l) : Amb n)) ht'ne ht'z hz' i fun k => ?_
    have hx : ((p, l) : Amb n) + u' k = x (phi k) := by simp [hu', hu]
    rw [hx, hpeq i]
    exact ((hfeas (phi k)).2.1 i)
  -- Step C, active diameters: each passes to the limit as an inequality.
  have hdiam : ∀ e : iota, dD p v.1 (a e) (b e) ≤ 0 := by
    intro e
    refine dD_nonpos_of_blowup ht'pos ht'z hz' (a e) (b e) (hpact e) fun k => ?_
    have hx : p + (u' k).1 = (x (phi k)).1 := by
      simp [hu', hu, Prod.fst_sub]
    rw [hx]
    exact (hfeas (phi k)).1 (a e) (b e)
  -- `η ≥ 0`, from `ℓ_k ≥ ℓ`.
  have heta : 0 ≤ v.2 := by
    have hnn : ∀ k, 0 ≤ ((t' k)⁻¹ • u' k).2 := by
      intro k
      have h1 : (0 : ℝ) ≤ (t' k)⁻¹ := (inv_pos.mpr (ht'pos k)).le
      have h2 : 0 ≤ (u' k).2 := by
        simp only [hu', hu, Prod.snd_sub, sub_nonneg]
        exact hge (phi k)
      exact mul_nonneg h1 h2
    have hsnd : Tendsto (fun k => ((t' k)⁻¹ • u' k).2) atTop (𝓝 v.2) :=
      (continuous_snd.tendsto v).comp hz'
    exact ge_of_tendsto hsnd (Eventually.of_forall hnn)
  -- The slice condition passes to the limit.
  have hsl : ∀ r : Cfg n, D.R r → cip v.1 r = 0 := by
    intro r hr
    have hk : ∀ k, cip ((t' k)⁻¹ • u' k).1 r = 0 := by
      intro k
      have h1 : ((t' k)⁻¹ • u' k).1 = (t' k)⁻¹ • (u' k).1 := rfl
      rw [h1, cip_smul_left]
      have := hslice (phi k) r hr
      simp only [hu', hu, Prod.fst_sub] at this ⊢
      rw [this, mul_zero]
    have hfst : Tendsto (fun k => ((t' k)⁻¹ • u' k).1) atTop (𝓝 v.1) :=
      (continuous_fst.tendsto v).comp hz'
    have hcont : Tendsto (fun k => cip ((t' k)⁻¹ • u' k).1 r) atTop (𝓝 (cip v.1 r)) :=
      ((continuous_cip_left r).tendsto v.1).comp hfst
    have : Tendsto (fun k => cip ((t' k)⁻¹ • u' k).1 r) atTop (𝓝 0) := by
      simp only [hk]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hcont this
  -- The limit direction lies in the linearised cone, in `D`'s normalisation.
  have hK : D.Keq v.1 (sc * v.2) := hbridge v.1 v.2 hside hdiam
  have heta' : 0 ≤ sc * v.2 := mul_nonneg hsc.le heta
  -- The algebraic core closes the argument.
  obtain ⟨hv1, hv2⟩ := no_admissible_direction hkap hm hlam hIR hK heta' hsl
  have hv2' : v.2 = 0 := by
    rcases mul_eq_zero.mp hv2 with h | h
    · exact absurd h hsc.ne'
    · exact h
  have : v = 0 := Prod.ext hv1 hv2'
  rw [this] at hvnorm
  simp at hvnorm

/-- The special case in which the data is read straight off `p` and `ℓ`
(`dataOf`), where the rescaling is trivial. -/
theorem no_blowup_sequence
    {iota : Type*} [Fintype iota] {p : Cfg n} {l : ℝ} (hl : 0 < l)
    {a b : iota → Fin n} {kap : ℝ} (hkap : 0 < kap)
    {al : Fin n → ℝ} {lam : iota → ℝ}
    (hm : (dataOf p l a b).MultiplierIdentity kap al lam) (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Cfg n, (dataOf p l a b).Ieq w 0 → (dataOf p l a b).R w)
    (hpeq : ∀ i : Fin n, eC i (p, l) = 0)
    (hpact : ∀ e : iota, dC (a e) (b e) p = 0)
    {x : ℕ → Amb n}
    (hfeas : ∀ k, IsFeasible (x k))
    (hne : ∀ k, x k ≠ (p, l))
    (hconv : Tendsto x atTop (𝓝 (p, l)))
    (hge : ∀ k, l ≤ (x k).2)
    (hslice : ∀ k, ∀ r : Cfg n, (dataOf p l a b).R r → cip ((x k).1 - p) r = 0) :
    False :=
  no_blowup_sequence_gen hl one_pos
    (fun v eta hs hd => by
      rw [one_mul]; exact (Keq_iff hl a b v eta).mp ⟨hs, hd⟩)
    hkap hm hlam hIR hpeq hpact hfeas hne hconv hge hslice

/-! ## The neighbourhood form

`no_blowup_sequence` is the paper's proof. Its contrapositive is the theorem's
statement: a neighbourhood `W` of `(p,ℓ)` on which no competitor beats `ℓ`. The
translation is the standard one for a first-countable space — `𝓝 (p,ℓ)` is
countably generated, so failing to hold eventually means failing along a
sequence (`Filter.exists_seq_forall_of_frequently`), and that sequence is
exactly the one `no_blowup_sequence` refutes.

The competitors here are the *normalised* ones: `hslice` is what step D supplies
for `g(q)·q`, and `isFeasible_move` says normalising costs no feasibility. -/

/-- **Theorem 3.5, blow-up half, in neighbourhood form.**

Under hypotheses (i) and (ii) at `(p, ℓ)`, there is a neighbourhood of `(p, ℓ)`
in which every feasible competitor that is normalised into the slice and has
side length at least `ℓ` *is* `(p, ℓ)`.

Since a competitor with side length `> ℓ` cannot equal `(p, ℓ)`, this says in
particular that no nearby normalised competitor has larger side length, hence
none has larger perimeter `nℓ`. Combined with `isFeasible_move` and
`eventually_phiGeom_zero` of step D — normalisation preserves feasibility and
supplies the slice condition — this is the paper's "`m ≤ ℓ`, with equality only
when `q` is congruent to `p`". -/
theorem eventually_no_better
    {iota : Type*} [Fintype iota] {p : Cfg n} {l : ℝ} (hl : 0 < l)
    {D : Data n iota} {a b : iota → Fin n}
    {sc : ℝ} (hsc : 0 < sc)
    (hbridge : ∀ (v : Cfg n) (eta : ℝ),
      (∀ i, eD p l v eta i = 0) → (∀ e, dD p v (a e) (b e) ≤ 0) → D.Keq v (sc * eta))
    {kap : ℝ} (hkap : 0 < kap)
    {al : Fin n → ℝ} {lam : iota → ℝ}
    (hm : D.MultiplierIdentity kap al lam) (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Cfg n, D.Ieq w 0 → D.R w)
    (hpeq : ∀ i : Fin n, eC i (p, l) = 0)
    (hpact : ∀ e : iota, dC (a e) (b e) p = 0) :
    ∀ᶠ y in 𝓝 ((p, l) : Amb n),
      IsFeasible y → l ≤ y.2 →
        (∀ r : Cfg n, D.R r → cip (y.1 - p) r = 0) →
        y = (p, l) := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨x, hxt, hxp⟩ := Filter.exists_seq_forall_of_frequently hcon
  refine no_blowup_sequence_gen hl hsc hbridge hkap hm hlam hIR hpeq hpact
    (x := x) (fun k => ?_) (fun k => ?_) hxt (fun k => ?_) (fun k => ?_)
  · exact (by
      by_contra hf
      exact (hxp k) fun hfe => absurd hfe hf)
  · exact fun he => (hxp k) (fun _ hge hsl => he)
  · exact (by
      by_contra hf
      exact (hxp k) fun _ hge => absurd hge hf)
  · exact (by
      by_contra hf
      push Not at hf
      obtain ⟨r, hr, hne⟩ := hf
      exact (hxp k) fun _ _ hsl => absurd (hsl r hr) hne)

/-! ## Congruence: discharging the slice hypothesis

`eventually_no_better` carries the slice condition as a hypothesis on the
competitor. The paper does not: it *normalises* the competitor first, and
concludes "`m ≤ ℓ`, with equality only when `q` is congruent to `p`". Step D
supplies both halves of that move — `isFeasible_move` says normalising costs no
feasibility, and `eventually_phiGeom_zero` says the normalised competitor
satisfies the slice equation — so the hypothesis can be discharged.

Two configurations are congruent when an orientation-preserving Euclidean motion
carries one to the other. That is exactly the relation `normCfg` realises. -/

/-- `q` is congruent to `p`: some orientation-preserving Euclidean motion carries
`q` onto `p`. -/
def Congruent (q p : Cfg n) : Prop := ∃ c : ℝ × ℝ × ℝ, moveCfg c q = p

/-- **Theorem 3.5 for the blow-up half, in the paper's form.**

Under hypotheses (i) and (ii) at `(p, ℓ)`, every feasible competitor in some
neighbourhood of `(p, ℓ)` whose side length is at least `ℓ` has side length
*exactly* `ℓ` and is congruent to `p`. Equivalently: `m ≤ ℓ`, with equality only
up to an orientation-preserving Euclidean motion.

No slice hypothesis appears. It is discharged by normalising the competitor, and
the conclusion is stated about the competitor itself. -/
theorem eventually_congruent_of_no_worse
    {iota : Type*} [Fintype iota] {p : Cfg n} {l : ℝ} (hl : 0 < l)
    {ii jj : Fin n} (hij : p ii ≠ p jj)
    {D : Data n iota} (hDp : D.p = p) {a b : iota → Fin n}
    {sc : ℝ} (hsc : 0 < sc)
    (hbridge : ∀ (v : Cfg n) (eta : ℝ),
      (∀ i, eD p l v eta i = 0) → (∀ e, dD p v (a e) (b e) ≤ 0) → D.Keq v (sc * eta))
    {kap : ℝ} (hkap : 0 < kap)
    {al : Fin n → ℝ} {lam : iota → ℝ}
    (hm : D.MultiplierIdentity kap al lam) (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Cfg n, D.Ieq w 0 → D.R w)
    (hpeq : ∀ i : Fin n, eC i (p, l) = 0)
    (hpact : ∀ e : iota, dC (a e) (b e) p = 0) :
    ∀ᶠ y in 𝓝 ((p, l) : Amb n),
      IsFeasible y → l ≤ y.2 → Congruent y.1 p ∧ y.2 = l := by
  classical
  -- The normalisation, as a map of the ambient space, fixing `(p, ℓ)`.
  set Psi : Amb n → Amb n := fun y => (normCfg hij y.1, y.2) with hPsi
  have hf1 : Tendsto (fun y : Amb n => normCfg hij y.1) (𝓝 ((p, l) : Amb n)) (𝓝 p) :=
    (tendsto_normCfg hij).comp (continuous_fst.tendsto ((p, l) : Amb n))
  have hf2 : Tendsto (fun y : Amb n => y.2) (𝓝 ((p, l) : Amb n)) (𝓝 l) :=
    continuous_snd.tendsto ((p, l) : Amb n)
  have hPsiT : Tendsto Psi (𝓝 ((p, l) : Amb n)) (𝓝 ((p, l) : Amb n)) :=
    hf1.prodMk_nhds hf2
  -- The normalised competitor is not beaten (previous theorem, pulled back).
  have hA := hPsiT.eventually
    (eventually_no_better hl hsc hbridge hkap hm hlam hIR hpeq hpact)
  -- The normalised competitor satisfies the slice equation (step D).
  have hB : ∀ᶠ y in 𝓝 ((p, l) : Amb n), PhiGeom p y.1 (g hij y.1) = 0 :=
    (continuous_fst.tendsto ((p, l) : Amb n)).eventually (eventually_phiGeom_zero hij)
  filter_upwards [hA, hB] with y hy hphi hfeas hge
  -- Unpack the slice equation into its three components.
  have hdisp : (fun k => gmove (g hij y.1) (y.1 k) - p k) = normCfg hij y.1 - p := by
    funext k; simp [normCfg, moveCfg, Pi.sub_apply]
  have h1 : cip (normCfg hij y.1 - p) (T1 n) = 0 := by
    have := congrArg (fun w : ℝ × ℝ × ℝ => w.1) hphi
    simpa [PhiGeom, hdisp] using this
  have h2 : cip (normCfg hij y.1 - p) (T2 n) = 0 := by
    have := congrArg (fun w : ℝ × ℝ × ℝ => w.2.1) hphi
    simpa [PhiGeom, hdisp] using this
  have h3 : cip (normCfg hij y.1 - p) (T3 p) = 0 := by
    have := congrArg (fun w : ℝ × ℝ × ℝ => w.2.2) hphi
    simpa [PhiGeom, hdisp] using this
  -- Feed the normalised competitor to `eventually_no_better`.
  have hfeas' : IsFeasible (Psi y) := by
    rw [hPsi]
    exact (isFeasible_move (g hij y.1) y).mpr hfeas
  have hslice' : ∀ r : Cfg n, D.R r → cip ((Psi y).1 - p) r = 0 :=
    slice_of_generators hDp h1 h2 h3
  have heq : Psi y = (p, l) := hy hfeas' hge hslice'
  -- Read the two conclusions off `Psi y = (p, ℓ)`.
  refine ⟨⟨g hij y.1, ?_⟩, ?_⟩
  · have := congrArg Prod.fst heq
    simpa [hPsi, normCfg] using this
  · have := congrArg Prod.snd heq
    simpa [hPsi] using this

/-- **Theorem 3.5 of the paper**, in the paper's own normalisation (`dataOf`,
where the scalar variable is `ℓ` itself and the rescaling is trivial).

Hypotheses (i) and (ii) are `hm`/`hlam` and `hIR`; `hpeq` and `hpact` say that
`(p, ℓ)` is equilateral with the declared diameters active, which the paper
folds into the phrase "equilateral small `n`-gon" and the definition of
`E_D(p)`; `hij` is the two distinct vertices the local Euclidean slice needs,
which the paper gets from strict convexity.

The statement is slightly stronger than the printed one in three respects, each
because the proof does not use the extra strength: only `I_eq ⊆ R_eq` is
assumed, not equality (the reverse inclusion is free and carries no
information); strict convexity of `p` is replaced by two distinct vertices; and
the competitors are not required to be convex. -/
theorem thm_3_5
    {iota : Type*} [Fintype iota] {p : Cfg n} {l : ℝ} (hl : 0 < l)
    {ii jj : Fin n} (hij : p ii ≠ p jj)
    {a b : iota → Fin n} {kap : ℝ} (hkap : 0 < kap)
    {al : Fin n → ℝ} {lam : iota → ℝ}
    (hm : (dataOf p l a b).MultiplierIdentity kap al lam) (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Cfg n, (dataOf p l a b).Ieq w 0 → (dataOf p l a b).R w)
    (hpeq : ∀ i : Fin n, eC i (p, l) = 0)
    (hpact : ∀ e : iota, dC (a e) (b e) p = 0) :
    ∀ᶠ y in 𝓝 ((p, l) : Amb n),
      IsFeasible y → l ≤ y.2 → Congruent y.1 p ∧ y.2 = l :=
  eventually_congruent_of_no_worse hl hij rfl one_pos
    (fun v eta hs hd => by rw [one_mul]; exact (Keq_iff hl a b v eta).mp ⟨hs, hd⟩)
    hkap hm hlam hIR hpeq hpact

/-- The conclusion in the printed form: **no nearby feasible competitor has a
larger side length**, hence none has larger perimeter `n·m`. -/
theorem thm_3_5_le
    {iota : Type*} [Fintype iota] {p : Cfg n} {l : ℝ} (hl : 0 < l)
    {ii jj : Fin n} (hij : p ii ≠ p jj)
    {a b : iota → Fin n} {kap : ℝ} (hkap : 0 < kap)
    {al : Fin n → ℝ} {lam : iota → ℝ}
    (hm : (dataOf p l a b).MultiplierIdentity kap al lam) (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Cfg n, (dataOf p l a b).Ieq w 0 → (dataOf p l a b).R w)
    (hpeq : ∀ i : Fin n, eC i (p, l) = 0)
    (hpact : ∀ e : iota, dC (a e) (b e) p = 0) :
    ∀ᶠ y in 𝓝 ((p, l) : Amb n), IsFeasible y → y.2 ≤ l := by
  filter_upwards [thm_3_5 hl hij hkap hm hlam hIR hpeq hpact] with y hy hf
  by_contra hlt
  push Not at hlt
  exact absurd (hy hf hlt.le).2 (ne_of_gt hlt)

end Chiquipoli.Feasible
