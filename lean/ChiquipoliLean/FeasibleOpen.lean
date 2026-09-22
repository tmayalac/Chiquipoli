/-
**Openness of strict convexity and the labelled cyclic order — step B of
Theorem 3.5.**

The paper's proof opens with

  "Strict convexity and labelled cyclic order are open conditions. After
   discarding finitely many terms, every `q^k` therefore has the same labelled
   cyclic order as `p`."

and the same openness holds for the strict inactive diameter margin
(Definition 2.4 of the article), which the article uses implicitly when it
builds `K_eq` from the active edges alone: an inactive pair imposes no
first-order condition. This file proves both.

Each is a finite conjunction of strict inequalities in continuous functions of
the configuration, so each cuts out a finite intersection of preimages of
`(0, ∞)`. That is the whole argument; it is short because the squared,
label-indexed formulation of `Feasible.lean` made it short.

The sequential corollaries (`Filter.Tendsto.eventually_*`) are the form the
blow-up actually consumes: a sequence of competitors converging to `p` is
eventually convex with `p`'s labelling, and eventually keeps every diameter that
is slack at `p` slack.
-/
import ChiquipoliLean.Feasible

namespace Chiquipoli.Feasible

open Chiquipoli.FirstOrder Filter Topology

variable {n : ℕ} [NeZero n]

/-! ## Strict convexity and the labelled cyclic order -/

/-- The convex-ordered configurations form an open set: a finite intersection of
preimages of `(0, ∞)` under the continuous maps `q ↦ cross (q i) (q (i+1)) (q j)`. -/
theorem isOpen_convexOrdered : IsOpen {q : Cfg n | ConvexOrdered q} := by
  have hEq : {q : Cfg n | ConvexOrdered q}
      = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ _ : j ≠ i, ⋂ _ : j ≠ i + 1,
          (fun q : Cfg n => cross (q i) (q (i + 1)) (q j)) ⁻¹' Set.Ioi 0 := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi,
      ConvexOrdered]
  rw [hEq]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  refine isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ => ?_
  exact (continuous_cross i j).isOpen_preimage _ isOpen_Ioi

/-- A configuration near a convex-ordered one is convex-ordered. This is the
paper's "after discarding finitely many terms". -/
theorem eventually_convexOrdered {p : Cfg n} (hp : ConvexOrdered p) :
    ∀ᶠ q in 𝓝 p, ConvexOrdered q :=
  isOpen_convexOrdered.mem_nhds hp

/-- Sequential form: a sequence converging to a convex-ordered configuration is
eventually convex-ordered, with the same labelled cyclic order. -/
theorem eventually_convexOrdered_of_tendsto {p : Cfg n} (hp : ConvexOrdered p)
    {q : ℕ → Cfg n} (hq : Tendsto q atTop (𝓝 p)) :
    ∀ᶠ k in atTop, ConvexOrdered (q k) :=
  hq.eventually (eventually_convexOrdered hp)

/-! ## The strict inactive diameter margin

The article's Definition 2.4 (the inactive diameter margin), used implicitly in
the proof of Theorem 3.5: a diameter that is strictly slack at `p` stays
strictly slack nearby, so it imposes no first-order condition on the blow-up
limit. This is
what lets `K_eq` be built from the active edges alone. -/

omit [NeZero n] in
/-- One slack diameter stays slack. -/
theorem eventually_dC_neg {p : Cfg n} {i j : Fin n} (h : dC i j p < 0) :
    ∀ᶠ q in 𝓝 p, dC i j q < 0 :=
  (continuous_dC i j).continuousAt.eventually_lt_const h

omit [NeZero n] in
/-- Every diameter slack at `p` — over any finite index set of pairs — stays
slack on a single neighbourhood. -/
theorem eventually_dC_neg_finset {p : Cfg n} (S : Finset (Fin n × Fin n))
    (h : ∀ e ∈ S, dC e.1 e.2 p < 0) :
    ∀ᶠ q in 𝓝 p, ∀ e ∈ S, dC e.1 e.2 q < 0 :=
  (eventually_all_finset S).2 fun e he => eventually_dC_neg (h e he)

omit [NeZero n] in
/-- Sequential form of the previous statement. -/
theorem eventually_dC_neg_of_tendsto {p : Cfg n} (S : Finset (Fin n × Fin n))
    (h : ∀ e ∈ S, dC e.1 e.2 p < 0) {q : ℕ → Cfg n} (hq : Tendsto q atTop (𝓝 p)) :
    ∀ᶠ k in atTop, ∀ e ∈ S, dC e.1 e.2 (q k) < 0 :=
  hq.eventually (eventually_dC_neg_finset S h)

/-! ## What step B delivers to the blow-up

Combined: a sequence of feasible competitors converging to `p` is eventually
feasible *in the paper's convex sense*, with `p`'s labelling and with every
diameter slack at `p` still slack. Nothing after this point needs to revisit
convexity. -/

theorem eventually_feasibleConvex_of_tendsto {p : Cfg n} {l : ℝ}
    (hp : ConvexOrdered p) {x : ℕ → Amb n} (hfeas : ∀ k, IsFeasible (x k))
    (hx : Tendsto x atTop (𝓝 (p, l))) :
    ∀ᶠ k in atTop, IsFeasibleConvex (x k) := by
  have h1 : Tendsto (fun k => (x k).1) atTop (𝓝 p) :=
    (continuous_fst.tendsto _).comp hx
  exact (eventually_convexOrdered_of_tendsto hp h1).mono fun k hk => ⟨hk, hfeas k⟩

end Chiquipoli.Feasible
