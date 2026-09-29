/-
# The multipliers as a self-stress, constructed and verified once for every `n`

A stress `σ` assigns a number to every bar (sides first, then active diameters).
Its force at a vertex `k` is `bal σ k = Σ_b σ_b · (p_{other end} − p_k)`. If every
vertex balances, `Σ_b σ_b ⟪p_{b₂} − p_{b₁}, v_{b₂} − v_{b₁}⟫ = 0` for every `v`
(`stationary_of_bal`), which is the stationarity `mult_of_stationary'` turns
into the multiplier identity of Theorem 3.5.

The stress is built by the reverse Henneberg recursion (`stressR`): two bars
carry given rational values; in reverse order each vertex `k` fixes its two
Henneberg bars by Cramer's rule so that it balances (`cramer_bal`); the bar
`0 → 1` is fixed last (`pin_bal`); vertices `0`, `1` balance by the global force
and moment identities. `bal_zero` proves every vertex balances, under
combinatorial conditions on the data (`stressDataOK`) that the kernel checks.
-/
import ChiquipoliFamily.Trig.Henneberg

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real FI Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family

variable {n nb : ℕ}

/-! ## Forces -/

/-- The force a unit stress on the bar `{a, b}` exerts at `k`. -/
def contrib (p : Cfg n) (bar : Fin n × Fin n) (k : Fin n) : ℝ × ℝ :=
  if bar.1 = k then p bar.2 - p k else if bar.2 = k then p bar.1 - p k else 0

/-- The net force at `k`. -/
noncomputable def bal (p : Cfg n) (bar : Fin nb → Fin n × Fin n) (σ : Fin nb → ℝ) (k : Fin n) : ℝ × ℝ :=
  ∑ b, σ b • contrib p (bar b) k

/-- The force of a bar splits into its two endpoint contributions. -/
lemma contrib_split (p : Cfg n) (a b k : Fin n) :
    contrib p (a, b) k = (if a = k then p b - p a else 0) + (if b = k then p a - p b else 0) := by
  unfold contrib
  by_cases h1 : a = k
  · subst h1
    by_cases h2 : b = a
    · subst h2; simp
    · simp [h2]
  · by_cases h2 : b = k
    · subst h2; simp [h1]
    · simp [h1, h2]

lemma contrib_sum_ip (p v : Cfg n) (a b : Fin n) (hab : a ≠ b) :
    ∑ k, ip (contrib p (a, b) k) (v k) = -ip (p b - p a) (v b - v a) := by
  have h : ∀ k, ip (contrib p (a, b) k) (v k)
      = (if a = k then ip (p b - p a) (v k) else 0) + (if b = k then ip (p a - p b) (v k) else 0) := by
    intro k
    rw [contrib_split]
    by_cases h1 : a = k <;> by_cases h2 : b = k <;> simp [h1, h2, ip] <;> ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [ip, Prod.fst_sub, Prod.snd_sub]; ring

lemma ip_smul_left' (c : ℝ) (x y : ℝ × ℝ) : ip (c • x) y = c * ip x y := by
  simp [ip, Prod.smul_fst, Prod.smul_snd]; ring

lemma ip_sum_left {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ) (y : ℝ × ℝ) :
    ip (∑ i ∈ s, f i) y = ∑ i ∈ s, ip (f i) y := by
  unfold ip
  simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

/-- **Stationarity from balance.** -/
theorem stationary_of_bal (p : Cfg n) (bar : Fin nb → Fin n × Fin n) (hbar : ∀ b, (bar b).1 ≠ (bar b).2)
    (σ : Fin nb → ℝ) (hbal : ∀ k, bal p bar σ k = 0) (v : Cfg n) :
    ∑ b, σ b * ip (p (bar b).2 - p (bar b).1) (v (bar b).2 - v (bar b).1) = 0 := by
  have key : ∑ k, ip (bal p bar σ k) (v k)
      = -∑ b, σ b * ip (p (bar b).2 - p (bar b).1) (v (bar b).2 - v (bar b).1) := by
    unfold bal
    simp only [ip_sum_left, ip_smul_left']
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have := contrib_sum_ip p v (bar b).1 (bar b).2 (hbar b)
    rw [show ((bar b).1, (bar b).2) = bar b from rfl] at this
    rw [this]; ring
  have : ∑ k, ip (bal p bar σ k) (v k) = 0 := by simp [hbal, ip]
  linarith

/-- The global force identity: the net forces sum to zero, for every stress. -/
theorem sum_bal (p : Cfg n) (bar : Fin nb → Fin n × Fin n) (σ : Fin nb → ℝ) :
    ∑ k, bal p bar σ k = 0 := by
  unfold bal
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.smul_sum]
  have : ∑ k, contrib p (bar b) k = 0 := by
    have e : ∀ k, contrib p (bar b) k = contrib p ((bar b).1, (bar b).2) k := fun k => rfl
    simp only [e, contrib_split, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    abel
  rw [this, smul_zero]

/-- The cross product `a × b`. -/
def crs (a b : ℝ × ℝ) : ℝ := a.1 * b.2 - a.2 * b.1

/-- The global moment identity. -/
theorem sum_moment (p : Cfg n) (bar : Fin nb → Fin n × Fin n) (σ : Fin nb → ℝ) :
    ∑ k, crs (p k) (bal p bar σ k) = 0 := by
  have lin : ∀ k, crs (p k) (bal p bar σ k) = ∑ b, σ b * crs (p k) (contrib p (bar b) k) := by
    intro k
    unfold bal crs
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => by ring
  simp only [lin]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ k, crs (p k) (contrib p (bar b) k) = 0 := by
    have e : ∀ k, crs (p k) (contrib p (bar b) k)
        = (if (bar b).1 = k then crs (p (bar b).1) (p (bar b).2 - p (bar b).1) else 0)
          + (if (bar b).2 = k then crs (p (bar b).2) (p (bar b).1 - p (bar b).2) else 0) := by
      intro k
      rw [show contrib p (bar b) k = contrib p ((bar b).1, (bar b).2) k from rfl, contrib_split]
      by_cases h1 : (bar b).1 = k <;> by_cases h2 : (bar b).2 = k <;>
        simp [h1, h2, crs] <;> (try subst h1) <;> (try subst h2) <;> ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    unfold crs; simp only [Prod.fst_sub, Prod.snd_sub]; ring
  rw [this, mul_zero]

/-! ## The reverse Henneberg recursion -/

lemma bal_update (p : Cfg n) (bar : Fin nb → Fin n × Fin n) (σ : Fin nb → ℝ) (b : Fin nb) (c : ℝ)
    (k : Fin n) : bal p bar (Function.update σ b c) k = bal p bar σ k + (c - σ b) • contrib p (bar b) k := by
  unfold bal
  have : ∀ b', Function.update σ b c b' • contrib p (bar b') k
      = σ b' • contrib p (bar b') k + (if b' = b then (c - σ b) • contrib p (bar b) k else 0) := by
    intro b'
    by_cases h : b' = b
    · subst h; simp [sub_smul]
    · simp [h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Does the bar `bar` have `k` as an endpoint? -/
def incident (bar : Fin n × Fin n) (k : Fin n) : Bool := decide (bar.1 = k) || decide (bar.2 = k)

lemma contrib_zero {p : Cfg n} {bar : Fin n × Fin n} {k : Fin n} (h : incident bar k = false) :
    contrib p bar k = 0 := by
  unfold incident at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  unfold contrib; simp [h.1, h.2]

lemma contrib_at {p : Cfg n} {bar : Fin n × Fin n} {k i : Fin n} (hik : i ≠ k)
    (h : (decide (bar = (k, i)) || decide (bar = (i, k))) = true) : contrib p bar k = p i - p k := by
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  unfold contrib
  rcases h with rfl | rfl
  · simp
  · simp [hik]

/-- One step of the recursion: vertex `k`, joined to `i`, `j` by bars `bi`, `bj`. -/
structure HStep (n nb : ℕ) where
  k : Fin n
  i : Fin n
  j : Fin n
  bi : Fin nb
  bj : Fin nb
  deriving DecidableEq, Repr

/-- The Henneberg determinant of a step, `det(p_i − p_k, p_j − p_k)`. -/
def stepDet (p : Cfg n) (s : HStep n nb) : ℝ :=
  (p s.i - p s.k).1 * (p s.j - p s.k).2 - (p s.i - p s.k).2 * (p s.j - p s.k).1

/-- Cramer's rule at `s.k`: the stresses on `bi`, `bj` that cancel the current force. -/
noncomputable def cramerStep (p : Cfg n) (bar : Fin nb → Fin n × Fin n) (σ : Fin nb → ℝ)
    (s : HStep n nb) : Fin nb → ℝ :=
  let F := bal p bar σ s.k
  let u := p s.i - p s.k
  let w := p s.j - p s.k
  let D := u.1 * w.2 - u.2 * w.1
  Function.update (Function.update σ s.bi (((-F.1) * w.2 + F.2 * w.1) / D)) s.bj (((-F.2) * u.1 + F.1 * u.2) / D)

/-- The conditions on one step, given the vertices already processed and the bars
already assigned: `k ∉ {0, 1}`; the bars join `k` to `i`, `j`; they are new, not
among the preset ones, and not incident to any processed vertex. -/
def stepOK (bar : Fin nb → Fin n × Fin n) (extras : List (Fin nb)) (P : List (Fin n))
    (A : List (Fin nb)) (s : HStep n nb) : Bool :=
  -- the two bars are forced once (the kernel would otherwise re-read them for every `k'`)
  match bar s.bi, bar s.bj with
  | (x1, x2), (y1, y2) =>
    decide (2 ≤ s.k.val) && decide (s.i ≠ s.k) && decide (s.j ≠ s.k)
    && (decide ((x1, x2) = (s.k, s.i)) || decide ((x1, x2) = (s.i, s.k)))
    && (decide ((y1, y2) = (s.k, s.j)) || decide ((y1, y2) = (s.j, s.k)))
    && decide (s.bi ≠ s.bj) && !(A.contains s.bi) && !(A.contains s.bj)
    && !(extras.contains s.bi) && !(extras.contains s.bj)
    && P.all (fun k' => !incident (x1, x2) k' && !incident (y1, y2) k')

def stepsOK (bar : Fin nb → Fin n × Fin n) (extras : List (Fin nb)) :
    List (Fin n) → List (Fin nb) → List (HStep n nb) → Bool
  | _, _, [] => true
  | P, A, s :: rest => stepOK bar extras P A s && stepsOK bar extras (s.k :: P) (s.bi :: s.bj :: A) rest

lemma not_mem_of_contains {α : Type*} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : (!l.contains a) = true) : a ∉ l := by
  intro hm
  rw [List.contains_iff_mem.mpr hm] at h
  exact Bool.noConfusion h

lemma stepOK_spec {bar : Fin nb → Fin n × Fin n} {extras : List (Fin nb)} {P : List (Fin n)}
    {A : List (Fin nb)} {s : HStep n nb} (h : stepOK bar extras P A s = true) :
    2 ≤ s.k.val ∧ s.i ≠ s.k ∧ s.j ≠ s.k
    ∧ (decide (bar s.bi = (s.k, s.i)) || decide (bar s.bi = (s.i, s.k))) = true
    ∧ (decide (bar s.bj = (s.k, s.j)) || decide (bar s.bj = (s.j, s.k))) = true
    ∧ s.bi ≠ s.bj ∧ s.bi ∉ A ∧ s.bj ∉ A ∧ s.bi ∉ extras ∧ s.bj ∉ extras
    ∧ ∀ k ∈ P, incident (bar s.bi) k = false ∧ incident (bar s.bj) k = false := by
  unfold stepOK at h
  rcases hx : bar s.bi with ⟨x1, x2⟩
  rcases hy : bar s.bj with ⟨y1, y2⟩
  rw [hx, hy] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, h4, h5,
    of_decide_eq_true h6, not_mem_of_contains h7, not_mem_of_contains h8, not_mem_of_contains h9,
    not_mem_of_contains h10, fun k hk => ?_⟩
  have := List.all_eq_true.mp h11 k hk
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this

lemma fold_unchanged (p : Cfg n) (bar : Fin nb → Fin n × Fin n) :
    ∀ (steps : List (HStep n nb)) (σ : Fin nb → ℝ) (b : Fin nb),
      (∀ s ∈ steps, b ≠ s.bi ∧ b ≠ s.bj) → steps.foldl (cramerStep p bar) σ b = σ b
  | [], _, _, _ => rfl
  | s :: rest, σ, b, h => by
    simp only [List.foldl_cons]
    rw [fold_unchanged p bar rest _ b (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))]
    obtain ⟨h1, h2⟩ := h s List.mem_cons_self
    simp [cramerStep, Function.update_apply, h1, h2]

/-- **The recursion balances every processed vertex.** -/
lemma fold_bal (p : Cfg n) (bar : Fin nb → Fin n × Fin n) (extras : List (Fin nb)) :
    ∀ (steps : List (HStep n nb)) (P : List (Fin n)) (A : List (Fin nb)) (σ : Fin nb → ℝ),
      stepsOK bar extras P A steps = true → (∀ s ∈ steps, stepDet p s ≠ 0) →
      (∀ k ∈ P, bal p bar σ k = 0) → (∀ b, b ∉ A → b ∉ extras → σ b = 0) →
      ∀ k ∈ P ++ steps.map (·.k), bal p bar (steps.foldl (cramerStep p bar) σ) k = 0
  | [], P, A, σ, _, _, hP, _ => by simpa using hP
  | s :: rest, P, A, σ, hok, hdet, hP, hA => by
    simp only [stepsOK, Bool.and_eq_true] at hok
    obtain ⟨hs, hrest⟩ := hok
    obtain ⟨hk2, hik, hjk, hbi, hbj, hbij, hbiA, hbjA, hbiE, hbjE, hinc⟩ := stepOK_spec hs
    have hsi : σ s.bi = 0 := hA _ hbiA hbiE
    have hsj : σ s.bj = 0 := hA _ hbjA hbjE
    set σ' := cramerStep p bar σ s with hσ'
    -- the balance after the step, at any vertex
    have hbal' : ∀ k', bal p bar σ' k' = bal p bar σ k'
        + (((-(bal p bar σ s.k).1) * (p s.j - p s.k).2 + (bal p bar σ s.k).2 * (p s.j - p s.k).1) / stepDet p s)
            • contrib p (bar s.bi) k'
        + (((-(bal p bar σ s.k).2) * (p s.i - p s.k).1 + (bal p bar σ s.k).1 * (p s.i - p s.k).2) / stepDet p s)
            • contrib p (bar s.bj) k' := by
      intro k'
      simp only [hσ', cramerStep, stepDet]
      rw [bal_update, bal_update]
      simp only [Function.update_apply, if_neg (Ne.symm hbij), hsi, hsj, sub_zero]
      try abel
    have hP' : ∀ k ∈ s.k :: P, bal p bar σ' k = 0 := by
      intro k hk
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · rw [hbal', contrib_at hik hbi, contrib_at hjk hbj]
        have hD := hdet s List.mem_cons_self
        unfold stepDet at hD
        obtain ⟨e1, e2⟩ := cramer_bal (F1 := (bal p bar σ s.k).1) (F2 := (bal p bar σ s.k).2)
          (a1 := (p s.i - p s.k).1) (a2 := (p s.i - p s.k).2) (b1 := (p s.j - p s.k).1)
          (b2 := (p s.j - p s.k).2) hD
        unfold stepDet
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]; linarith
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero]; linarith
      · have hi := hinc k hk
        rw [hbal', contrib_zero hi.1, contrib_zero hi.2, hP k hk]
        simp
    have hA' : ∀ b, b ∉ s.bi :: s.bj :: A → b ∉ extras → σ' b = 0 := by
      intro b hb hbe
      simp only [List.mem_cons, not_or] at hb
      simp only [hσ', cramerStep, Function.update_apply, if_neg hb.1, if_neg hb.2.1]
      exact hA b hb.2.2 hbe
    have := fold_bal p bar extras rest (s.k :: P) (s.bi :: s.bj :: A) σ' hrest
      (fun s' hs' => hdet s' (List.mem_cons_of_mem _ hs')) hP' hA'
    intro k hk
    simp only [List.foldl_cons]
    apply this
    simp only [List.mem_append, List.mem_cons, List.map_cons] at hk ⊢
    tauto

/-- The recursion, then the pinned bar `pb` at vertex `i1`, along `p i0 − p i1`. -/
noncomputable def stressR (p : Cfg n) (bar : Fin nb → Fin n × Fin n) (σ0 : Fin nb → ℝ)
    (steps : List (HStep n nb)) (i0 i1 : Fin n) (pb : Fin nb) : Fin nb → ℝ :=
  let σ := steps.foldl (cramerStep p bar) σ0
  let G := bal p bar σ i1
  let u := p i0 - p i1
  Function.update σ pb ((-(G.1 * u.1 + G.2 * u.2)) / (u.1 * u.1 + u.2 * u.2))

/-- **Every vertex balances.** -/
theorem bal_zero (p : Cfg n) (bar : Fin nb → Fin n × Fin n) (σ0 : Fin nb → ℝ) (extras : List (Fin nb))
    (hσ0 : ∀ b, b ∉ extras → σ0 b = 0) (steps : List (HStep n nb)) (i0 i1 : Fin n) (pb : Fin nb)
    (hi0 : i0.val = 0) (hi1 : i1.val = 1) (h01 : p i0 ≠ p i1)
    (hok : stepsOK bar extras [] [] steps = true) (hdet : ∀ s ∈ steps, stepDet p s ≠ 0)
    (hcov : ∀ k, k = i0 ∨ k = i1 ∨ k ∈ steps.map (·.k))
    (hpb : bar pb = (i0, i1) ∨ bar pb = (i1, i0)) (hpbS : ∀ s ∈ steps, pb ≠ s.bi ∧ pb ≠ s.bj)
    (hpbE : pb ∉ extras) :
    ∀ k, bal p bar (stressR p bar σ0 steps i0 i1 pb) k = 0 := by
  set σ := steps.foldl (cramerStep p bar) σ0 with hσ
  have hfold := fold_bal p bar extras steps [] [] σ0 hok hdet (by simp)
    (fun b _ hb => hσ0 b hb)
  simp only [List.nil_append] at hfold
  have hσpb : σ pb = 0 := by rw [hσ, fold_unchanged p bar steps σ0 pb hpbS]; exact hσ0 pb hpbE
  have hi01 : i0 ≠ i1 := by intro h; rw [h] at hi0; omega
  -- the step vertices are not 0, 1, so the pinned bar does not touch them
  have hk2 : ∀ k ∈ steps.map (·.k), 2 ≤ k.val := by
    have aux : ∀ (steps : List (HStep n nb)) (P : List (Fin n)) (A : List (Fin nb)),
        stepsOK bar extras P A steps = true → ∀ k ∈ steps.map (·.k), 2 ≤ k.val := by
      intro steps
      induction steps with
      | nil => simp
      | cons s rest ih =>
        intro P A h k hk
        simp only [stepsOK, Bool.and_eq_true] at h
        simp only [List.map_cons, List.mem_cons] at hk
        rcases hk with rfl | hk
        · exact (stepOK_spec h.1).1
        · exact ih _ _ h.2 k hk
    exact aux steps [] [] hok
  have hpbinc : ∀ k ∈ steps.map (·.k), incident (bar pb) k = false := by
    intro k hk
    have := hk2 k hk
    unfold incident
    rcases hpb with h | h <;> rw [h] <;>
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] <;>
      constructor <;> intro e <;> subst e <;> omega
  unfold stressR
  simp only [← hσ]
  set G := bal p bar σ i1
  set u := p i0 - p i1
  set c := (-(G.1 * u.1 + G.2 * u.2)) / (u.1 * u.1 + u.2 * u.2)
  set σf := Function.update σ pb c with hσf
  have hbalf : ∀ k, bal p bar σf k = bal p bar σ k + c • contrib p (bar pb) k := by
    intro k; rw [hσf, bal_update, hσpb, sub_zero]
  have hsteps : ∀ k ∈ steps.map (·.k), bal p bar σf k = 0 := by
    intro k hk; rw [hbalf, contrib_zero (hpbinc k hk), hfold k hk]; simp
  have hc1 : contrib p (bar pb) i1 = p i0 - p i1 := by
    unfold contrib
    rcases hpb with h | h <;> rw [h] <;> simp [hi01]
  have hu : u.1 * u.1 + u.2 * u.2 ≠ 0 := by
    intro h0
    have h1 : u.1 = 0 := by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2]
    have h2 : u.2 = 0 := by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2]
    exact h01 (sub_eq_zero.mp (Prod.ext h1 h2))
  have hpin : (bal p bar σf i1).1 * u.1 + (bal p bar σf i1).2 * u.2 = 0 := by
    rw [hbalf, hc1]
    have := pin_bal (G1 := G.1) (G2 := G.2) (u1 := u.1) (u2 := u.2) hu
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linarith
  -- global force and moment identities
  have hothers : ∀ k, k ≠ i0 ∧ k ≠ i1 → bal p bar σf k = 0 := by
    intro k hk
    rcases hcov k with h | h | h
    · exact absurd h hk.1
    · exact absurd h hk.2
    · exact hsteps k h
  have hsum := sum_bal p bar σf
  rw [Finset.sum_eq_add i0 i1 hi01 (fun k _ hk => hothers k hk) (by simp) (by simp)] at hsum
  have hmom := sum_moment p bar σf
  rw [Finset.sum_eq_add i0 i1 hi01 (fun k _ hk => by rw [hothers k hk]; simp [crs]) (by simp) (by simp)] at hmom
  have e0 : bal p bar σf i0 = -bal p bar σf i1 := by rw [add_eq_zero_iff_eq_neg] at hsum; exact hsum
  rw [e0] at hmom
  have hB : bal p bar σf i1 = 0 := by
    set B := bal p bar σf i1
    have m : u.1 * B.2 - u.2 * B.1 = 0 := by
      simp only [crs, Prod.fst_neg, Prod.snd_neg] at hmom
      have : u = p i0 - p i1 := rfl
      simp only [this, Prod.fst_sub, Prod.snd_sub]; linarith
    have b1 : (u.1 * u.1 + u.2 * u.2) * B.1 = 0 := by linear_combination u.1 * hpin - u.2 * m
    have b2 : (u.1 * u.1 + u.2 * u.2) * B.2 = 0 := by linear_combination u.2 * hpin + u.1 * m
    exact Prod.ext ((mul_eq_zero.mp b1).resolve_left hu) ((mul_eq_zero.mp b2).resolve_left hu)
  intro k
  by_cases h0 : k = i0
  · subst h0; rw [e0, hB, neg_zero]
  · by_cases h1 : k = i1
    · subst h1; exact hB
    · exact hothers k ⟨h0, h1⟩

/-! ## Enclosing the stress: a certificate checked step by step

`sd[b]` is a claimed enclosure of the stress on bar `b`. `stressCheck` recomputes,
in interval arithmetic, each Cramer step from the claimed enclosures of the bars
it depends on, and requires the result to lie inside the claim; the same for
the pinned bar. `stress_sound`: if the check passes, every claim is true. -/

/-- The preset stresses, `N / 2^30` on the bars listed. -/
noncomputable def presetσ (ex : List (Fin nb × ℤ)) (b : Fin nb) : ℝ :=
  ((ex.find? (fun e => decide (e.1 = b))).map (fun e => (e.2 : ℝ) / 2 ^ 30)).getD 0

def presetFI (N : ℤ) : FI := ⟨N * 2 ^ 354, N * 2 ^ 354⟩

lemma mem_presetFI (N : ℤ) : FI.mem ((N : ℝ) / 2 ^ 30) (presetFI N) := by
  have e : ((N * 2 ^ 354 : ℤ) : ℝ) / (2 : ℝ) ^ K = (N : ℝ) / 2 ^ 30 := by
    have hK : K = 354 + 30 := by unfold K; rfl
    rw [hK, pow_add]; push_cast
    field_simp
  unfold FI.mem presetFI val; rw [e]; exact ⟨le_rfl, le_rfl⟩

lemma presetσ_zero (ex : List (Fin nb × ℤ)) (b : Fin nb) (h : b ∉ ex.map (·.1)) : presetσ ex b = 0 := by
  unfold presetσ
  have : ex.find? (fun e => decide (e.1 = b)) = none := by
    rw [List.find?_eq_none]
    intro e he; simp only [decide_eq_true_eq]
    intro heq; exact h (List.mem_map.mpr ⟨e, he, heq⟩)
  rw [this]; rfl

/-- The interval vector `v − w`. -/
def psubFI (v w : FI × FI) : FI × FI := (sub v.1 w.1, sub v.2 w.2)
def paddFI (v w : FI × FI) : FI × FI := (add v.1 w.1, add v.2 w.2)
def pscaleFI (c : FI) (v : FI × FI) : FI × FI := (mul c v.1, mul c v.2)
def pzeroFI : FI × FI := (ofInt 0, ofInt 0)

/-- The unit force of `bar` at `k`, as an interval vector (`none` if not incident). -/
def contribFI (vd : List (FI × FI)) (bar : Fin n × Fin n) (k : Fin n) : Option (FI × FI) :=
  if bar.1 = k then (match vd[bar.2.val]?, vd[k.val]? with
    | some a, some c => some (psubFI a c) | _, _ => none)
  else if bar.2 = k then (match vd[bar.1.val]?, vd[k.val]? with
    | some a, some c => some (psubFI a c) | _, _ => none)
  else none

/-- One bar's term in the interval force at `k` (all bars but `x`, `y`). -/
def forceAcc (vd : List (FI × FI)) (sd : List FI) (known : List (Fin nb)) (k : Fin n) (x y : Fin nb)
    (acc : Option (FI × FI)) (e : Fin nb × (Fin n × Fin n)) : Option (FI × FI) :=
  match acc with
  | none => none
  | some v =>
    if incident e.2 k && decide (e.1 ≠ x) && decide (e.1 ≠ y) then
      (if known.contains e.1 then
        (match contribFI vd e.2 k, sd[e.1.val]? with
          | some c, some σb => some (paddFI v (pscaleFI σb c))
          | _, _ => none)
       else none)
    else some v

/-- The force at `k` from every incident bar except `x`, `y`, which must all be
known (in `known`); `none` if one is not, or an index is out of range. The bars
come as the list `bl` of `(index, endpoints)`, so that the kernel never indexes
into the bar list. -/
def forceFI (vd : List (FI × FI)) (sd : List FI) (bl : List (Fin nb × (Fin n × Fin n)))
    (known : List (Fin nb)) (k : Fin n) (x y : Fin nb) : Option (FI × FI) :=
  bl.foldl (forceAcc vd sd known k x y) (some pzeroFI)

/-- Cramer's rule in intervals. -/
def cramerFI (F u w : FI × FI) : Option (FI × FI) :=
  let D := sub (mul u.1 w.2) (mul u.2 w.1)
  match div (add (mul (neg F.1) w.2) (mul F.2 w.1)) D, div (add (mul (neg F.2) u.1) (mul F.1 u.2)) D with
  | some c1, some c2 => some (c1, c2)
  | _, _ => none

def stepFIOK (vd : List (FI × FI)) (sd : List FI) (bl : List (Fin nb × (Fin n × Fin n)))
    (known : List (Fin nb)) (s : HStep n nb) : Bool :=
  match forceFI vd sd bl known s.k s.bi s.bj, vd[s.i.val]?, vd[s.j.val]?, vd[s.k.val]?,
    sd[s.bi.val]?, sd[s.bj.val]? with
  | some F, some Pi, some Pj, some Pk, some Si, some Sj =>
    match cramerFI F (psubFI Pi Pk) (psubFI Pj Pk) with
    | some c => c.1.subset Si && c.2.subset Sj
    | none => false
  | _, _, _, _, _, _ => false

def stepsFIOK (vd : List (FI × FI)) (sd : List FI) (bl : List (Fin nb × (Fin n × Fin n))) :
    List (Fin nb) → List (HStep n nb) → Bool
  | _, [] => true
  | known, s :: rest => stepFIOK vd sd bl known s && stepsFIOK vd sd bl (s.bi :: s.bj :: known) rest

/-- The pinned bar `pb`, fixed last at `i1` along `p i0 − p i1`. -/
def pinFIOK (vd : List (FI × FI)) (sd : List FI) (bl : List (Fin nb × (Fin n × Fin n)))
    (known : List (Fin nb)) (i0 i1 : Fin n) (pb : Fin nb) : Bool :=
  match forceFI vd sd bl known i1 pb pb, vd[i0.val]?, vd[i1.val]?, sd[pb.val]? with
  | some G, some P0, some P1, some Sp =>
    let u := psubFI P0 P1
    match div (neg (add (mul G.1 u.1) (mul G.2 u.2))) (add (mul u.1 u.1) (mul u.2 u.2)) with
    | some c => c.subset Sp
    | none => false
  | _, _, _, _ => false

/-- The preset stresses are enclosed. -/
def presetOK (sd : List FI) (ex : List (Fin nb × ℤ)) : Bool :=
  ex.all fun e => match sd[e.1.val]? with
    | some S => (presetFI e.2).subset S
    | none => false

/-! ### Soundness -/

lemma pmem_sub {a b : ℝ × ℝ} {A B : FI × FI} (ha : PMem a A) (hb : PMem b B) : PMem (a - b) (psubFI A B) :=
  ⟨mem_sub ha.1 hb.1, mem_sub ha.2 hb.2⟩
lemma pmem_add {a b : ℝ × ℝ} {A B : FI × FI} (ha : PMem a A) (hb : PMem b B) : PMem (a + b) (paddFI A B) :=
  ⟨mem_add ha.1 hb.1, mem_add ha.2 hb.2⟩
lemma pmem_scale {c : ℝ} {a : ℝ × ℝ} {C : FI} {A : FI × FI} (hc : FI.mem c C) (ha : PMem a A) :
    PMem (c • a) (pscaleFI C A) := ⟨mem_mul hc ha.1, mem_mul hc ha.2⟩
lemma pmem_zero : PMem (0 : ℝ × ℝ) pzeroFI := by
  have h := mem_ofInt 0; simp only [Int.cast_zero] at h; exact ⟨h, h⟩

/-- `sd` encloses `σ` on the bars of `known`. -/
def SdEncl (sd : List FI) (σ : Fin nb → ℝ) (known : List (Fin nb)) : Prop :=
  ∀ b ∈ known, ∃ S, sd[b.val]? = some S ∧ FI.mem (σ b) S

lemma contribFI_sound {p : Cfg n} {vd : List (FI × FI)} (he : Encl p vd) {bar : Fin n × Fin n} {k : Fin n}
    {C : FI × FI} (h : contribFI vd bar k = some C) : PMem (contrib p bar k) C := by
  obtain ⟨hlen, hq⟩ := he
  have g : ∀ m : Fin n, vd[m.val]? = some (vd[m.val]'(by rw [hlen]; exact m.isLt)) :=
    fun m => List.getElem?_eq_getElem _
  unfold contribFI at h
  unfold contrib
  split_ifs at h ⊢ with h1 h2
  · rw [g, g] at h; simp only [Option.some.injEq] at h; subst h
    exact pmem_sub (hq _) (hq _)
  · rw [g, g] at h; simp only [Option.some.injEq] at h; subst h
    exact pmem_sub (hq _) (hq _)

lemma forceAcc_none (vd : List (FI × FI)) (sd : List FI) (known : List (Fin nb)) (k : Fin n) (x y : Fin nb) :
    ∀ l : List (Fin nb × (Fin n × Fin n)), l.foldl (forceAcc vd sd known k x y) none = none
  | [] => rfl
  | _ :: l => forceAcc_none vd sd known k x y l

lemma forceAcc_some (vd : List (FI × FI)) (sd : List FI) (known : List (Fin nb)) (k : Fin n)
    (x y : Fin nb) (v : FI × FI) (e : Fin nb × (Fin n × Fin n)) :
    forceAcc vd sd known k x y (some v) e =
      if incident e.2 k && decide (e.1 ≠ x) && decide (e.1 ≠ y) then
        (if known.contains e.1 then
          (match contribFI vd e.2 k, sd[e.1.val]? with
            | some c, some σb => some (paddFI v (pscaleFI σb c))
            | _, _ => none)
         else none)
      else some v := rfl

lemma forceFI_step {p : Cfg n} {vd : List (FI × FI)} (he : Encl p vd) {sd : List FI}
    {bar : Fin nb → Fin n × Fin n} {known : List (Fin nb)} {σ : Fin nb → ℝ} (hsd : SdEncl sd σ known)
    {k : Fin n} {x y : Fin nb} (hx : σ x = 0) (hy : σ y = 0) :
    ∀ (l : List (Fin nb × (Fin n × Fin n))), (∀ e ∈ l, e.2 = bar e.1) →
      ∀ (a : ℝ × ℝ) (A V : FI × FI), PMem a A →
      l.foldl (forceAcc vd sd known k x y) (some A) = some V →
      PMem (a + (l.map fun e => σ e.1 • contrib p (bar e.1) k).sum) V := by
  intro l
  induction l with
  | nil => intro _ a A V ha h; simp only [List.foldl_nil, Option.some.injEq] at h; subst h; simpa using ha
  | cons e l ih =>
    intro hl a A V ha h
    have hl' : ∀ e' ∈ l, e'.2 = bar e'.1 := fun e' he' => hl e' (List.mem_cons_of_mem _ he')
    have he2 : e.2 = bar e.1 := hl e List.mem_cons_self
    simp only [List.foldl_cons] at h
    simp only [List.map_cons, List.sum_cons, ← add_assoc]
    rw [forceAcc_some] at h
    by_cases hc : (incident e.2 k && decide (e.1 ≠ x) && decide (e.1 ≠ y)) = true
    · rw [if_pos hc] at h
      by_cases hk : known.contains e.1 = true
      · rw [if_pos hk] at h
        cases hC : contribFI vd e.2 k with
        | none => rw [hC] at h; simp only at h; rw [forceAcc_none] at h; cases h
        | some C =>
          cases hS : sd[e.1.val]? with
          | none => rw [hC, hS] at h; simp only at h; rw [forceAcc_none] at h; cases h
          | some Sb =>
            rw [hC, hS] at h
            simp only at h
            obtain ⟨S', hS', hmem⟩ := hsd e.1 (List.contains_iff_mem.mp hk)
            rw [hS] at hS'; simp only [Option.some.injEq] at hS'; subst hS'
            rw [he2] at hC
            exact ih hl' _ _ V (pmem_add ha (pmem_scale hmem (contribFI_sound he hC))) h
      · rw [if_neg hk] at h; rw [forceAcc_none] at h; cases h
    · rw [if_neg hc] at h
      have hz : σ e.1 • contrib p (bar e.1) k = 0 := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and_or, Bool.not_eq_true] at hc
        rcases hc with (hc | hc) | hc
        · rw [← he2, contrib_zero hc, smul_zero]
        · push Not at hc; rw [hc, hx, zero_smul]
        · push Not at hc; rw [hc, hy, zero_smul]
      rw [hz, add_zero]
      exact ih hl' a A V ha h

/-- The bar list in the form the kernel reads, and the map it stands for. -/
lemma zip_finRange {α : Type*} (L : List α) :
    (List.finRange L.length).zip L = (List.finRange L.length).map fun b => (b, L[b.val]'b.isLt) := by
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp

lemma forceFI_sound {p : Cfg n} {vd : List (FI × FI)} (he : Encl p vd) {sd : List FI}
    {bar : Fin nb → Fin n × Fin n} {bl : List (Fin nb × (Fin n × Fin n))}
    (hbl : bl = (List.finRange nb).map fun b => (b, bar b))
    {known : List (Fin nb)} {σ : Fin nb → ℝ} (hsd : SdEncl sd σ known)
    {k : Fin n} {x y : Fin nb} (hx : σ x = 0) (hy : σ y = 0) {V : FI × FI}
    (h : forceFI vd sd bl known k x y = some V) : PMem (bal p bar σ k) V := by
  unfold forceFI at h
  have hbl' : ∀ e ∈ bl, e.2 = bar e.1 := by
    rw [hbl]; intro e he'
    simp only [List.mem_map] at he'
    obtain ⟨b, _, rfl⟩ := he'; rfl
  have := forceFI_step he hsd hx hy bl hbl' 0 pzeroFI V pmem_zero h
  unfold bal
  rw [Fin.sum_univ_def]
  subst hbl
  simpa [List.map_map, Function.comp_def] using this

lemma cramerFI_sound {F u w : ℝ × ℝ} {Fi ui wi : FI × FI} {c : FI × FI} (hF : PMem F Fi)
    (hu : PMem u ui) (hw : PMem w wi) (h : cramerFI Fi ui wi = some c) :
    FI.mem (((-F.1) * w.2 + F.2 * w.1) / (u.1 * w.2 - u.2 * w.1)) c.1 ∧
      FI.mem (((-F.2) * u.1 + F.1 * u.2) / (u.1 * w.2 - u.2 * w.1)) c.2 := by
  unfold cramerFI at h
  simp only at h
  have hD := mem_sub (mem_mul hu.1 hw.2) (mem_mul hu.2 hw.1)
  cases h1 : div (add (mul (neg Fi.1) wi.2) (mul Fi.2 wi.1)) (sub (mul ui.1 wi.2) (mul ui.2 wi.1)) <;>
    cases h2 : div (add (mul (neg Fi.2) ui.1) (mul Fi.1 ui.2)) (sub (mul ui.1 wi.2) (mul ui.2 wi.1)) <;>
    rw [h1, h2] at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
  subst h
  exact ⟨mem_div (mem_add (mem_mul (mem_neg hF.1) hw.2) (mem_mul hF.2 hw.1)) hD h1,
         mem_div (mem_add (mem_mul (mem_neg hF.2) hu.1) (mem_mul hF.1 hu.2)) hD h2⟩

lemma encl_get {p : Cfg n} {vd : List (FI × FI)} (he : Encl p vd) {k : Fin n} {P : FI × FI}
    (h : vd[k.val]? = some P) : PMem (p k) P := by
  obtain ⟨hlen, hq⟩ := he
  rw [List.getElem?_eq_getElem (by rw [hlen]; exact k.isLt), Option.some.injEq] at h
  rw [← h]; exact hq k

/-- The known bars after the recursion. -/
def knownAfter (known : List (Fin nb)) (steps : List (HStep n nb)) : List (Fin nb) :=
  known ++ steps.flatMap fun s => [s.bi, s.bj]

/-- **The recursion stays inside the claimed enclosures.** -/
lemma fold_encl {p : Cfg n} {vd : List (FI × FI)} (he : Encl p vd) {sd : List FI}
    {bar : Fin nb → Fin n × Fin n} {bl : List (Fin nb × (Fin n × Fin n))}
    (hbl : bl = (List.finRange nb).map fun b => (b, bar b)) (extras : List (Fin nb)) :
    ∀ (steps : List (HStep n nb)) (P : List (Fin n)) (A known : List (Fin nb)) (σ : Fin nb → ℝ),
      stepsOK bar extras P A steps = true → stepsFIOK vd sd bl known steps = true →
      (∀ b ∈ known, b ∈ A ∨ b ∈ extras) → SdEncl sd σ known →
      (∀ b, b ∉ A → b ∉ extras → σ b = 0) →
      SdEncl sd (steps.foldl (cramerStep p bar) σ) (knownAfter known steps)
  | [], _, _, known, σ, _, _, _, hsd, _ => by simpa [knownAfter] using hsd
  | s :: rest, P, A, known, σ, hok, hfi, hkA, hsd, hA => by
    simp only [stepsOK, Bool.and_eq_true] at hok
    obtain ⟨hs, hrest⟩ := hok
    obtain ⟨hk2, hik, hjk, hbi, hbj, hbij, hbiA, hbjA, hbiE, hbjE, hinc⟩ := stepOK_spec hs
    simp only [stepsFIOK, Bool.and_eq_true] at hfi
    obtain ⟨hstep, hfrest⟩ := hfi
    have hsi : σ s.bi = 0 := hA _ hbiA hbiE
    have hsj : σ s.bj = 0 := hA _ hbjA hbjE
    have hbiK : s.bi ∉ known := fun h => (hkA _ h).elim hbiA hbiE
    have hbjK : s.bj ∉ known := fun h => (hkA _ h).elim hbjA hbjE
    unfold stepFIOK at hstep
    cases hF : forceFI vd sd bl known s.k s.bi s.bj with
    | none => rw [hF] at hstep; cases hstep
    | some F =>
    cases hPi : vd[s.i.val]? with
    | none => rw [hF, hPi] at hstep; cases hstep
    | some Pi =>
    cases hPj : vd[s.j.val]? with
    | none => rw [hF, hPi, hPj] at hstep; cases hstep
    | some Pj =>
    cases hPk : vd[s.k.val]? with
    | none => rw [hF, hPi, hPj, hPk] at hstep; cases hstep
    | some Pk =>
    cases hSi : sd[s.bi.val]? with
    | none => rw [hF, hPi, hPj, hPk, hSi] at hstep; cases hstep
    | some Si =>
    cases hSj : sd[s.bj.val]? with
    | none => rw [hF, hPi, hPj, hPk, hSi, hSj] at hstep; cases hstep
    | some Sj =>
    rw [hF, hPi, hPj, hPk, hSi, hSj] at hstep
    simp only at hstep
    cases hc : cramerFI F (psubFI Pi Pk) (psubFI Pj Pk) with
    | none => rw [hc] at hstep; cases hstep
    | some c =>
    rw [hc] at hstep
    simp only [Bool.and_eq_true] at hstep
    have hFm := forceFI_sound he hbl hsd hsi hsj hF
    have hu := pmem_sub (encl_get he hPi) (encl_get he hPk)
    have hw := pmem_sub (encl_get he hPj) (encl_get he hPk)
    obtain ⟨m1, m2⟩ := cramerFI_sound hFm hu hw hc
    set σ' := cramerStep p bar σ s with hσ'
    have e1 : σ' s.bi = ((-(bal p bar σ s.k).1) * (p s.j - p s.k).2 + (bal p bar σ s.k).2 * (p s.j - p s.k).1)
        / ((p s.i - p s.k).1 * (p s.j - p s.k).2 - (p s.i - p s.k).2 * (p s.j - p s.k).1) := by
      simp only [hσ', cramerStep, Function.update_apply, if_neg hbij, if_true]
    have e2 : σ' s.bj = ((-(bal p bar σ s.k).2) * (p s.i - p s.k).1 + (bal p bar σ s.k).1 * (p s.i - p s.k).2)
        / ((p s.i - p s.k).1 * (p s.j - p s.k).2 - (p s.i - p s.k).2 * (p s.j - p s.k).1) := by
      simp only [hσ', cramerStep, Function.update_apply, if_true]
    have hsd' : SdEncl sd σ' (s.bi :: s.bj :: known) := by
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | rfl | hb
      · exact ⟨Si, hSi, by rw [e1]; exact mem_of_subset m1 hstep.1⟩
      · exact ⟨Sj, hSj, by rw [e2]; exact mem_of_subset m2 hstep.2⟩
      · obtain ⟨S, hS, hm⟩ := hsd b hb
        have n1 : b ≠ s.bi := fun h => hbiK (h ▸ hb)
        have n2 : b ≠ s.bj := fun h => hbjK (h ▸ hb)
        refine ⟨S, hS, ?_⟩
        simp only [hσ', cramerStep, Function.update_apply, if_neg n1, if_neg n2]
        exact hm
    have hkA' : ∀ b ∈ s.bi :: s.bj :: known, b ∈ s.bi :: s.bj :: A ∨ b ∈ extras := by
      intro b hb
      simp only [List.mem_cons] at hb ⊢
      rcases hb with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · rcases hkA b h with h' | h'
        · exact Or.inl (Or.inr (Or.inr h'))
        · exact Or.inr h'
    have hA' : ∀ b, b ∉ s.bi :: s.bj :: A → b ∉ extras → σ' b = 0 := by
      intro b hb hbe
      simp only [List.mem_cons, not_or] at hb
      simp only [hσ', cramerStep, Function.update_apply, if_neg hb.1, if_neg hb.2.1]
      exact hA b hb.2.2 hbe
    have ih := fold_encl he hbl extras rest (s.k :: P) (s.bi :: s.bj :: A) (s.bi :: s.bj :: known) σ'
      hrest hfrest hkA' hsd' hA'
    simp only [List.foldl_cons]
    intro b hb
    apply ih b
    simp only [knownAfter, List.mem_append, List.mem_cons, List.flatMap_cons, List.mem_flatMap,
      List.not_mem_nil, or_false] at hb ⊢
    rcases hb with h | (h | h) | h
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr h

/-- The initial stresses are enclosed. -/
lemma preset_encl {sd : List FI} {ex : List (Fin nb × ℤ)} (h : presetOK sd ex = true) :
    SdEncl sd (presetσ ex) (ex.map (·.1)) := by
  intro b hb
  unfold presetσ
  cases hf : ex.find? (fun e => decide (e.1 = b)) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
    exact hf e he (by simp)
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hb' : e.1 = b := by simpa using List.find?_some hf
    unfold presetOK at h
    have := List.all_eq_true.mp h e he
    cases hS : sd[e.1.val]? with
    | none => rw [hS] at this; cases this
    | some S =>
      rw [hS] at this
      refine ⟨S, hb' ▸ hS, ?_⟩
      simp only [Option.map_some, Option.getD_some]
      exact mem_of_subset (mem_presetFI e.2) this

/-- **The stress certificate.** If the kernel checks pass, every bar of
`pb :: knownAfter` carries a stress inside its claimed enclosure. -/
theorem stress_encl {p : Cfg n} {vd : List (FI × FI)} (he : Encl p vd) {sd : List FI}
    {bar : Fin nb → Fin n × Fin n} {bl : List (Fin nb × (Fin n × Fin n))}
    (hbl : bl = (List.finRange nb).map fun b => (b, bar b)) (ex : List (Fin nb × ℤ))
    (steps : List (HStep n nb)) (i0 i1 : Fin n) (pb : Fin nb)
    (hok : stepsOK bar (ex.map (·.1)) [] [] steps = true) (hpre : presetOK sd ex = true)
    (hfi : stepsFIOK vd sd bl (ex.map (·.1)) steps = true)
    (hpin : pinFIOK vd sd bl (knownAfter (ex.map (·.1)) steps) i0 i1 pb = true)
    (hpbS : ∀ s ∈ steps, pb ≠ s.bi ∧ pb ≠ s.bj) (hpbE : pb ∉ ex.map (·.1)) :
    SdEncl sd (stressR p bar (presetσ ex) steps i0 i1 pb) (pb :: knownAfter (ex.map (·.1)) steps) := by
  have h0 : ∀ b, b ∉ ex.map (·.1) → presetσ ex b = 0 := fun b hb => presetσ_zero ex b hb
  have hsd := fold_encl he hbl (ex.map (·.1)) steps [] [] (ex.map (·.1)) (presetσ ex) hok hfi
    (fun b hb => Or.inr hb) (preset_encl hpre) (fun b _ hb => h0 b hb)
  set σ := steps.foldl (cramerStep p bar) (presetσ ex) with hσ
  have hσpb : σ pb = 0 := by rw [hσ, fold_unchanged p bar steps _ pb hpbS]; exact h0 pb hpbE
  have hpbK : pb ∉ knownAfter (ex.map (·.1)) steps := by
    intro h
    simp only [knownAfter, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with h | ⟨s, hs, h | h⟩
    · exact hpbE h
    · exact (hpbS s hs).1 h
    · exact (hpbS s hs).2 h
  unfold pinFIOK at hpin
  cases hG : forceFI vd sd bl (knownAfter (ex.map (·.1)) steps) i1 pb pb with
  | none => rw [hG] at hpin; cases hpin
  | some G =>
  cases hP0 : vd[i0.val]? with
  | none => rw [hG, hP0] at hpin; cases hpin
  | some P0 =>
  cases hP1 : vd[i1.val]? with
  | none => rw [hG, hP0, hP1] at hpin; cases hpin
  | some P1 =>
  cases hSp : sd[pb.val]? with
  | none => rw [hG, hP0, hP1, hSp] at hpin; cases hpin
  | some Sp =>
  rw [hG, hP0, hP1, hSp] at hpin
  simp only at hpin
  set U := psubFI P0 P1
  cases hc : div (neg (add (mul G.1 U.1) (mul G.2 U.2))) (add (mul U.1 U.1) (mul U.2 U.2)) with
  | none => rw [hc] at hpin; cases hpin
  | some c =>
  rw [hc] at hpin
  simp only at hpin
  have hGm := forceFI_sound he hbl hsd hσpb hσpb hG
  have hU : PMem (p i0 - p i1) U := pmem_sub (encl_get he hP0) (encl_get he hP1)
  have hcm := mem_div (mem_neg (mem_add (mem_mul hGm.1 hU.1) (mem_mul hGm.2 hU.2)))
    (mem_add (mem_mul hU.1 hU.1) (mem_mul hU.2 hU.2)) hc
  intro b hb
  unfold stressR
  simp only [← hσ]
  simp only [List.mem_cons] at hb
  rcases hb with rfl | hb
  · refine ⟨Sp, hSp, ?_⟩
    simp only [Function.update_apply, if_true]
    have e : ((-((bal p bar σ i1).1 * (p i0 - p i1).1 + (bal p bar σ i1).2 * (p i0 - p i1).2))
        / ((p i0 - p i1).1 * (p i0 - p i1).1 + (p i0 - p i1).2 * (p i0 - p i1).2))
        = -((bal p bar σ i1).1 * (p i0 - p i1).1 + (bal p bar σ i1).2 * (p i0 - p i1).2)
          / ((p i0 - p i1).1 * (p i0 - p i1).1 + (p i0 - p i1).2 * (p i0 - p i1).2) := rfl
    exact mem_of_subset hcm hpin
  · obtain ⟨S, hS, hm⟩ := hsd b hb
    have : b ≠ pb := fun h => hpbK (h ▸ hb)
    refine ⟨S, hS, ?_⟩
    simp only [Function.update_apply, if_neg this]
    exact hm

end Chiquipoli.Family.Trig
