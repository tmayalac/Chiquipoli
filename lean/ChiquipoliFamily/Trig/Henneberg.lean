/-
# Infinitesimal rigidity by a Henneberg order, proved once for every `n`

A displacement `w` that keeps every bar of a list `L` stationary to first order
is an infinitesimal rigid motion, provided the vertices can be added one at a
time: pin the bar `0 → 1`, then add each vertex `k` of an order, joined by two
bars of `L` to two vertices already added, with independent directions.

The order is data; `henOK` checks (in the kernel) that each step uses two bars of
`L` and two vertices already placed, and `detOK` checks, from the vertex
enclosures, that each step's two directions are independent. `rigid_of_henneberg`
is then a single theorem for every `n`, with no per-vertex proof.
-/
import ChiquipoliFamily.Trig.Checks
import ChiquipoliFamily.Basic

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real FI Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family

variable {n : ℕ}

/-- `L` contains the bar `{a, b}`, in either orientation. -/
def barMem (L : List (Fin n × Fin n)) (a b : Fin n) : Bool := L.contains (a, b) || L.contains (b, a)

/-- The order is valid: each step `(k, i, j)` joins `k` to two already placed
vertices `i ≠ j` by two bars of `L`. `done` are the vertices placed so far. -/
def henOK (L : List (Fin n × Fin n)) : List (Fin n) → List (Fin n × Fin n × Fin n) → Bool
  | _, [] => true
  | done, (k, i, j) :: rest =>
    done.contains i && done.contains j && barMem L k i && barMem L k j && henOK L (k :: done) rest

/-- Every vertex is `0`, `1` or placed by the order. -/
def coverOK (order : List (Fin n × Fin n × Fin n)) : Bool :=
  (List.finRange n).all fun k => decide (k.val = 0) || decide (k.val = 1) || (order.map (·.1)).contains k

lemma bar_of_mem {L : List (Fin n × Fin n)} {p w : Cfg n}
    (hL : ∀ ab ∈ L, ip (p ab.2 - p ab.1) (w ab.2 - w ab.1) = 0) {a b : Fin n} (h : barMem L a b = true) :
    ip (p a - p b) (w a - w b) = 0 := by
  unfold barMem at h
  simp only [Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h with h | h
  · exact bar_flip (hL _ h)
  · exact hL _ h

/-- The induction along the order. -/
lemma zero_along (L : List (Fin n × Fin n)) (p w : Cfg n)
    (hL : ∀ ab ∈ L, ip (p ab.2 - p ab.1) (w ab.2 - w ab.1) = 0) :
    ∀ (order : List (Fin n × Fin n × Fin n)) (done : List (Fin n)),
      henOK L done order = true →
      (∀ s ∈ order, (p s.1 - p s.2.1).1 * (p s.1 - p s.2.2).2 - (p s.1 - p s.2.1).2 * (p s.1 - p s.2.2).1 ≠ 0) →
      (∀ x ∈ done, w x = 0) → ∀ x ∈ order.map (·.1), w x = 0
  | [], _, _, _, _ => by simp
  | (k, i, j) :: rest, done, hok, hdet, hdone => by
    simp only [henOK, Bool.and_eq_true, List.contains_iff_mem] at hok
    obtain ⟨⟨⟨⟨hi, hj⟩, hbi⟩, hbj⟩, hrest⟩ := hok
    have hk : w k = 0 :=
      henneberg_step (bar_of_mem hL hbi) (bar_of_mem hL hbj) (hdone i hi) (hdone j hj)
        (hdet (k, i, j) (List.mem_cons_self))
    have ih := zero_along L p w hL rest (k :: done) hrest
      (fun s hs => hdet s (List.mem_cons_of_mem _ hs))
      (fun x hx => by
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hk
        · exact hdone x hx)
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hk
    · exact ih x hx

/-- **Rigidity from a Henneberg order.** -/
theorem rigid_of_henneberg [NeZero n] (hn : 2 ≤ n) (L : List (Fin n × Fin n)) (p w : Cfg n)
    (hL : ∀ ab ∈ L, ip (p ab.2 - p ab.1) (w ab.2 - w ab.1) = 0)
    (h01 : p ⟨0, by omega⟩ ≠ p ⟨1, by omega⟩)
    (hpin : barMem L ⟨0, by omega⟩ ⟨1, by omega⟩ = true)
    (order : List (Fin n × Fin n × Fin n))
    (hok : henOK L [⟨0, by omega⟩, ⟨1, by omega⟩] order = true)
    (hcov : coverOK order = true)
    (hdet : ∀ s ∈ order, (p s.1 - p s.2.1).1 * (p s.1 - p s.2.2).2 - (p s.1 - p s.2.1).2 * (p s.1 - p s.2.2).1 ≠ 0) :
    ∃ (t : ℝ × ℝ) (ω : ℝ), ∀ k, w k = t + ω • J (p k) := by
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  have hb := bar_flip (bar_of_mem hL hpin)
  obtain ⟨t, ω, h0, h1⟩ := pin_bar h01 hb
  set w' : Cfg n := fun k => w k - (t + ω • J (p k)) with hw'
  have hL' : ∀ ab ∈ L, ip (p ab.2 - p ab.1) (w' ab.2 - w' ab.1) = 0 := fun ab h => bar_sub_rigid (hL ab h)
  have hdone : ∀ x ∈ [i0, i1], w' x = 0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp only [hw', h0, sub_self]
    · simp only [hw', h1, sub_self]
  have hz := zero_along L p w' hL' order [i0, i1] hok hdet hdone
  refine ⟨t, ω, fun k => ?_⟩
  have hk : w' k = 0 := by
    unfold coverOK at hcov
    simp only [List.all_eq_true, List.mem_finRange, Bool.or_eq_true, decide_eq_true_eq,
      List.contains_iff_mem, true_implies] at hcov
    rcases hcov k with (h | h) | h
    · have : k = i0 := Fin.ext h
      subst this; exact hdone _ (by simp)
    · have : k = i1 := Fin.ext h
      subst this; exact hdone _ (by simp)
    · exact hz k h
  simpa [hw', sub_eq_zero] using hk

/-! ## The determinants, from the vertex enclosures -/

/-- The Henneberg determinant as an interval. -/
def henDetFI (vd : List (FI × FI)) (s : ℕ × ℕ × ℕ) : Option FI :=
  match vd[s.1]?, vd[s.2.1]?, vd[s.2.2]? with
  | some K, some I, some J =>
    some (sub (mul (sub K.1 I.1) (sub K.2 J.2)) (mul (sub K.2 I.2) (sub K.1 J.1)))
  | _, _, _ => none

/-- Every step's determinant is enclosed away from zero. -/
def detOK (vd : List (FI × FI)) (order : List (ℕ × ℕ × ℕ)) : Bool :=
  order.all fun s => match henDetFI vd s with
    | some D => decide (0 < D.lo) || decide (D.hi < 0)
    | none => false

theorem det_ne_of_detOK {q : Cfg n} {vd : List (FI × FI)} (he : Encl q vd)
    (order : List (Fin n × Fin n × Fin n))
    (h : detOK vd (order.map fun s => (s.1.val, s.2.1.val, s.2.2.val)) = true) :
    ∀ s ∈ order, (q s.1 - q s.2.1).1 * (q s.1 - q s.2.2).2 - (q s.1 - q s.2.1).2 * (q s.1 - q s.2.2).1 ≠ 0 := by
  obtain ⟨hlen, hq⟩ := he
  intro s hs
  unfold detOK at h
  simp only [List.all_eq_true, List.mem_map] at h
  have := h _ ⟨s, hs, rfl⟩
  unfold henDetFI at this
  simp only at this
  rw [List.getElem?_eq_getElem (by rw [hlen]; exact s.1.isLt),
      List.getElem?_eq_getElem (by rw [hlen]; exact s.2.1.isLt),
      List.getElem?_eq_getElem (by rw [hlen]; exact s.2.2.isLt)] at this
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  have hm : FI.mem ((q s.1 - q s.2.1).1 * (q s.1 - q s.2.2).2 - (q s.1 - q s.2.1).2 * (q s.1 - q s.2.2).1)
      (sub (mul (sub (vd[s.1.val]'(by rw [hlen]; exact s.1.isLt)).1 (vd[s.2.1.val]'(by rw [hlen]; exact s.2.1.isLt)).1)
                (sub (vd[s.1.val]'(by rw [hlen]; exact s.1.isLt)).2 (vd[s.2.2.val]'(by rw [hlen]; exact s.2.2.isLt)).2))
           (mul (sub (vd[s.1.val]'(by rw [hlen]; exact s.1.isLt)).2 (vd[s.2.1.val]'(by rw [hlen]; exact s.2.1.isLt)).2)
                (sub (vd[s.1.val]'(by rw [hlen]; exact s.1.isLt)).1 (vd[s.2.2.val]'(by rw [hlen]; exact s.2.2.isLt)).1))) := by
    have a := hq s.1; have b := hq s.2.1; have c := hq s.2.2
    simp only [Prod.fst_sub, Prod.snd_sub]
    exact mem_sub (mem_mul (mem_sub a.1 b.1) (mem_sub a.2 c.2)) (mem_mul (mem_sub a.2 b.2) (mem_sub a.1 c.1))
  rcases this with hpos | hneg
  · exact ne_of_gt (pos_of_mem hm hpos)
  · apply ne_of_lt
    refine lt_of_le_of_lt hm.2 ?_
    unfold val; exact div_neg_of_neg_of_pos (by exact_mod_cast hneg) two_pow_K_pos

end Chiquipoli.Family.Trig
