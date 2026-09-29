/-
# The `O(n²)` sign conditions, as kernel computations with one soundness theorem each

Given a list `vd` of vertex enclosures (`vd[k] ∋ p_k`), the kernel checks

* `sideOK vd i`: every vertex other than `p_i, p_{i+1}` lies strictly to the left
  of the directed side `p_i → p_{i+1}` (the support determinant is positive);
* `farRowOK n act vd i`: every pair `(i, j)`, `j > i`, is either declared active
  (`act i j`) or strictly shorter than `1`.

Both are Boolean functions over lists, evaluated by the kernel
(`decide +kernel`); `conv_sound` and `far_sound` turn a `true` into
`ConvexOrdered` and into the strict inequalities `dC i j < 0`. Side `i` is read
from the rotation `vd.drop i ++ vd.take i`, so a check never indexes a list at
random (`rot_getElem`).
-/
import ChiquipoliFamily.Trig.Interp
import ChiquipoliLean.Theory.Feasible

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real FI Chiquipoli.FirstOrder Chiquipoli.Feasible

/-! ## Interval versions of the two geometric quantities -/

/-- `cross a b c = (b − a)ₓ (c − a)ᵧ − (b − a)ᵧ (c − a)ₓ`, as an interval. -/
def crossFI (a b c : FI × FI) : FI :=
  sub (mul (sub b.1 a.1) (sub c.2 a.2)) (mul (sub b.2 a.2) (sub c.1 a.1))

/-- `|b − a|²`, as an interval. -/
def sqdFI (a b : FI × FI) : FI :=
  add (mul (sub b.1 a.1) (sub b.1 a.1)) (mul (sub b.2 a.2) (sub b.2 a.2))

/-- A point is enclosed by a pair of intervals. -/
def PMem (p : ℝ × ℝ) (P : FI × FI) : Prop := FI.mem p.1 P.1 ∧ FI.mem p.2 P.2

lemma cross_eq' (a b c : ℝ × ℝ) :
    cross a b c = (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) := by
  simp only [cross, ip, J, Prod.fst_sub, Prod.snd_sub]; ring

lemma mem_crossFI {a b c : ℝ × ℝ} {A B C : FI × FI} (ha : PMem a A) (hb : PMem b B) (hc : PMem c C) :
    FI.mem (cross a b c) (crossFI A B C) := by
  rw [cross_eq']
  exact mem_sub (mem_mul (mem_sub hb.1 ha.1) (mem_sub hc.2 ha.2))
    (mem_mul (mem_sub hb.2 ha.2) (mem_sub hc.1 ha.1))

lemma mem_sqdFI {a b : ℝ × ℝ} {A B : FI × FI} (ha : PMem a A) (hb : PMem b B) :
    FI.mem (nsq (b - a)) (sqdFI A B) := by
  have e : nsq (b - a) = (b.1 - a.1) * (b.1 - a.1) + (b.2 - a.2) * (b.2 - a.2) := by
    simp only [nsq, ip, Prod.fst_sub, Prod.snd_sub]
  rw [e]
  exact mem_add (mem_mul (mem_sub hb.1 ha.1) (mem_sub hb.1 ha.1))
    (mem_mul (mem_sub hb.2 ha.2) (mem_sub hb.2 ha.2))

lemma pos_of_mem {x : ℝ} {I : FI} (h : FI.mem x I) (hlo : 0 < I.lo) : 0 < x := by
  have : (0 : ℝ) < val I.lo := by unfold val; exact div_pos (by exact_mod_cast hlo) two_pow_K_pos
  exact lt_of_lt_of_le this h.1

lemma lt_one_of_mem {x : ℝ} {I : FI} (h : FI.mem x I) (hhi : I.hi < S) : x < 1 := by
  have : val I.hi < 1 := by
    unfold val; rw [div_lt_one two_pow_K_pos, ← S_cast]; exact_mod_cast hhi
  exact lt_of_le_of_lt h.2 this

/-! ## Rotated lists -/

lemma rot_getElem {α : Type*} (l : List α) (i t : ℕ) (hi : i < l.length) (ht : t < l.length) :
    (l.drop i ++ l.take i)[t]'(by simp; omega) = l[(i + t) % l.length]'(Nat.mod_lt _ (by omega)) := by
  by_cases h : t < l.length - i
  · rw [List.getElem_append_left (by simp; omega)]
    simp only [List.getElem_drop]
    congr 1
    rw [Nat.mod_eq_of_lt (by omega)]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_take, List.length_drop]
    congr 1
    have e : i + t = (t - (l.length - i)) + l.length := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ## Convexity -/

/-- Side `i`: every non-incident vertex strictly to the left. -/
def sideOK (vd : List (FI × FI)) (i : ℕ) : Bool :=
  match vd.drop i ++ vd.take i with
  | a :: b :: others => others.all fun c => decide (0 < (crossFI a b c).lo)
  | _ => false

/-- The vertices of `Q`, as a list of points. -/
def ptsOf {n : ℕ} (q : Cfg n) : List (ℝ × ℝ) := List.ofFn q

/-- Every vertex is enclosed by the corresponding entry of `vd`. -/
def Encl {n : ℕ} (q : Cfg n) (vd : List (FI × FI)) : Prop :=
  ∃ h : vd.length = n, ∀ k : Fin n, PMem (q k) (vd[k.val]'(by rw [h]; exact k.isLt))

lemma rot_getElem? {α : Type*} (l : List α) (i t : ℕ) (hi : i < l.length) (ht : t < l.length) :
    (l.drop i ++ l.take i)[t]? = some (l[(i + t) % l.length]'(Nat.mod_lt _ (by omega))) := by
  rw [List.getElem?_eq_getElem (by simp; omega), rot_getElem l i t hi ht]

/-- What `sideOK` says, in terms of `vd` itself. -/
lemma sideOK_spec (vd : List (FI × FI)) (i : ℕ) (hi : i < vd.length) (h3 : 3 ≤ vd.length)
    (h : sideOK vd i = true) (t : ℕ) (h2 : 2 ≤ t) (ht : t < vd.length) :
    0 < (crossFI (vd[i]'hi) (vd[(i + 1) % vd.length]'(Nat.mod_lt _ (by omega)))
      (vd[(i + t) % vd.length]'(Nat.mod_lt _ (by omega)))).lo := by
  have hr0 := rot_getElem? vd i 0 hi (by omega)
  have hr1 := rot_getElem? vd i 1 hi (by omega)
  have hrt := rot_getElem? vd i t hi ht
  simp only [Nat.add_zero, Nat.mod_eq_of_lt hi] at hr0
  unfold sideOK at h
  generalize vd.drop i ++ vd.take i = r at h hr0 hr1 hrt
  match r, h, hr0, hr1, hrt with
  | a :: b :: others, h, hr0, hr1, hrt =>
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr0
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hr1
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
    simp only [List.getElem?_cons_succ] at hrt
    rw [List.getElem?_eq_some_iff] at hrt
    obtain ⟨hlt, hc⟩ := hrt
    rw [← hr0, ← hr1, ← hc]
    exact h _ (List.getElem_mem _)

theorem conv_sound {n : ℕ} [NeZero n] (hn : 3 ≤ n) {q : Cfg n} {vd : List (FI × FI)}
    (he : Encl q vd) (hs : ∀ i < n, sideOK vd i = true) : ConvexOrdered q := by
  obtain ⟨hlen, hq⟩ := he
  subst hlen
  intro i j hji hji1
  have hi := i.isLt
  have hj := j.isLt
  set t := (j.val + vd.length - i.val) % vd.length with ht
  have htn : t < vd.length := Nat.mod_lt _ (by omega)
  have hjt : (i.val + t) % vd.length = j.val := by
    rw [ht, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have e : i.val + (j.val + vd.length - i.val) = j.val + vd.length := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  have ht2 : 2 ≤ t := by
    by_contra hlt
    push Not at hlt
    interval_cases t
    · apply hji; ext; rw [← hjt]; simp [Nat.mod_eq_of_lt hi]
    · apply hji1; ext; rw [← hjt]; simp [Fin.val_add]
  have hc := sideOK_spec vd i.val hi hn (hs i.val hi) t ht2 htn
  have e1 : (i.val + 1) % vd.length = (i + 1 : Fin vd.length).val := by simp [Fin.val_add]
  simp only [e1, hjt] at hc
  exact pos_of_mem (mem_crossFI (hq i) (hq (i + 1)) (hq j)) hc

/-! ## Inactive pairs -/

/-- Row `i`: every `j > i` (the list `rest` starts at `j`) is active or strictly shorter than `1`. -/
def farRow (act : ℕ → ℕ → Bool) (i : ℕ) (p : FI × FI) : ℕ → List (FI × FI) → Bool
  | _, [] => true
  | j, c :: rest => (act i j || decide ((sqdFI p c).hi < S)) && farRow act i p (j + 1) rest

/-- Row `i` of `vd`. -/
def farRowOK (act : ℕ → ℕ → Bool) (vd : List (FI × FI)) (i : ℕ) : Bool :=
  match vd.drop i with
  | p :: rest => farRow act i p (i + 1) rest
  | [] => true

lemma farRow_spec (act : ℕ → ℕ → Bool) (i : ℕ) (p : FI × FI) :
    ∀ (j : ℕ) (l : List (FI × FI)), farRow act i p j l = true →
      ∀ t (ht : t < l.length), act i (j + t) = true ∨ (sqdFI p (l[t])).hi < S
  | _, [], _, t, ht => by simp at ht
  | j, c :: rest, h, t, ht => by
    simp only [farRow, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases t with _ | t
    · simpa using h.1
    · have := farRow_spec act i p (j + 1) rest h.2 t (by simp at ht; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using this

theorem far_sound {n : ℕ} {q : Cfg n} {vd : List (FI × FI)} (act : ℕ → ℕ → Bool)
    (he : Encl q vd) (hs : ∀ i < n, farRowOK act vd i = true) :
    ∀ i j : Fin n, i < j → act i.val j.val = true ∨ dC i j q < 0 := by
  obtain ⟨hlen, hq⟩ := he
  subst hlen
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val < j.val := hij
  have hsi := hs i.val hi
  unfold farRowOK at hsi
  have hd : vd.drop i.val = vd[i.val] :: vd.drop (i.val + 1) := List.drop_eq_getElem_cons hi
  rw [hd] at hsi
  simp only at hsi
  have := farRow_spec act i.val (vd[i.val]) (i.val + 1) (vd.drop (i.val + 1)) hsi
    (j.val - (i.val + 1)) (by simp; omega)
  have e : i.val + 1 + (j.val - (i.val + 1)) = j.val := by omega
  rw [e] at this
  rcases this with h | h
  · exact Or.inl h
  · right
    simp only [List.getElem_drop, e] at h
    have hm := mem_sqdFI (hq i) (hq j)
    have := lt_one_of_mem hm h
    unfold dC; linarith

/-! ## The vertex enclosures themselves -/

/-- Enclose both coordinates of a symbolic point. -/
def encPair (tab : List (FI × FI)) (p : Tm × Tm) : Option (FI × FI) :=
  match enc tab p.1, enc tab p.2 with
  | some a, some b => some (a, b)
  | _, _ => none

/-- Entry `k` of `vd` contains the interval evaluation of upstream's vertex `k`. -/
def vdEntryOK (n : ℕ) (tab : List (FI × FI)) (k : ℕ) (v : FI × FI) : Bool :=
  match encPair tab (vertexS n k) with
  | some e => e.1.subset v.1 && e.2.subset v.2
  | none => false

/-- Every entry of `vd` from index `k` on is checked. -/
def vdFrom (n : ℕ) (tab : List (FI × FI)) : ℕ → List (FI × FI) → Bool
  | _, [] => true
  | k, v :: rest => vdEntryOK n tab k v && vdFrom n tab (k + 1) rest

lemma vdFrom_spec (n : ℕ) (tab : List (FI × FI)) :
    ∀ (k : ℕ) (l : List (FI × FI)), vdFrom n tab k l = true →
      ∀ t (ht : t < l.length), vdEntryOK n tab (k + t) (l[t]) = true
  | _, [], _, t, ht => by simp at ht
  | k, v :: rest, h, t, ht => by
    simp only [vdFrom, Bool.and_eq_true] at h
    rcases t with _ | t
    · simpa using h.1
    · have := vdFrom_spec n tab (k + 1) rest h.2 t (by simp at ht; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using this

/-- The published polygon, as a configuration. -/
noncomputable def Qc (n : ℕ) (z : ℝ) : Cfg n := fun k => Optigon.vertex n z k

/-- **The checked enclosures enclose the published polygon.** -/
theorem encl_of_vd {n : ℕ} {z : ℝ} {tab vd : List (FI × FI)} (hv : TabValid z tab)
    (hlen : vd.length = n) (h : vdFrom n tab 0 vd = true) : Encl (Qc n z) vd := by
  refine ⟨hlen, fun k => ?_⟩
  have hk := vdFrom_spec n tab 0 vd h k.val (by rw [hlen]; exact k.isLt)
  simp only [Nat.zero_add] at hk
  unfold vdEntryOK at hk
  cases he : encPair tab (vertexS n k.val) with
  | none => rw [he] at hk; simp at hk
  | some e =>
    rw [he] at hk
    simp only [Bool.and_eq_true] at hk
    unfold encPair at he
    cases h1 : enc tab (vertexS n k.val).1 <;> cases h2 : enc tab (vertexS n k.val).2 <;>
      rw [h1, h2] at he <;> simp only [reduceCtorEq, Option.some.injEq] at he
    rename_i a b
    subst he
    have hq : Qc n z k = ((vertexS n k.val).1.eval z, (vertexS n k.val).2.eval z) := vertex_eval n z k.val
    rw [hq]
    exact ⟨mem_of_subset (enc_sound hv _ _ h1) hk.1, mem_of_subset (enc_sound hv _ _ h2) hk.2⟩

end Chiquipoli.Family.Trig
