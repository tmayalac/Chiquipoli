/-
# Enclosing upstream's terms from a table of `(cos kz, sin kz)`

`enc tab t` evaluates a term `t : Tm` of the symbolic constructor in fixed-point
interval arithmetic, reading `sin (kz)`, `cos (kz)` from the table `tab`
(`tab[k] ∋ (cos kz, sin kz)`). It returns `none` if a division is not bounded
away from zero or an index is out of the table. `enc_sound`: whenever it
returns `some I`, the true value of `t` at `z` lies in `I`.

The only identities it uses are upstream's own: the quarter-turn shifts
`sin (i (2z − π/2)) = ± sin/cos (2iz)` (`Optigon.sin_quarter`,
`sin_quarter_succ`, `cos_quarter_succ`, proved in `Optigon.lean`), and
`(4i + c) z = (4i + c : ℕ) z`.
-/
import ChiquipoliFamily.Interval.Term
import ChiquipoliFamily.Interval.Base

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real FI

/-- `tab[k]`, or `none` past the end. -/
def look (tab : List (FI × FI)) (k : ℕ) : Option (FI × FI) := tab[k]?

/-- `rs r y` read from the table entry of `y`. -/
def encRS (r : ℕ) (cs : FI × FI) : FI :=
  match r with
  | 0 => cs.2
  | 1 => neg cs.1
  | 2 => neg cs.2
  | _ => cs.1

/-- `rc r y` read from the table entry of `y`. -/
def encRC (r : ℕ) (cs : FI × FI) : FI :=
  match r with
  | 0 => cs.1
  | 1 => cs.2
  | 2 => neg cs.1
  | _ => neg cs.2

/-- The interval evaluation of a term. -/
def enc (tab : List (FI × FI)) : Tm → Option FI
  | .zero => some (ofInt 0)
  | .one => some (ofInt 1)
  | .two => some (ofInt 2)
  | .sinZ => (look tab 1).map (·.2)
  | .cosZ => (look tab 1).map (·.1)
  | .sin2Z => (look tab 2).map (·.2)
  | .cos2Z => (look tab 2).map (·.1)
  | .sin3Z => (look tab 3).map (·.2)
  | .cos3Z => (look tab 3).map (·.1)
  | .sQ i => (look tab (2 * i)).map (encRS (i % 4))
  | .sQ1 i => (look tab (2 * (i + 1))).map (encRS ((i + 1) % 4))
  | .cQ1 i => (look tab (2 * (i + 1))).map (encRC ((i + 1) % 4))
  | .s41 i => (look tab (4 * i + 1)).map (·.2)
  | .s42 i => (look tab (4 * i + 2)).map (·.2)
  | .s43 i => (look tab (4 * i + 3)).map (·.2)
  | .c41 i => (look tab (4 * i + 1)).map (·.1)
  | .c42 i => (look tab (4 * i + 2)).map (·.1)
  | .c43 i => (look tab (4 * i + 3)).map (·.1)
  | .pm i => some (if i % 2 = 0 then ofInt 1 else ofInt (-1))
  | .neg a => (enc tab a).map neg
  | .sub a b => match enc tab a, enc tab b with
    | some x, some y => some (sub x y)
    | _, _ => none
  | .mul a b => match enc tab a, enc tab b with
    | some x, some y => some (mul x y)
    | _, _ => none
  | .div a b => match enc tab a, enc tab b with
    | some x, some y => div x y
    | _, _ => none

/-- The table encloses `(cos kz, sin kz)` at every index it has. -/
def TabValid (z : ℝ) (tab : List (FI × FI)) : Prop :=
  ∀ k (hk : k < tab.length), FI.mem (cos (k * z)) (tab[k]).1 ∧ FI.mem (sin (k * z)) (tab[k]).2

lemma look_sound {z : ℝ} {tab : List (FI × FI)} (hv : TabValid z tab) {k : ℕ} {cs : FI × FI}
    (h : look tab k = some cs) : FI.mem (cos (k * z)) cs.1 ∧ FI.mem (sin (k * z)) cs.2 := by
  unfold look at h
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨hk, hcs⟩ := h
  subst hcs
  exact hv k hk

lemma encRS_sound {r : ℕ} {y : ℝ} {cs : FI × FI} (h : FI.mem (cos y) cs.1 ∧ FI.mem (sin y) cs.2)
    (hr : r < 4) : FI.mem (Optigon.rs r y) (encRS r cs) := by
  interval_cases r
  · simpa [Optigon.rs, encRS] using h.2
  · simpa [Optigon.rs, encRS] using mem_neg h.1
  · simpa [Optigon.rs, encRS] using mem_neg h.2
  · simpa [Optigon.rs, encRS] using h.1

lemma encRC_sound {r : ℕ} {y : ℝ} {cs : FI × FI} (h : FI.mem (cos y) cs.1 ∧ FI.mem (sin y) cs.2)
    (hr : r < 4) : FI.mem (Optigon.rc r y) (encRC r cs) := by
  interval_cases r
  · simpa [Optigon.rc, encRC] using h.1
  · simpa [Optigon.rc, encRC] using h.2
  · simpa [Optigon.rc, encRC] using mem_neg h.1
  · simpa [Optigon.rc, encRC] using mem_neg h.2

/-- **Soundness of the interval evaluation.** -/
theorem enc_sound {z : ℝ} {tab : List (FI × FI)} (hv : TabValid z tab) :
    ∀ (t : Tm) (I : FI), enc tab t = some I → FI.mem (t.eval z) I := by
  intro t
  induction t with
  | zero => intro I h; cases h; simpa [Tm.eval] using mem_ofInt 0
  | one => intro I h; cases h; simpa [Tm.eval] using mem_ofInt 1
  | two => intro I h; cases h; simpa [Tm.eval] using mem_ofInt 2
  | sinZ =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    simpa [Tm.eval] using (look_sound hv hl).2
  | cosZ =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    simpa [Tm.eval] using (look_sound hv hl).1
  | sin2Z =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    simpa [Tm.eval] using (look_sound hv hl).2
  | cos2Z =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    simpa [Tm.eval] using (look_sound hv hl).1
  | sin3Z =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    simpa [Tm.eval] using (look_sound hv hl).2
  | cos3Z =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    simpa [Tm.eval] using (look_sound hv hl).1
  | sQ i =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    have hs := look_sound hv hl
    have e : ((2 * i : ℕ) : ℝ) * z = (i : ℝ) * (2 * z) := by push_cast; ring
    rw [e] at hs
    simp only [Tm.eval]
    rw [Optigon.sin_quarter]
    exact encRS_sound hs (Nat.mod_lt _ (by norm_num))
  | sQ1 i =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    have hs := look_sound hv hl
    have e : ((2 * (i + 1) : ℕ) : ℝ) * z = ((i : ℝ) + 1) * (2 * z) := by push_cast; ring
    rw [e] at hs
    simp only [Tm.eval]
    rw [Optigon.sin_quarter_succ]
    exact encRS_sound hs (Nat.mod_lt _ (by norm_num))
  | cQ1 i =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    have hs := look_sound hv hl
    have e : ((2 * (i + 1) : ℕ) : ℝ) * z = ((i : ℝ) + 1) * (2 * z) := by push_cast; ring
    rw [e] at hs
    simp only [Tm.eval]
    rw [Optigon.cos_quarter_succ]
    exact encRC_sound hs (Nat.mod_lt _ (by norm_num))
  | s41 i =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    have hs := (look_sound hv hl).2
    simp only [Tm.eval]; push_cast at hs; exact hs
  | s42 i =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    have hs := (look_sound hv hl).2
    simp only [Tm.eval]; push_cast at hs; exact hs
  | s43 i =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    have hs := (look_sound hv hl).2
    simp only [Tm.eval]; push_cast at hs; exact hs
  | c41 i =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    have hs := (look_sound hv hl).1
    simp only [Tm.eval]; push_cast at hs; exact hs
  | c42 i =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    have hs := (look_sound hv hl).1
    simp only [Tm.eval]; push_cast at hs; exact hs
  | c43 i =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨cs, hl, rfl⟩ := h
    have hs := (look_sound hv hl).1
    simp only [Tm.eval]; push_cast at hs; exact hs
  | pm i =>
    intro I h; simp only [enc, Option.some.injEq] at h
    subst h
    simp only [Tm.eval]
    rcases Nat.even_or_odd i with he | ho
    · rw [he.neg_one_pow, if_pos (Nat.even_iff.mp he)]; simpa using mem_ofInt 1
    · rw [ho.neg_one_pow, if_neg (by rw [Nat.odd_iff] at ho; omega)]; simpa using mem_ofInt (-1)
  | neg a ih =>
    intro I h; simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact mem_neg (ih x hx)
  | sub a b iha ihb =>
    intro I h
    simp only [enc] at h
    cases ha : enc tab a <;> cases hb : enc tab b <;> rw [ha, hb] at h <;> simp only [reduceCtorEq] at h
    rename_i x y
    cases h
    exact mem_sub (iha x ha) (ihb y hb)
  | mul a b iha ihb =>
    intro I h
    simp only [enc] at h
    cases ha : enc tab a <;> cases hb : enc tab b <;> rw [ha, hb] at h <;> simp only [reduceCtorEq] at h
    rename_i x y
    cases h
    exact mem_mul (iha x ha) (ihb y hb)
  | div a b iha ihb =>
    intro I h
    simp only [enc] at h
    cases ha : enc tab a <;> cases hb : enc tab b <;> rw [ha, hb] at h <;> simp only [reduceCtorEq] at h
    rename_i x y
    exact mem_div (iha x ha) (ihb y hb) h

end Chiquipoli.Family.Trig
