/-
# Enclosures of `cos (k z)` and `sin (k z)`, computed by the kernel

For a dyadic point `z₀ = N / 2^K`:

1. `x = z₀ / 2^J` is tiny, and Mathlib's bounds `cos_bound`, `sin_bound`
   (`|cos x − (1 − x²/2)| ≤ |x|⁴ · 5/96`, `|sin x − (x − x³/6)| ≤ |x|⁵/100`) enclose
   `cos x`, `sin x` to about `|x|⁴`;
2. `J` doublings (`cos 2y = 2cos²y − 1`, `sin 2y = 2 sin y cos y`) give
   `cos z₀`, `sin z₀`;
3. for every `z` within `r` of `z₀`, `|cos z − cos z₀| ≤ |z − z₀|` widens them to
   the whole interval;
4. the rotation `(cos (k+1)z, sin (k+1)z) = (cos kz cos z − sin kz sin z, …)`
   gives every multiple. Its interval error grows only like `(1 + |sin z|)^k`,
   unlike the Chebyshev recurrence `2c·T_k − T_{k−1}`, whose width grows like
   `(1 + √2)^k` and is useless beyond a few dozen steps.

The table of step 4 is supplied as data and CHECKED entry by entry (`tabOK`), so
the kernel never re-evaluates a long recurrence: each entry need only contain
the rotation of the previous one.
-/
import ChiquipoliFamily.Trig.FI

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real FI

/-! ## Step 1–2: a point -/

/-- `(C, S)` with `C ∋ cos x`, `S ∋ sin x` for the tiny `x` enclosed by `Y`:
the Taylor polynomials, widened by an upper bound for `|x|⁴`. -/
def taylorCS (Y : FI) : FI × FI :=
  let y2 := mul Y Y
  let y4 := mul y2 y2
  let r := y4.hi
  let one := ofInt 1
  let half := (⟨S / 2, S / 2⟩ : FI)           -- exactly 1/2
  let sixth := (⟨S / 6, -((-S) / 6)⟩ : FI)     -- contains 1/6
  ((sub one (mul half y2)).widen r, (sub Y (mul sixth (mul y2 Y))).widen r)

/-- One doubling: `(cos 2y, sin 2y)` from `(cos y, sin y)`. -/
def dbl (cs : FI × FI) : FI × FI :=
  let two := ofInt 2
  (sub (mul two (mul cs.1 cs.1)) (ofInt 1), mul two (mul cs.2 cs.1))

def dblN : ℕ → FI × FI → FI × FI
  | 0, cs => cs
  | j + 1, cs => dblN j (dbl cs)

/-- `x` enclosed as `[⌊N/2^J⌋, ⌈N/2^J⌉]`. -/
def halfFI (N : ℤ) (J : ℕ) : FI := ⟨N / 2 ^ J, -((-N) / 2 ^ J)⟩

/-- `(cos z₀, sin z₀)` at `z₀ = N / 2^K`. -/
def pointCS (N : ℤ) (J : ℕ) : FI × FI := dblN J (taylorCS (halfFI N J))

lemma mem_half : FI.mem (1 / 2 : ℝ) (⟨S / 2, S / 2⟩ : FI) := by
  have hK : K = (K - 1) + 1 := by unfold K; rfl
  have h2 : S / 2 = 2 ^ (K - 1) := by
    unfold S; rw [hK, pow_succ, Int.mul_ediv_cancel _ (by norm_num)]; rfl
  unfold FI.mem val
  rw [h2]; push_cast
  have : (2 : ℝ) ^ (K - 1) / (2 : ℝ) ^ K = 1 / 2 := by
    conv_rhs => rw [show (1 : ℝ) / 2 = (2 : ℝ) ^ (K - 1) / ((2 : ℝ) ^ (K - 1) * 2) by field_simp]
    rw [← pow_succ, ← hK]
  rw [this]; exact ⟨le_rfl, le_rfl⟩

lemma mem_sixth : FI.mem (1 / 6 : ℝ) (⟨S / 6, -((-S) / 6)⟩ : FI) := by
  unfold FI.mem val
  have hK := two_pow_K_pos
  constructor
  · have := floor_div_le S 6 (by norm_num)
    rw [S_cast] at this
    rw [div_le_iff₀ hK]
    push_cast at this ⊢
    nlinarith [this]
  · have := le_ceil_div S 6 (by norm_num)
    rw [S_cast] at this
    rw [le_div_iff₀ hK]
    push_cast at this ⊢
    nlinarith [this]

lemma mem_halfFI (N : ℤ) (J : ℕ) :
    FI.mem ((N : ℝ) / (2 : ℝ) ^ K / (2 : ℝ) ^ J) (halfFI N J) := by
  have hJ : (0 : ℤ) < 2 ^ J := by positivity
  unfold FI.mem val halfFI
  have hK := two_pow_K_pos
  have hJr : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
  constructor
  · have := floor_div_le N (2 ^ J) hJ
    push_cast at this
    calc ((N / 2 ^ J : ℤ) : ℝ) / (2 : ℝ) ^ K ≤ ((N : ℝ) / (2 : ℝ) ^ J) / (2 : ℝ) ^ K :=
          div_le_div_of_nonneg_right this hK.le
      _ = (N : ℝ) / (2 : ℝ) ^ K / (2 : ℝ) ^ J := by ring
  · have := le_ceil_div N (2 ^ J) hJ
    push_cast at this ⊢
    calc (N : ℝ) / (2 : ℝ) ^ K / (2 : ℝ) ^ J = ((N : ℝ) / (2 : ℝ) ^ J) / (2 : ℝ) ^ K := by ring
      _ ≤ _ := div_le_div_of_nonneg_right this hK.le

/-- The Taylor step is sound as long as the enclosed point is at most `1`. -/
lemma mem_taylorCS {x : ℝ} {Y : FI} (hx : FI.mem x Y) (h1 : |x| ≤ 1) :
    FI.mem (cos x) (taylorCS Y).1 ∧ FI.mem (sin x) (taylorCS Y).2 := by
  have hy2 := mem_mul hx hx
  have hy4 := mem_mul hy2 hy2
  have hx4 : x ^ 4 ≤ val (mul (mul Y Y) (mul Y Y)).hi := by
    have := hy4.2; nlinarith [this]
  have habs4 : |x| ^ 4 = x ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  have hxle : |x| ^ 5 ≤ |x| ^ 4 := by
    have := abs_nonneg x
    calc |x| ^ 5 = |x| ^ 4 * |x| := by ring
      _ ≤ |x| ^ 4 * 1 := by gcongr
      _ = |x| ^ 4 := by ring
  constructor
  · apply mem_widen (x := 1 - (1 / 2) * (x * x))
    · have h1 : FI.mem (1 : ℝ) (ofInt 1) := by simpa using mem_ofInt 1
      exact mem_sub h1 (mem_mul mem_half hy2)
    · have hb := Real.cos_bound h1
      have e : 1 - (1 / 2) * (x * x) = 1 - x ^ 2 / 2 := by ring
      rw [e]
      calc |cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 * (5 / 96) := hb
        _ ≤ |x| ^ 4 := by nlinarith [pow_nonneg (abs_nonneg x) 4]
        _ ≤ _ := by rw [habs4]; exact hx4
  · apply mem_widen (x := x - (1 / 6) * ((x * x) * x))
    · exact mem_sub hx (mem_mul mem_sixth (mem_mul hy2 hx))
    · have hb := Real.sin_bound h1
      have e : x - (1 / 6) * ((x * x) * x) = x - x ^ 3 / 6 := by ring
      rw [e]
      calc |sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 100 := hb
        _ ≤ |x| ^ 4 := by nlinarith [hxle, pow_nonneg (abs_nonneg x) 5]
        _ ≤ _ := by rw [habs4]; exact hx4

lemma mem_dbl {y : ℝ} {cs : FI × FI} (h : FI.mem (cos y) cs.1 ∧ FI.mem (sin y) cs.2) :
    FI.mem (cos (2 * y)) (dbl cs).1 ∧ FI.mem (sin (2 * y)) (dbl cs).2 := by
  have h2 : FI.mem (2 : ℝ) (ofInt 2) := by simpa using mem_ofInt 2
  have h1 : FI.mem (1 : ℝ) (ofInt 1) := by simpa using mem_ofInt 1
  constructor
  · rw [cos_two_mul]
    have := mem_sub (mem_mul h2 (mem_mul h.1 h.1)) h1
    simpa [dbl, sq, mul_assoc] using this
  · rw [sin_two_mul]
    have := mem_mul h2 (mem_mul h.2 h.1)
    simpa [dbl, mul_assoc] using this

lemma mem_dblN (J : ℕ) {y : ℝ} {cs : FI × FI} (h : FI.mem (cos y) cs.1 ∧ FI.mem (sin y) cs.2) :
    FI.mem (cos (2 ^ J * y)) (dblN J cs).1 ∧ FI.mem (sin (2 ^ J * y)) (dblN J cs).2 := by
  induction J generalizing y cs with
  | zero => simpa [dblN] using h
  | succ j ih =>
    simp only [dblN]
    have := ih (y := 2 * y) (cs := dbl cs) (mem_dbl h)
    have e : (2 : ℝ) ^ j * (2 * y) = 2 ^ (j + 1) * y := by ring
    rwa [e] at this

/-- **The point enclosure.** For `z₀ = N / 2^K` with `|z₀| ≤ 2^J`. -/
theorem mem_pointCS (N : ℤ) (J : ℕ) (hN : |(N : ℝ) / (2 : ℝ) ^ K| ≤ (2 : ℝ) ^ J) :
    FI.mem (cos ((N : ℝ) / (2 : ℝ) ^ K)) (pointCS N J).1 ∧
      FI.mem (sin ((N : ℝ) / (2 : ℝ) ^ K)) (pointCS N J).2 := by
  have hJ : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
  have hx := mem_halfFI N J
  have h1 : |(N : ℝ) / (2 : ℝ) ^ K / (2 : ℝ) ^ J| ≤ 1 := by
    rw [abs_div, abs_of_pos hJ, div_le_one hJ]; exact hN
  have := mem_dblN J (mem_taylorCS hx h1)
  have e : (2 : ℝ) ^ J * ((N : ℝ) / (2 : ℝ) ^ K / (2 : ℝ) ^ J) = (N : ℝ) / (2 : ℝ) ^ K := by
    field_simp
  rwa [e] at this

/-! ## Step 3: an interval of parameters -/

/-- `cos z`, `sin z` for every `z` within `r / 2^K` of `z₀`. -/
theorem mem_interval_CS {z : ℝ} (N : ℤ) (J : ℕ) (r : ℤ)
    (hN : |(N : ℝ) / (2 : ℝ) ^ K| ≤ (2 : ℝ) ^ J) (hz : |z - (N : ℝ) / (2 : ℝ) ^ K| ≤ val r) :
    FI.mem (cos z) ((pointCS N J).1.widen r) ∧ FI.mem (sin z) ((pointCS N J).2.widen r) := by
  obtain ⟨hc, hs⟩ := mem_pointCS N J hN
  exact ⟨mem_widen hc ((Real.abs_cos_sub_cos_le _ _).trans hz),
         mem_widen hs ((Real.abs_sin_sub_sin_le _ _).trans hz)⟩

/-! ## Step 4: every multiple, by rotation -/

/-- `(cos (k+1)z, sin (k+1)z)` from `(cos kz, sin kz)` and `(cos z, sin z) ∈ (C, S)`. -/
def rotStep (C S : FI) (cs : FI × FI) : FI × FI :=
  (sub (mul cs.1 C) (mul cs.2 S), add (mul cs.2 C) (mul cs.1 S))

/-- The table is consistent: each entry contains the rotation of the previous one. -/
def tabOK (C S : FI) : List (FI × FI) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    ((rotStep C S a).1.subset b.1 && (rotStep C S a).2.subset b.2) && tabOK C S (b :: rest)

/-- The first entry contains `(cos 0, sin 0) = (1, 0)`. -/
def tabHead : List (FI × FI) → Bool
  | [] => false
  | a :: _ => (ofInt 1).subset a.1 && (ofInt 0).subset a.2

lemma mem_rotStep {z y : ℝ} {C S : FI} {cs : FI × FI} (hC : FI.mem (cos z) C) (hS : FI.mem (sin z) S)
    (h : FI.mem (cos y) cs.1 ∧ FI.mem (sin y) cs.2) :
    FI.mem (cos (y + z)) (rotStep C S cs).1 ∧ FI.mem (sin (y + z)) (rotStep C S cs).2 := by
  rw [cos_add, sin_add]
  exact ⟨mem_sub (mem_mul h.1 hC) (mem_mul h.2 hS), mem_add (mem_mul h.2 hC) (mem_mul h.1 hS)⟩

/-- Soundness of a checked table, from any starting multiple `k₀`. -/
lemma tab_sound_aux {z : ℝ} {C S : FI} (hC : FI.mem (cos z) C) (hS : FI.mem (sin z) S) :
    ∀ (l : List (FI × FI)) (k₀ : ℕ), tabOK C S l = true → ∀ (a : FI × FI), l.head? = some a →
      (FI.mem (cos (k₀ * z)) a.1 ∧ FI.mem (sin (k₀ * z)) a.2) →
      ∀ t (ht : t < l.length), FI.mem (cos ((k₀ + t : ℕ) * z)) (l[t]).1 ∧
        FI.mem (sin ((k₀ + t : ℕ) * z)) (l[t]).2
  | [], k₀, _, a, ha, _ => by simp at ha
  | [b], k₀, _, a, ha, h0 => by
    intro t ht
    simp only [List.length_singleton, Nat.lt_one_iff] at ht
    subst ht
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    simpa using h0
  | b :: c :: rest, k₀, hok, a, ha, h0 => by
    intro t ht
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    simp only [tabOK, Bool.and_eq_true] at hok
    obtain ⟨⟨h1, h2⟩, hrest⟩ := hok
    rcases t with _ | t
    · simpa using h0
    · have hc : FI.mem (cos ((k₀ + 1 : ℕ) * z)) c.1 ∧ FI.mem (sin ((k₀ + 1 : ℕ) * z)) c.2 := by
        have := mem_rotStep hC hS h0
        have e : (k₀ : ℝ) * z + z = ((k₀ + 1 : ℕ) : ℝ) * z := by push_cast; ring
        rw [e] at this
        exact ⟨mem_of_subset this.1 h1, mem_of_subset this.2 h2⟩
      have := tab_sound_aux hC hS (c :: rest) (k₀ + 1) hrest c rfl hc t
        (by simp only [List.length_cons] at ht ⊢; omega)
      have e : k₀ + 1 + t = k₀ + (t + 1) := by omega
      rw [e] at this
      simpa using this

/-- **A checked table encloses every multiple.** -/
theorem tab_sound {z : ℝ} {C S : FI} (hC : FI.mem (cos z) C) (hS : FI.mem (sin z) S)
    (tab : List (FI × FI)) (hh : tabHead tab = true) (hok : tabOK C S tab = true) :
    ∀ k (hk : k < tab.length), FI.mem (cos (k * z)) (tab[k]).1 ∧ FI.mem (sin (k * z)) (tab[k]).2 := by
  intro k hk
  cases tab with
  | nil => simp at hk
  | cons a rest =>
    simp only [tabHead, Bool.and_eq_true] at hh
    have h0 : FI.mem (cos ((0 : ℕ) * z)) a.1 ∧ FI.mem (sin ((0 : ℕ) * z)) a.2 := by
      simp only [Nat.cast_zero, zero_mul, cos_zero, sin_zero]
      exact ⟨mem_of_subset (by simpa using mem_ofInt 1) hh.1, mem_of_subset (by simpa using mem_ofInt 0) hh.2⟩
    have := tab_sound_aux hC hS (a :: rest) 0 hok a rfl h0 k hk
    simpa using this

end Chiquipoli.Family.Trig
