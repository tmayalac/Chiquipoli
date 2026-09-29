/-
# From the kernel checks to the published polygon, once for every `n = 16k`

`published_of_checks` is the whole argument, proved once. Its hypotheses are
Boolean checks on finite data (tables of `(cos kz, sin kz)` enclosures, vertex
enclosures, the active graph, shape witnesses, a Henneberg order and a
self-stress certificate) that the kernel evaluates per `n` by `decide +kernel`;
its conclusion is the statement of `A<n>/Published.lean`: upstream's `F` has
exactly one zero in upstream's bracket, and the polygon upstream builds there is
a strict local maximiser of the perimeter, modulo Euclidean motions.

Nothing here trusts the data: a wrong table, enclosure, graph, witness or stress
makes a check return `false`, and the proof does not go through.

* **Exact identities** (`Shp`): every side and every active diameter of the
  published polygon is one of the symbolic shapes of `Shapes.lean`/`FSide.lean`,
  possibly mirrored (`tM`) or reversed. The kernel compares the symbolic vertices
  `vertexS n k` (upstream's code, run symbolically) with the witness; the length
  identities are then theorems, not numerics.
* **Inequalities** (`conv_sound`, `far_sound`): from the interval enclosures.
* **Root**: existence by sign change (`root_exists`), uniqueness on an interval
  containing upstream's bracket by `Fd < 0` (`root_unique`).
* **Rigidity** (`rigid_of_henneberg`) and **multipliers** (`bal_zero`,
  `stress_encl`) feed `Feasible.thm_3_5`.
-/
import ChiquipoliFamily.Trig.Stress
import ChiquipoliFamily.Trig.Root

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real Tm FI Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family

/-! ## Shapes: the exact identities, by witness -/

/-- The symbolic shapes whose squared length `Shapes.lean` / `FSide.lean` compute:
active diameters (length `1`), sides (length `2 sin(z/2)`), and the two closing
sides (squared length `F + (2 sin(z/2))²`). -/
inductive Shp where
  | fqr (i : ℕ) | fqu (i : ℕ) | fqt (i : ℕ) | f0qr | f0qu | f0qt | otop | cut (i : ℕ) | c0ut
  | sur (i : ℕ) | srt (i : ℕ) | s0ur | s0rt | s0top | sqt (i : ℕ) | suq (i : ℕ) | s0qt | s0uq
  | clo (k : ℕ) | clo' (k : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- The two symbolic endpoints `(X, Y)`; the identity is about `nsq (X − Y)`. -/
def Shp.pts : Shp → (Tm × Tm) × (Tm × Tm)
  | fqr i => (tr i, tq i)
  | fqu i => (tu i, tq i)
  | fqt i => (tt i, tq i)
  | f0qr => (tr0, tq0)
  | f0qu => (tu0, tq0)
  | f0qt => (tOrigin, tq0)
  | otop => (tTop, tOrigin)
  | cut i => (tt (i + 1), tu i)
  | c0ut => (tt 1, tu0)
  | sur i => (tr i, tu i)
  | srt i => (tt i, tr i)
  | s0ur => (tr0, tu0)
  | s0rt => (tOrigin, tr0)
  | s0top => (tTop, tq0)
  | sqt i => (tt (i + 1), tq i)
  | suq i => (tq (i + 1), tu i)
  | s0qt => (tt 1, tq0)
  | s0uq => (tq 1, tu0)
  | clo k => (tu (2 * k - 1), tM (tq (2 * k - 1)))
  | clo' k => (tq (2 * k - 1), tM (tu (2 * k - 1)))

/-- `0`: a diameter; `1`: a side; `2`: a closing side. -/
def Shp.kind : Shp → ℕ
  | fqr _ | fqu _ | fqt _ | f0qr | f0qu | f0qt | otop | cut _ | c0ut => 0
  | sur _ | srt _ | s0ur | s0rt | s0top | sqt _ | suq _ | s0qt | s0uq => 1
  | clo _ | clo' _ => 2

/-- The closing index (`k` with `n = 16k`); `0` for the other shapes. -/
def Shp.ck : Shp → ℕ
  | clo k | clo' k => k
  | _ => 0

/-- The squared length the identities give. -/
noncomputable def Shp.val (z : ℝ) (s : Shp) : ℝ :=
  match s.kind with
  | 0 => 1
  | 1 => (2 * sin (z / 2)) ^ 2
  | _ => Optigon.F (8 * (2 * s.ck)) z + (2 * sin (z / 2)) ^ 2

theorem Shp.nsq_pts (z : ℝ) (hc : cos (2 * z) ≠ 0) (s : Shp) (hk : s.kind = 2 → 1 ≤ s.ck) :
    nsq (ev z s.pts.1 - ev z s.pts.2) = s.val z := by
  cases s <;> simp only [Shp.pts, Shp.val, Shp.kind, Shp.ck] at hk ⊢
  · exact fan_qr z _
  · exact fan_qu z _
  · exact fan_qt z _
  · exact fan0_qr z
  · exact fan0_qu z
  · exact fan0_qt z
  · exact origin_top z
  · exact cross_ut z _ hc
  · exact cross0_ut z hc
  · exact side_ur z _
  · exact side_rt z _
  · exact side0_ur z
  · exact side0_rt z
  · exact side0_top z
  · exact side_qt z _ hc
  · exact side_uq z _ hc
  · exact side0_qt z hc
  · exact side0_uq z hc
  · exact closing z _ (hk trivial)
  · exact closing' z _ (hk trivial)

/-- `neg zero` is `zero`: the only normalisation needed, for the vertices upstream
does not mirror (`0` and `n/2`). -/
def nz : Tm → Tm
  | Tm.neg Tm.zero => Tm.zero
  | t => t

lemma eval_nz (z : ℝ) (t : Tm) : (nz t).eval z = t.eval z := by
  unfold nz; split <;> simp [Tm.eval]

def nzP (p : Tm × Tm) : Tm × Tm := (nz p.1, nz p.2)

lemma ev_nzP (z : ℝ) (p : Tm × Tm) : ev z (nzP p) = ev z p := by
  simp [ev, nzP, eval_nz]

/-- A witness: a shape, possibly mirrored, possibly reversed. -/
structure W where
  s : Shp
  mir : Bool
  flip : Bool
  deriving DecidableEq, Repr, Inhabited

def W.pts (w : W) : (Tm × Tm) × (Tm × Tm) :=
  let XY := w.s.pts
  let XY := if w.mir then (tM XY.1, tM XY.2) else XY
  if w.flip then (XY.2, XY.1) else XY

theorem W.nsq_pts (z : ℝ) (hc : cos (2 * z) ≠ 0) (w : W) (hk : w.s.kind = 2 → 1 ≤ w.s.ck) :
    nsq (ev z w.pts.1 - ev z w.pts.2) = w.s.val z := by
  have h := Shp.nsq_pts z hc w.s hk
  unfold W.pts
  cases w.mir <;> cases w.flip <;> simp only [if_true, if_false, Bool.false_eq_true]
  · exact h
  · rw [nsq_comm]; exact h
  · rw [nsq_mirror]; exact h
  · rw [nsq_comm, nsq_mirror]; exact h

/-- The witness matches the two symbolic vertices `x`, `y` (`nsq (x − y)`). -/
def W.fits (w : W) (x y : Tm × Tm) : Bool :=
  decide (nzP x = nzP w.pts.1) && decide (nzP y = nzP w.pts.2)

lemma W.nsq_of_fits {z : ℝ} (hc : cos (2 * z) ≠ 0) {w : W} (hk : w.s.kind = 2 → 1 ≤ w.s.ck)
    {x y : Tm × Tm} (h : w.fits x y = true) : nsq (ev z x - ev z y) = w.s.val z := by
  unfold W.fits at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← ev_nzP z x, ← ev_nzP z y, h.1, h.2, ev_nzP, ev_nzP]
  exact W.nsq_pts z hc w hk

/-! ## The root, and upstream's bracket -/

lemma val_le_val {a b : ℤ} (h : a ≤ b) : val a ≤ val b := by
  unfold val; exact div_le_div_of_nonneg_right (by exact_mod_cast h) two_pow_K_pos.le

lemma val_lt_val {a b : ℤ} (h : a < b) : val a < val b := by
  unfold val; exact div_lt_div_of_pos_right (by exact_mod_cast h) two_pow_K_pos

lemma val_sub' (a b : ℤ) : val (a - b) = val a - val b := by unfold val; push_cast; ring
lemma val_add' (a b : ℤ) : val (a + b) = val a + val b := by unfold val; push_cast; ring
lemma val_zero' : val 0 = 0 := by unfold val; simp

lemma val_two_mul (a : ℤ) : val (2 * a) = 2 * val a := by unfold val; push_cast; ring

/-- A point in `[0, 1]`: `pointCS` applies. -/
lemma abs_val_le_one {N : ℤ} (h0 : 0 ≤ N) (h1 : N ≤ S) (J : ℕ) :
    |(N : ℝ) / (2 : ℝ) ^ K| ≤ (2 : ℝ) ^ J := by
  have hK := two_pow_K_pos
  have a : (0 : ℝ) ≤ (N : ℝ) / (2 : ℝ) ^ K := div_nonneg (by exact_mod_cast h0) hK.le
  have b : (N : ℝ) / (2 : ℝ) ^ K ≤ 1 := by
    rw [div_le_one hK, ← S_cast]; exact_mod_cast h1
  rw [abs_of_nonneg a]
  exact b.trans (one_le_pow₀ (by norm_num))

/-- The point enclosure at `val N`. -/
lemma mem_point {N : ℤ} (h0 : 0 ≤ N) (h1 : N ≤ S) (J : ℕ) :
    FI.mem (cos (val N)) (pointCS N J).1 ∧ FI.mem (sin (val N)) (pointCS N J).2 :=
  mem_pointCS N J (abs_val_le_one h0 h1 J)

/-- A checked table is valid wherever `|z − val N| ≤ val r`. -/
theorem tab_valid {N r : ℤ} (h0 : 0 ≤ N) (h1 : N ≤ S) (J : ℕ) {tab : List (FI × FI)}
    (hh : tabHead tab = true) (hok : tabOK ((pointCS N J).1.widen r) ((pointCS N J).2.widen r) tab = true)
    {z : ℝ} (hz : |z - val N| ≤ val r) : TabValid z tab := by
  have h := mem_interval_CS N J r (abs_val_le_one h0 h1 J) hz
  exact tab_sound h.1 h.2 tab hh hok

/-- `val N ≤ c / n` from an integer inequality (`c = C / 10^20`). -/
lemma val_le_div {N C : ℤ} {n : ℕ} (hn : 0 < n) (h : N * n * 10 ^ 20 ≤ C * S) :
    val N ≤ ((C : ℝ) / 10 ^ 20) / n := by
  have hK := two_pow_K_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold val
  rw [div_le_div_iff₀ hK (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : ((N * n * 10 ^ 20 : ℤ) : ℝ) ≤ ((C * S : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at this; rw [S_cast] at this; linarith

lemma div_le_val {N C : ℤ} {n : ℕ} (hn : 0 < n) (h : C * S ≤ N * n * 10 ^ 20) :
    ((C : ℝ) / 10 ^ 20) / n ≤ val N := by
  have hK := two_pow_K_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold val
  rw [div_le_div_iff₀ (by positivity) hK, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : ((C * S : ℤ) : ℝ) ≤ ((N * n * 10 ^ 20 : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at this; rw [S_cast] at this; linarith

/-- The enclosure of `π / n` from Mathlib's twenty digits of `π`. -/
lemma pi_div_mem {n : ℕ} (hn : 0 < n) {Np rp : ℤ}
    (hlo : (Np - rp) * n * 10 ^ 20 ≤ 314159265358979323846 * S)
    (hhi : 314159265358979323847 * S ≤ (Np + rp) * n * 10 ^ 20) :
    |π / n - val Np| ≤ val rp := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have p1 := Real.pi_gt_d20
  have p2 := Real.pi_lt_d20
  have a := val_le_div hn hlo
  have b := div_le_val hn hhi
  rw [val_sub'] at a; rw [val_add'] at b
  have e1 : ((314159265358979323846 : ℤ) : ℝ) / 10 ^ 20 = (3.14159265358979323846 : ℝ) := by norm_num
  have e2 : ((314159265358979323847 : ℤ) : ℝ) / 10 ^ 20 = (3.14159265358979323847 : ℝ) := by norm_num
  rw [e1] at a; rw [e2] at b
  have c1 : (3.14159265358979323846 : ℝ) / n < π / n := div_lt_div_of_pos_right p1 hnr
  have c2 : π / n < (3.14159265358979323847 : ℝ) / n := div_lt_div_of_pos_right p2 hnr
  rw [abs_le]; constructor <;> linarith

/-- The integer side conditions of the root and bracket argument. -/
def bracketOK (n : ℕ) (N0 rr Np rp Nc rc Hlo Ha : ℤ) : Bool :=
  decide (0 < N0 - rr) && decide (0 < rr) && decide (4 * (N0 + rr) < 3 * S)
  && decide (0 < Nc - rc) && decide (0 ≤ rc) && decide (4 * (Nc + rc) < 3 * S)
  && decide (0 ≤ Np) && decide (Np ≤ S) && decide (0 ≤ rp)
  && decide (2 * Hlo = N0 - rr) && decide (2 * Ha = Nc - rc)
  && decide ((Np - rp) * n * 10 ^ 20 ≤ 314159265358979323846 * S)
  && decide (314159265358979323847 * S ≤ (Np + rp) * n * 10 ^ 20)
  && decide (N0 + rr < Np - rp) && decide (Np + rp ≤ Nc + rc)

/-- The interval comparisons of `sin` at the bracket ends. -/
def sinOK (J : ℕ) (Np rp Hlo Ha : ℤ) : Bool :=
  let SP := (pointCS Np J).2.widen rp
  decide (SP.hi < 2 * (pointCS Hlo J).2.lo) && decide (2 * (pointCS Ha J).2.hi ≤ SP.lo)

/-- The sign change and the monotonicity, from the tables. -/
def rootOK (k : ℕ) (tabLo tabHi tabU : List (FI × FI)) : Bool :=
  (match encF (2 * k) tabLo with | some I => decide (0 < I.lo) | none => false)
  && (match encF (2 * k) tabHi with | some I => decide (I.hi < 0) | none => false)
  && (match encFd (2 * k) tabU with | some I => decide (I.hi < 0) | none => false)

lemma lt_S_of {N : ℤ} (h : 4 * N < 3 * S) : N ≤ S := by have := S_pos; omega

lemma val_lt_pi_four {N : ℤ} (h : 4 * N < 3 * S) : val N < π / 4 := by
  have hK := two_pow_K_pos
  have : val N < 3 / 4 := by
    unfold val; rw [div_lt_iff₀ hK]
    have : ((4 * N : ℤ) : ℝ) < ((3 * S : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this; rw [S_cast] at this; linarith
  linarith [pi_gt_three]

lemma neg_of_hi {x : ℝ} {I : FI} (h : FI.mem x I) (hI : I.hi < 0) : x < 0 := by
  have : val I.hi < 0 := by unfold val; exact div_neg_of_neg_of_pos (by exact_mod_cast hI) two_pow_K_pos
  linarith [h.2]

/-- **The root.** Upstream's `F_n`, `n = 16k`, has a zero `z` within `val rr` of
`val N0`, and it is the only zero in upstream's bracket. -/
theorem root_facts (n k : ℕ) (hn : n = 16 * k) (hk : 1 ≤ k) (J : ℕ) (N0 rr Np rp Nc rc Hlo Ha : ℤ)
    (tabLo tabHi tabU : List (FI × FI))
    (hb : bracketOK n N0 rr Np rp Nc rc Hlo Ha = true) (hs : sinOK J Np rp Hlo Ha = true)
    (hLo : tabHead tabLo = true ∧ tabOK ((pointCS (N0 - rr) J).1.widen 0) ((pointCS (N0 - rr) J).2.widen 0) tabLo = true)
    (hHi : tabHead tabHi = true ∧ tabOK ((pointCS (N0 + rr) J).1.widen 0) ((pointCS (N0 + rr) J).2.widen 0) tabHi = true)
    (hU : tabHead tabU = true ∧ tabOK ((pointCS Nc J).1.widen rc) ((pointCS Nc J).2.widen rc) tabU = true)
    (hr : rootOK k tabLo tabHi tabU = true) :
    ∃ z : ℝ, z ∈ Set.Ioo (Optigon.lo n) (Optigon.hi n) ∧ Optigon.F n z = 0 ∧
      (∀ z' ∈ Set.Ioo (Optigon.lo n) (Optigon.hi n), Optigon.F n z' = 0 → z' = z) ∧
      |z - val N0| ≤ val rr ∧ 0 < z ∧ z < π / 4 := by
  unfold bracketOK at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, b12⟩, b13⟩, b14⟩, b15⟩ := hb
  unfold sinOK at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨s1, s2⟩ := hs
  unfold rootOK at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨r1, r2⟩, r3⟩ := hr
  have hn0 : 0 < n := by omega
  have hnm : n = 8 * (2 * k) := by omega
  have hK := two_pow_K_pos
  have hS := S_pos
  -- the bracket ends
  have hzlo : 0 < (val (N0 - rr)) := by have := val_lt_val b1; rwa [val_zero'] at this
  have hzhi : (val (N0 + rr)) < π / 4 := val_lt_pi_four b3
  have hlohi : (val (N0 - rr)) < (val (N0 + rr)) := val_lt_val (by omega)
  have ha0 : 0 < val (Nc - rc) := by have := val_lt_val b4; rwa [val_zero'] at this
  have hb4 : val (Nc + rc) < π / 4 := val_lt_pi_four b6
  -- sin (π / n)
  have hpi := pi_div_mem hn0 b12 b13
  have hSP := (mem_interval_CS Np J rp (abs_val_le_one b7 b8 J) hpi).2
  -- F at the two ends
  have tvLo : TabValid (val (N0 - rr)) tabLo := tab_valid (by omega) (by omega) J hLo.1 hLo.2 (by simp [val_zero'])
  have tvHi : TabValid (val (N0 + rr)) tabHi := tab_valid (by omega) (lt_S_of b3) J hHi.1 hHi.2 (by simp [val_zero'])
  have Flo : 0 < Optigon.F n (val (N0 - rr)) := by
    cases h : encF (2 * k) tabLo with
    | none => rw [h] at r1; cases r1
    | some I =>
      rw [h] at r1; simp only [decide_eq_true_eq] at r1
      have := encF_sound tvLo (2 * k) (by omega) h
      rw [hnm]; exact pos_of_mem this r1
  have Fhi : Optigon.F n (val (N0 + rr)) < 0 := by
    cases h : encF (2 * k) tabHi with
    | none => rw [h] at r2; cases r2
    | some I =>
      rw [h] at r2; simp only [decide_eq_true_eq] at r2
      have := encF_sound tvHi (2 * k) (by omega) h
      rw [hnm]; exact neg_of_hi this r2
  obtain ⟨z, hz, hFz⟩ := root_exists n hlohi hzlo hzhi (Or.inl ⟨Flo, Fhi⟩)
  -- upstream's bracket
  have hlo_lt : Optigon.lo n < (val (N0 - rr)) := by
    apply lo_lt_of n hzlo (by linarith [pi_gt_three])
    have h1 := (mem_point (N := Hlo) (by omega) (by omega) J).2
    have e : (val (N0 - rr)) / 2 = val Hlo := by rw [← b10, val_two_mul]; ring
    rw [e]
    have : val (pointCS Np J |>.2.widen rp).hi < 2 * val (pointCS Hlo J).2.lo := by
      rw [← val_two_mul]; exact val_lt_val s1
    linarith [hSP.2, h1.1]
  have hhi_gt : (val (N0 + rr)) < Optigon.hi n := by
    unfold Optigon.hi
    have := val_lt_val b14
    rw [val_sub'] at this
    have := (abs_le.mp hpi).1
    linarith
  have ha_le : val (Nc - rc) ≤ Optigon.lo n := by
    apply le_lo_of n ha0.le (by linarith [pi_gt_three, hb4, val_le_val (show Nc - rc ≤ Nc + rc by omega)])
    have h1 := (mem_point (N := Ha) (by omega) (by omega) J).2
    have e : val (Nc - rc) / 2 = val Ha := by rw [← b11, val_two_mul]; ring
    rw [e]
    have : 2 * val (pointCS Ha J).2.hi ≤ val (pointCS Np J |>.2.widen rp).lo := by
      rw [← val_two_mul]; exact val_le_val s2
    linarith [hSP.1, h1.2]
  have hhi_le : Optigon.hi n ≤ val (Nc + rc) := by
    unfold Optigon.hi
    have := val_le_val b15
    rw [val_add', val_add'] at this
    have := (abs_le.mp hpi).2
    rw [val_add']
    linarith
  -- uniqueness: `Fd < 0` on `[a, b]`
  have hneg : ∀ t ∈ Set.Icc (val (Nc - rc)) (val (Nc + rc)), Fd n t < 0 := by
    intro t ht
    have hc : |t - val Nc| ≤ val rc := by
      rw [abs_le]
      have e1 : val (Nc - rc) = val Nc - val rc := val_sub' _ _
      have e2 : val (Nc + rc) = val Nc + val rc := val_add' _ _
      constructor <;> linarith [ht.1, ht.2]
    have tv : TabValid t tabU := tab_valid (by omega) (lt_S_of b6 |>.trans' (by omega)) J hU.1 hU.2 hc
    cases h : encFd (2 * k) tabU with
    | none => rw [h] at r3; cases r3
    | some I =>
      rw [h] at r3; simp only [decide_eq_true_eq] at r3
      have := encFd_sound tv (2 * k) (by omega) h
      rw [hnm]; exact neg_of_hi this r3
  have hzI : z ∈ Set.Icc (val (Nc - rc)) (val (Nc + rc)) := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  refine ⟨z, ⟨by linarith [hz.1], by linarith [hz.2]⟩, hFz, ?_, ?_, by linarith [hz.1], by linarith [hz.2]⟩
  · intro z' hz' hF'
    exact root_unique n ha0 hb4 hneg hzI ⟨by linarith [hz'.1], by linarith [hz'.2]⟩ hFz hF'
  · rw [abs_le]
    have e1 : val (N0 - rr) = val N0 - val rr := val_sub' _ _
    have e2 : val (N0 + rr) = val N0 + val rr := val_add' _ _
    constructor <;> linarith [hz.1, hz.2]

/-! ## The polygon at the root: exact identities and inequalities -/

/-- The symbolic vertex `k`, from the literal list `VS` (checked against
`vertexS`, i.e. against upstream's code run symbolically). -/
def vsAt (VS : List (Tm × Tm)) (k : ℕ) : Tm × Tm := VS.getD k (Tm.zero, Tm.zero)

def vsOK (n : ℕ) (VS : List (Tm × Tm)) (k : ℕ) : Bool := decide (vertexS n k = vsAt VS k)

lemma Qc_eq {n : ℕ} {z : ℝ} {VS : List (Tm × Tm)} (h : ∀ k < n, vsOK n VS k = true) (k : Fin n) :
    Qc n z k = ev z (vsAt VS k) := by
  have := h k.val k.isLt
  unfold vsOK at this
  simp only [decide_eq_true_eq] at this
  simp only [Qc, vertex_eval, ev, this]

/-- The vertex enclosure `vd[k]` contains the evaluation of the symbolic vertex. -/
def vdOK (tab : List (FI × FI)) (VS : List (Tm × Tm)) (vd : List (FI × FI)) (k : ℕ) : Bool :=
  match encPair tab (vsAt VS k), vd[k]? with
  | some e, some v => e.1.subset v.1 && e.2.subset v.2
  | _, _ => false

theorem encl_of_vdOK {n : ℕ} {z : ℝ} {tab : List (FI × FI)} (hv : TabValid z tab) {VS : List (Tm × Tm)}
    (hVS : ∀ k < n, vsOK n VS k = true) {vd : List (FI × FI)} (hlen : vd.length = n)
    (h : ∀ k < n, vdOK tab VS vd k = true) : Encl (Qc n z) vd := by
  refine ⟨hlen, fun k => ?_⟩
  have hk := h k.val k.isLt
  unfold vdOK at hk
  rw [List.getElem?_eq_getElem (by rw [hlen]; exact k.isLt)] at hk
  cases he : encPair tab (vsAt VS k) with
  | none => rw [he] at hk; cases hk
  | some e =>
    rw [he] at hk
    simp only [Bool.and_eq_true] at hk
    unfold encPair at he
    cases h1 : enc tab (vsAt VS k).1 <;> cases h2 : enc tab (vsAt VS k).2 <;> rw [h1, h2] at he <;>
      simp only [reduceCtorEq, Option.some.injEq] at he
    subst he
    rw [Qc_eq hVS k]
    exact ⟨mem_of_subset (enc_sound hv _ _ h1) hk.1, mem_of_subset (enc_sound hv _ _ h2) hk.2⟩

lemma fin_add_one_val {n : ℕ} [NeZero n] (i : Fin n) : ((i + 1 : Fin n) : ℕ) = (i.val + 1) % n := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- Side `i` is a side shape, or a closing side with `n = 16k`. -/
def sideWOK (n k : ℕ) (VS : List (Tm × Tm)) (sideW : List W) (i : ℕ) : Bool :=
  let w := sideW.getD i default
  (decide (w.s.kind = 1) || (decide (w.s.kind = 2) && decide (w.s.ck = k)))
    && w.fits (vsAt VS ((i + 1) % n)) (vsAt VS i)

/-- **Every side has length `2 sin(z/2)`**, at a zero of `F`. -/
theorem sides_eq {n k : ℕ} [NeZero n] (hn : n = 16 * k) (hk : 1 ≤ k) {z : ℝ} (hc : cos (2 * z) ≠ 0)
    (hF : Optigon.F n z = 0) {VS : List (Tm × Tm)} (hVS : ∀ k < n, vsOK n VS k = true)
    {sideW : List W} (hW : ∀ i < n, sideWOK n k VS sideW i = true) (i : Fin n) :
    nsq (Qc n z (i + 1) - Qc n z i) = (2 * sin (z / 2)) ^ 2 := by
  have h := hW i.val i.isLt
  unfold sideWOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hkind, hfit⟩ := h
  set w := sideW.getD i.val default
  have hk' : w.s.kind = 2 → 1 ≤ w.s.ck := by
    intro h2; rcases hkind with h1 | ⟨_, h3⟩
    · omega
    · omega
  rw [Qc_eq hVS, Qc_eq hVS, fin_add_one_val, W.nsq_of_fits hc hk' hfit]
  unfold Shp.val
  rcases hkind with h1 | ⟨h2, h3⟩
  · rw [h1]; rfl
  · rw [h2]
    simp only
    rw [h3, show 8 * (2 * k) = n by omega, hF, zero_add]

/-- Diameter `e` is a diameter shape (vacuous past the end of `E`, so that the
check can run on whole chunks). -/
def diamWOK {n : ℕ} (VS : List (Tm × Tm)) (E : List (Fin n × Fin n)) (diamW : List W) (e : ℕ) : Bool :=
  match E[e]? with
  | none => true
  | some ab => match diamW[e]? with
    | some w => decide (w.s.kind = 0) && w.fits (vsAt VS ab.2.val) (vsAt VS ab.1.val)
    | none => false

theorem diams_eq {n : ℕ} {z : ℝ} (hc : cos (2 * z) ≠ 0) {VS : List (Tm × Tm)} (hVS : ∀ k < n, vsOK n VS k = true)
    {E : List (Fin n × Fin n)} {diamW : List W} (hW : ∀ e < E.length, diamWOK VS E diamW e = true)
    (e : Fin E.length) : nsq (Qc n z (E[e.val]).2 - Qc n z (E[e.val]).1) = 1 := by
  have h := hW e.val e.isLt
  unfold diamWOK at h
  rw [List.getElem?_eq_getElem e.isLt] at h
  simp only at h
  cases hw : diamW[e.val]? with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [Qc_eq hVS, Qc_eq hVS, W.nsq_of_fits hc (by rw [h.1]; simp) h.2]
    unfold Shp.val; rw [h.1]; rfl

/-- Ayala Hoffmann's closed form of the active graph `G_n`, as a predicate on `i`, `j`. -/
def gnAct (n i j : ℕ) : Bool :=
  let h := n / 2
  let t (a b : ℕ) : Bool := decide (a < h) &&
    ((decide ((b + n - a) % n = h) && decide (a ≠ h / 2))
      || (decide ((b + n - a) % n = h - 1) && (decide (a % 4 = 2) || decide (a % 4 = 3)))
      || (decide ((b + n - a) % n = h + 1) && (decide (a % 4 = 0) || decide (a % 4 = 3))))
  t i j || t j i

/-- Every pair `G_n` marks is in the list `E`. -/
def actOK {n : ℕ} (E : List (Fin n × Fin n)) (i : ℕ) : Bool :=
  (List.range n).all fun j => !(decide (i < j) && gnAct n i j) || (E.map fun e => (e.1.val, e.2.val)).contains (i, j)

/-- **Small**: every pair at distance at most `1`. -/
theorem small_of {n : ℕ} {z : ℝ} (hc : cos (2 * z) ≠ 0) {VS : List (Tm × Tm)} (hVS : ∀ k < n, vsOK n VS k = true)
    {E : List (Fin n × Fin n)} {diamW : List W} (hW : ∀ e < E.length, diamWOK VS E diamW e = true)
    {vd : List (FI × FI)} (he : Encl (Qc n z) vd) (hfar : ∀ i < n, farRowOK (gnAct n) vd i = true)
    (hact : ∀ i < n, actOK E i = true) : Small (Qc n z) := by
  have hlt : ∀ i j : Fin n, i < j → dC i j (Qc n z) ≤ 0 := by
    intro i j hij
    rcases far_sound (gnAct n) he hfar i j hij with h | h
    · have := hact i.val i.isLt
      unfold actOK at this
      have hj := List.all_eq_true.mp this j.val (List.mem_range.mpr j.isLt)
      simp only [hij, h, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
        Fin.lt_def] at hj
      have hij' : i.val < j.val := hij
      simp only [hij', decide_true, Bool.true_and, Bool.not_true, Bool.false_or] at hj
      obtain ⟨e, he', hee⟩ := List.mem_map.mp (List.contains_iff_mem.mp hj)
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he'
      have hd := diams_eq hc hVS hW ⟨t, ht⟩
      simp only [Prod.mk.injEq] at hee
      have h1 : (E[t]).1 = i := Fin.ext hee.1
      have h2 : (E[t]).2 = j := Fin.ext hee.2
      rw [h1, h2] at hd
      unfold dC; rw [hd]; simp
    · exact h.le
  intro i j
  rcases lt_trichotomy i j with h | h | h
  · exact hlt i j h
  · subst h; unfold dC; simp [nsq, ip]
  · have := hlt j i h
    unfold dC at this ⊢; rw [nsq_comm]; exact this

/-! ## Bars, sums -/

/-- The interval sum. -/
def sumFI : List FI → FI
  | [] => ofInt 0
  | I :: t => add I (sumFI t)

theorem sum_mem : ∀ {n : ℕ} (f : Fin n → ℝ) (Is : List FI) (hlen : Is.length = n),
    (∀ i : Fin n, FI.mem (f i) (Is[i.val]'(by rw [hlen]; exact i.isLt))) → FI.mem (∑ i, f i) (sumFI Is)
  | 0, f, Is, hlen, _ => by
    rw [List.length_eq_zero_iff] at hlen; subst hlen
    simpa [sumFI] using mem_ofInt 0
  | n + 1, f, Is, hlen, h => by
    cases Is with
    | nil => simp at hlen
    | cons I t =>
      simp only [List.length_cons, add_left_inj] at hlen
      rw [Fin.sum_univ_succ]
      have h0 := h 0
      simp only [Fin.val_zero, List.getElem_cons_zero] at h0
      exact mem_add h0 (sum_mem (fun i => f i.succ) t hlen (fun i => by
        have := h i.succ; simpa using this))

/-- The bar `b`, read from the literal list. -/
def barOf {n nb : ℕ} [NeZero n] (BARS : List (Fin n × Fin n)) (b : Fin nb) : Fin n × Fin n :=
  BARS.getD b.val default

lemma barOf_side {n m : ℕ} [NeZero n] {E BARS : List (Fin n × Fin n)}
    (hB : BARS = (List.finRange n).map (fun i => (i, i + 1)) ++ E) (i : Fin n) :
    barOf (nb := n + m) BARS (Fin.castAdd m i) = (i, i + 1) := by
  subst hB
  unfold barOf
  simp only [Fin.coe_castAdd, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp)]
  simp

/-- The endpoints of the active diameter `e`. -/
def eA {n m : ℕ} [NeZero n] (E : List (Fin n × Fin n)) (e : Fin m) : Fin n := (E.getD e.val default).1
def eB {n m : ℕ} [NeZero n] (E : List (Fin n × Fin n)) (e : Fin m) : Fin n := (E.getD e.val default).2

lemma barOf_diam {n m : ℕ} [NeZero n] {E BARS : List (Fin n × Fin n)}
    (hB : BARS = (List.finRange n).map (fun i => (i, i + 1)) ++ E) (e : Fin m) :
    barOf (nb := n + m) BARS (Fin.natAdd n e) = (eA E e, eB E e) := by
  subst hB
  unfold barOf eA eB
  simp only [Fin.coe_natAdd, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

lemma getD_eq_getElem' {α : Type*} [Inhabited α] (l : List α) (i : ℕ) (h : i < l.length) :
    l.getD i default = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma zip_finRange' {α : Type*} [Inhabited α] (L : List α) (N : ℕ) (h : L.length = N) :
    (List.finRange N).zip L = (List.finRange N).map fun b => (b, L.getD b.val default) := by
  subst h
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

/-- A bounded check, from checks on consecutive chunks of `c` indices. -/
theorem forall_lt_of_chunks (f : ℕ → Bool) (c q N : ℕ) (hc : 0 < c) (hN : N ≤ c * q)
    (h : ∀ t < q, (List.range' (c * t) c).all f = true) : ∀ i < N, f i = true := by
  intro i hi
  have ht : i / c < q := by
    rw [Nat.div_lt_iff_lt_mul hc]; rw [mul_comm] at hN; omega
  have := List.all_eq_true.mp (h (i / c) ht) i
  apply this
  rw [List.mem_range']
  exact ⟨i % c, Nat.mod_lt _ hc, by rw [one_mul]; exact (Nat.div_add_mod i c).symm⟩

/-! ## The theorem -/

/-- **The published polygon, from the kernel checks.** For `n = 16k`: if the
checks pass, upstream's `F_n` has exactly one zero `z` in upstream's bracket, and
the polygon upstream builds there is a strictly convex equilateral small `n`-gon
and a strict local maximiser of the perimeter, modulo Euclidean motions. -/
theorem published_of_checks (n k m : ℕ) [NeZero n] (hn : n = 16 * k) (hk : 1 ≤ k)
    -- the root, and upstream's bracket
    (J : ℕ) (N0 rr Np rp Nc rc Hlo Ha : ℤ) (tabLo tabHi tabU : List (FI × FI))
    (hb : bracketOK n N0 rr Np rp Nc rc Hlo Ha = true) (hs : sinOK J Np rp Hlo Ha = true)
    (hLo : tabHead tabLo = true ∧
      tabOK ((pointCS (N0 - rr) J).1.widen 0) ((pointCS (N0 - rr) J).2.widen 0) tabLo = true)
    (hHi : tabHead tabHi = true ∧
      tabOK ((pointCS (N0 + rr) J).1.widen 0) ((pointCS (N0 + rr) J).2.widen 0) tabHi = true)
    (hU : tabHead tabU = true ∧ tabOK ((pointCS Nc J).1.widen rc) ((pointCS Nc J).2.widen rc) tabU = true)
    (hr : rootOK k tabLo tabHi tabU = true)
    -- the polygon: vertices, exact identities, inequalities
    (tab : List (FI × FI))
    (htab : tabHead tab = true ∧ tabOK ((pointCS N0 J).1.widen rr) ((pointCS N0 J).2.widen rr) tab = true)
    (VS : List (Tm × Tm)) (hVS : ∀ k < n, vsOK n VS k = true)
    (vd : List (FI × FI)) (hvdlen : vd.length = n) (hvd : ∀ k < n, vdOK tab VS vd k = true)
    (hconv : ∀ i < n, sideOK vd i = true) (hfar : ∀ i < n, farRowOK (gnAct n) vd i = true)
    (E : List (Fin n × Fin n)) (hm : E.length = m) (hact : ∀ i < n, actOK E i = true)
    (sideW diamW : List W) (hsw : ∀ i < n, sideWOK n k VS sideW i = true)
    (hdw : ∀ e < E.length, diamWOK VS E diamW e = true)
    -- rigidity
    (BARS : List (Fin n × Fin n)) (hBARS : BARS = (List.finRange n).map (fun i => (i, i + 1)) ++ E)
    (order : List (Fin n × Fin n × Fin n))
    (hen : henOK BARS [0, 1] order = true) (hcov : coverOK order = true)
    (hdet : detOK vd (order.map fun s => (s.1.val, s.2.1.val, s.2.2.val)) = true)
    -- the self-stress
    (BL : List (Fin (n + m) × (Fin n × Fin n))) (hBL : BL = (List.finRange (n + m)).zip BARS)
    (steps : List (HStep n (n + m))) (hord : order = steps.reverse.map fun s => (s.k, s.i, s.j))
    (ex : List (Fin (n + m) × ℤ)) (pb : Fin (n + m)) (sd : List FI)
    (hsOK : stepsOK (barOf BARS) (ex.map (·.1)) [] [] steps = true)
    (hpre : presetOK sd ex = true) (hfi : stepsFIOK vd sd BL (ex.map (·.1)) steps = true)
    (hpin : pinFIOK vd sd BL (knownAfter (ex.map (·.1)) steps) 0 1 pb = true)
    (hpb : barOf BARS pb = (0, 1))
    (hpbS : steps.all (fun s => decide (pb ≠ s.bi) && decide (pb ≠ s.bj)) = true)
    (hpbE : (ex.map (·.1)).contains pb = false)
    (hcovS : (List.finRange (n + m)).all (fun b => (pb :: knownAfter (ex.map (·.1)) steps).contains b) = true)
    (hsdlen : sd.length = n + m) (hlam : (sd.drop n).all (fun I => decide (0 < I.lo)) = true)
    (hsum : (sumFI (sd.take n)).hi < 0) :
    ∃ z : ℝ, z ∈ Set.Ioo (Optigon.lo n) (Optigon.hi n) ∧ Optigon.F n z = 0 ∧
      (∀ z' ∈ Set.Ioo (Optigon.lo n) (Optigon.hi n), Optigon.F n z' = 0 → z' = z) ∧
      0 < 2 * sin (z / 2) ∧ IsFeasibleConvex (Qc n z, 2 * sin (z / 2)) ∧
      (∀ᶠ y in nhds ((Qc n z, 2 * sin (z / 2)) : Amb n), IsFeasible y → 2 * sin (z / 2) ≤ y.2 →
          Feasible.Congruent y.1 (Qc n z) ∧ y.2 = 2 * sin (z / 2)) ∧
      (∀ᶠ y in nhds ((Qc n z, 2 * sin (z / 2)) : Amb n), IsFeasible y → y.2 ≤ 2 * sin (z / 2)) := by
  obtain ⟨z, hzB, hF, huniq, hzr, hz0, hz4⟩ :=
    root_facts n k hn hk J N0 rr Np rp Nc rc Hlo Ha tabLo tabHi tabU hb hs hLo hHi hU hr
  have hb' := hb
  unfold bracketOK at hb'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hb'
  have hn16 : 16 ≤ n := by omega
  have hS := S_pos
  have hc : cos (2 * z) ≠ 0 := cos_two_ne hz0 hz4
  have tv : TabValid z tab := tab_valid (N := N0) (by omega) (by omega) J htab.1 htab.2 hzr
  have he : Encl (Qc n z) vd := encl_of_vdOK tv hVS hvdlen hvd
  have hl : 0 < 2 * sin (z / 2) := by
    have : 0 < sin (z / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_gt_three])
    linarith
  -- the sides, the diameters
  have hside := sides_eq hn hk hc hF hVS hsw
  have hpeq : ∀ i : Fin n, eC i (Qc n z, 2 * sin (z / 2)) = 0 := by
    intro i; unfold eC; simp only; rw [hside i]; ring
  have hdiam : ∀ e : Fin m, nsq (Qc n z (eB E e) - Qc n z (eA E e)) = 1 := by
    intro e
    have := diams_eq hc hVS hdw ⟨e.val, by rw [hm]; exact e.isLt⟩
    have hg := getD_eq_getElem' E e.val (by rw [hm]; exact e.isLt)
    simp only [eA, eB, hg]; exact this
  have hpact : ∀ e : Fin m, dC (eA E e) (eB E e) (Qc n z) = 0 := by
    intro e; unfold dC; rw [hdiam e]; ring
  have hfeas : IsFeasibleConvex (Qc n z, 2 * sin (z / 2)) :=
    ⟨conv_sound (by omega) he hconv, small_of hc hVS hdw he hfar hact, hpeq, hl⟩
  have h1n : (1 : Fin n).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have e0 : (⟨0, by omega⟩ : Fin n) = 0 := Fin.ext (by simp)
  have e1 : (⟨1, by omega⟩ : Fin n) = 1 := Fin.ext (by rw [h1n])
  have h01 : Qc n z 0 ≠ Qc n z 1 := by
    intro h
    have h2 := hside 0
    rw [zero_add, h, sub_self] at h2
    have : nsq (0 : ℝ × ℝ) = 0 := by simp [nsq, ip]
    rw [this] at h2
    nlinarith
  -- rigidity
  have hIR : ∀ w : Cfg n, (dataOf (Qc n z) (2 * sin (z / 2)) (eA (m := m) E) (eB (m := m) E)).Ieq w 0 →
      (dataOf (Qc n z) (2 * sin (z / 2)) (eA (m := m) E) (eB (m := m) E)).R w := by
    rintro w ⟨hsd, hdd⟩
    have hL : ∀ ab ∈ BARS, ip (Qc n z ab.2 - Qc n z ab.1) (w ab.2 - w ab.1) = 0 := by
      intro ab hab
      rw [hBARS, List.mem_append] at hab
      rcases hab with hab | hab
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hab
        have := hsd i
        simp only [Data.sideD, dataOf, ip_smul_left, sub_zero] at this
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (inv_ne_zero hl.ne')
        · exact h
      · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hab
        have := hdd ⟨t, by rw [← hm]; exact ht⟩
        simp only [Data.diamD, dataOf, eA, eB, getD_eq_getElem' E t ht] at this
        exact this
    have hpin' : barMem BARS ⟨0, by omega⟩ ⟨1, by omega⟩ = true := by
      rw [e0, e1]
      unfold barMem
      have : ((0 : Fin n), (1 : Fin n)) ∈ BARS := by
        rw [hBARS]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨0, List.mem_finRange _, by simp⟩)
      simp only [Bool.or_eq_true, List.contains_iff_mem]
      exact Or.inl this
    have hok' : henOK BARS [⟨0, by omega⟩, ⟨1, by omega⟩] order = true := by rw [e0, e1]; exact hen
    obtain ⟨t, ω, hw⟩ := rigid_of_henneberg (by omega) BARS (Qc n z) w hL (by rw [e0, e1]; exact h01)
      hpin' order hok' hcov (det_ne_of_detOK he order hdet)
    exact ⟨t, ω, fun i => by simpa [dataOf] using hw i⟩
  -- the self-stress
  have hlenB : BARS.length = n + m := by rw [hBARS]; simp [hm]
  have hbl : BL = (List.finRange (n + m)).map fun b => (b, barOf BARS b) := by
    rw [hBL, zip_finRange' BARS (n + m) hlenB]; rfl
  have hdetS : ∀ s ∈ steps, stepDet (Qc n z) s ≠ 0 := by
    intro s hs
    have := det_ne_of_detOK he order hdet (s.k, s.i, s.j)
      (by rw [hord]; exact List.mem_map.mpr ⟨s, List.mem_reverse.mpr hs, rfl⟩)
    unfold stepDet; intro h0; apply this
    simp only [Prod.fst_sub, Prod.snd_sub] at h0 ⊢
    linear_combination h0
  have hcovV : ∀ q : Fin n, q = 0 ∨ q = 1 ∨ q ∈ steps.map (·.k) := by
    intro q
    unfold coverOK at hcov
    have := List.all_eq_true.mp hcov q (List.mem_finRange q)
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at this
    rcases this with (h | h) | h
    · exact Or.inl (Fin.ext (by simp [h]))
    · exact Or.inr (Or.inl (Fin.ext (by rw [h, h1n])))
    · right; right
      rw [hord, List.map_map] at h
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
      exact List.mem_map.mpr ⟨s, List.mem_reverse.mp hs, rfl⟩
  have hpbS' : ∀ s ∈ steps, pb ≠ s.bi ∧ pb ≠ s.bj := by
    intro s hs
    have := List.all_eq_true.mp hpbS s hs
    simpa using this
  have hpbE' : pb ∉ ex.map (·.1) := by
    intro h; rw [List.contains_iff_mem.mpr h] at hpbE; cases hpbE
  have hbal := bal_zero (Qc n z) (barOf BARS) (presetσ ex) (ex.map (·.1)) (fun b hb => presetσ_zero ex b hb)
    steps 0 1 pb (by simp) h1n h01 hsOK hdetS hcovV (Or.inl hpb) hpbS' hpbE'
  have hbar : ∀ b, (barOf (nb := n + m) BARS b).1 ≠ (barOf (nb := n + m) BARS b).2 := by
    intro b
    induction b using Fin.addCases with
    | left i =>
      rw [barOf_side hBARS]
      intro h
      simp only at h
      have h' := congrArg Fin.val h
      rw [fin_add_one_val] at h'
      have hi := i.isLt
      rcases Nat.lt_or_ge (i.val + 1) n with h2 | h2
      · rw [Nat.mod_eq_of_lt h2] at h'; omega
      · have h3 : i.val + 1 = n := by omega
        rw [h3, Nat.mod_self] at h'; omega
    | right e =>
      rw [barOf_diam hBARS]
      intro h
      have := hdiam e
      simp only at h
      rw [h, sub_self] at this
      simp [nsq, ip] at this
  set σ := stressR (Qc n z) (barOf BARS) (presetσ ex) steps 0 1 pb with hσ
  have hstat : ∀ v : Cfg n, (∑ i, σ (Fin.castAdd m i) * ip (Qc n z (i + 1) - Qc n z i) (v (i + 1) - v i))
      + ∑ e, σ (Fin.natAdd n e) * ip (Qc n z (eB E e) - Qc n z (eA E e)) (v (eB E e) - v (eA E e)) = 0 := by
    intro v
    have h := stationary_of_bal (Qc n z) (barOf BARS) hbar σ hbal v
    rw [Fin.sum_univ_add] at h
    simp only [barOf_side hBARS, barOf_diam hBARS] at h
    exact h
  have hmult := mult_of_stationary' hl.ne' (eA (m := m) E) (eB (m := m) E) (fun i => σ (Fin.castAdd m i))
    (fun e => σ (Fin.natAdd n e)) _ hstat rfl
  -- the enclosures
  have henc := stress_encl he hbl ex steps 0 1 pb hsOK hpre hfi hpin hpbS' hpbE'
  have hall : ∀ b : Fin (n + m), ∃ S, sd[b.val]? = some S ∧ FI.mem (σ b) S := by
    intro b
    have := List.all_eq_true.mp hcovS b (List.mem_finRange b)
    exact henc b (List.contains_iff_mem.mp this)
  have hlamp : ∀ e : Fin m, 0 < σ (Fin.natAdd n e) := by
    intro e
    obtain ⟨S', hS', hmem⟩ := hall (Fin.natAdd n e)
    have hlt : n + e.val < sd.length := by rw [hsdlen]; omega
    simp only [Fin.coe_natAdd] at hS'
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hS'
    have hlt' : e.val < (sd.drop n).length := by simp [hsdlen]
    have := List.all_eq_true.mp hlam ((sd.drop n)[e.val]'hlt') (List.getElem_mem hlt')
    simp only [List.getElem_drop, decide_eq_true_eq] at this
    rw [← hS'] at hmem
    exact pos_of_mem hmem this
  have hsneg : ∑ i, σ (Fin.castAdd m i) < 0 := by
    have hmem := sum_mem (fun i => σ (Fin.castAdd m i)) (sd.take n) (by simp [hsdlen]) (fun i => by
      obtain ⟨S', hS', hm'⟩ := hall (Fin.castAdd m i)
      have hlt : i.val < sd.length := by rw [hsdlen]; omega
      simp only [Fin.coe_castAdd] at hS'
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hS'
      simp only [List.getElem_take]
      rw [hS']; exact hm')
    exact neg_of_hi hmem hsum
  have hkap : 0 < -(2 * sin (z / 2) * ∑ i, σ (Fin.castAdd m i)) :=
    neg_pos.mpr (mul_neg_of_pos_of_neg hl hsneg)
  refine ⟨z, hzB, hF, huniq, hl, hfeas,
    thm_3_5 hl h01 hkap hmult hlamp hIR hpeq hpact,
    thm_3_5_le hl h01 hkap hmult hlamp hIR hpeq hpact⟩

end Chiquipoli.Family.Trig
