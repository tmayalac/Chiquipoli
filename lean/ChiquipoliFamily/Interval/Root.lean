/-
# The zero of upstream's `F`: existence in a tiny bracket, uniqueness in upstream's

* `root_exists`: if interval arithmetic shows `F > 0` at `zlo` and `F < 0` at `zhi`
  (or the reverse), `F` has a zero strictly between (intermediate value theorem;
  `F` is continuous where `cos 2t ≠ 0`).
* `root_unique`: if `Fd < 0` on an interval `[a, b]` containing upstream's bracket
  `(lo, hi) = (2 arcsin(sin(π/n)/2), π/n)`, then `F` has at most one zero there.
* `lo_lt_of`, `lo_ge_of`: bounds on `lo` from bounds on `sin`, through `arcsin`.

Nothing here depends on `n` beyond `n > 0`.
-/
import ChiquipoliFamily.Interval.FDeriv

set_option linter.unusedVariables false

namespace Chiquipoli.Family.Trig

open Real Set

lemma cos_two_ne {t : ℝ} (h0 : 0 < t) (h1 : t < π / 4) : cos (2 * t) ≠ 0 := by
  apply ne_of_gt; apply cos_pos_of_mem_Ioo; constructor <;> linarith

theorem root_exists (n : ℕ) {zlo zhi : ℝ} (hlt : zlo < zhi) (h0 : 0 < zlo) (h1 : zhi < π / 4)
    (hs : (0 < Optigon.F n zlo ∧ Optigon.F n zhi < 0) ∨ (Optigon.F n zlo < 0 ∧ 0 < Optigon.F n zhi)) :
    ∃ z ∈ Ioo zlo zhi, Optigon.F n z = 0 := by
  have hc : ContinuousOn (Optigon.F n) (Icc zlo zhi) :=
    F_continuousOn n zlo zhi (fun t ht => cos_two_ne (by linarith [ht.1]) (by linarith [ht.2]))
  rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨z, hz, hF⟩ := intermediate_value_Ioo' hlt.le hc ⟨hb, ha⟩
    exact ⟨z, hz, hF⟩
  · obtain ⟨z, hz, hF⟩ := intermediate_value_Ioo hlt.le hc ⟨ha, hb⟩
    exact ⟨z, hz, hF⟩

theorem root_unique (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : b < π / 4)
    (hneg : ∀ t ∈ Icc a b, Fd n t < 0) {z z' : ℝ} (hz : z ∈ Icc a b) (hz' : z' ∈ Icc a b)
    (hF : Optigon.F n z = 0) (hF' : Optigon.F n z' = 0) : z' = z := by
  have hanti := F_strictAnti n a b (fun t ht => cos_two_ne (by linarith [ht.1]) (by linarith [ht.2])) hneg
  exact hanti.injOn hz' hz (hF'.trans hF.symm)

/-- `lo < q` when `sin(π/n)/2 < sin(q/2)`, for `0 < q ≤ π`. -/
lemma lo_lt_of (n : ℕ) {q : ℝ} (hq0 : 0 < q) (hqπ : q ≤ π)
    (h : sin (π / n) / 2 < sin (q / 2)) : Optigon.lo n < q := by
  unfold Optigon.lo
  have hq2 : q / 2 ≤ π / 2 := by linarith
  have hq2' : -(π / 2) ≤ q / 2 := by linarith [pi_pos]
  have := (arcsin_lt_iff_lt_sin' (y := q / 2) ⟨by linarith [pi_pos], hq2⟩).mpr h
  linarith

/-- `q ≤ lo` when `sin(q/2) ≤ sin(π/n)/2`, for `0 ≤ q ≤ π`. -/
lemma le_lo_of (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hqπ : q ≤ π)
    (h : sin (q / 2) ≤ sin (π / n) / 2) : q ≤ Optigon.lo n := by
  unfold Optigon.lo
  have hq2 : q / 2 ≤ π / 2 := by linarith
  have := (le_arcsin_iff_sin_le' (x := q / 2) ⟨by linarith [pi_pos], hq2⟩).mpr h
  linarith

end Chiquipoli.Family.Trig
