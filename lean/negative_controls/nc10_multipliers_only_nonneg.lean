-- NEGATIVE CONTROL. Must FAIL to compile.
-- Lemma 3.3 with the multipliers weakened from strictly positive to merely
-- nonnegative. This is the crux of hypothesis (i): with `λ ≥ 0` a vanishing
-- weighted sum can hide a strictly negative diameter differential against a
-- zero multiplier, so active equality does not follow. Everything else in the
-- proof script is unchanged.
import ChiquipoliLean
namespace Chiquipoli.FirstOrder
open Finset
theorem bad {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] {D : Data n ι} {κ : ℝ}
    {α : Fin n → ℝ} {lam : ι → ℝ}
    (hm : D.MultiplierIdentity κ α lam) (hlam : ∀ e, 0 ≤ lam e)
    {v : Fin n → ℝ × ℝ} {η : ℝ} (hK : D.Keq v η) (hz : κ * η = 0) :
    ∀ e, D.diamD v e = 0 := by
  have hside : (∑ i, α i * D.sideD v η i) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hK.1 i]; ring
  have hsum : (∑ e, lam e * D.diamD v e) = 0 := by
    have h := hm v η; rw [hz, hside, zero_add] at h; linarith
  have hnp : ∀ e ∈ (univ : Finset ι), lam e * D.diamD v e ≤ 0 := by
    intro e _
    have h1 := hlam e
    have h2 := hK.2 e
    nlinarith
  have hz' := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hsum
  intro e
  rcases mul_eq_zero.mp (hz' e (mem_univ e)) with h | h
  · linarith [hlam e, hK.2 e]
  · exact h
end Chiquipoli.FirstOrder
