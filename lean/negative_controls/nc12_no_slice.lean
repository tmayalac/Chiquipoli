-- NEGATIVE CONTROL. Must FAIL to compile.
-- Theorem 3.5's algebraic core without the slice condition `v ⊥ R(p)`. Without
-- it the conclusion is false, not merely unproved: any nonzero infinitesimal
-- rigid motion lies in K_eq with η = 0, and perimeter is invariant along it.
-- That is exactly why the paper normalises each competitor into R(p)^⊥.
import ChiquipoliLean
namespace Chiquipoli.FirstOrder
theorem bad {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] {D : Data n ι} {κ : ℝ}
    {α : Fin n → ℝ} {lam : ι → ℝ} (hκ : 0 < κ)
    (hm : D.MultiplierIdentity κ α lam) (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Fin n → ℝ × ℝ, D.Ieq w 0 → D.R w)
    {v : Fin n → ℝ × ℝ} {η : ℝ} (hK : D.Keq v η) (hη : 0 ≤ η) :
    v = 0 ∧ η = 0 := by
  have hle := no_ascent hm (fun e => (hlam e).le) hK
  have hη0 : η = 0 := by nlinarith
  have hz : κ * η = 0 := by rw [hη0, mul_zero]
  have hI : D.Ieq v 0 := by
    refine ⟨fun i => ?_, active_equality hm hlam hK hz⟩
    have h := hK.1 i; rwa [hη0] at h
  have hR : D.R v := hIR v hI
  exact ⟨eq_zero_of_cip_self (by linarith), hη0⟩
end Chiquipoli.FirstOrder
