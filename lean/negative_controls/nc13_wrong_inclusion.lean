-- NEGATIVE CONTROL. Must FAIL to compile.
-- Theorem 3.5's algebraic core with hypothesis (ii) replaced by its FREE half.
-- `R_eq ⊆ I_eq` holds at every configuration and is proved unconditionally as
-- `dsq_rigid`; it carries no information. The certified content is the reverse
-- inclusion, `I_eq ⊆ R_eq`, which is the rank gate. Substituting one for the
-- other must not go through.
import ChiquipoliLean
namespace Chiquipoli.FirstOrder
theorem bad {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] {D : Data n ι} {κ : ℝ}
    {α : Fin n → ℝ} {lam : ι → ℝ} (hκ : 0 < κ)
    (hm : D.MultiplierIdentity κ α lam) (hlam : ∀ e, 0 < lam e)
    (hRI : ∀ w : Fin n → ℝ × ℝ, D.R w → D.Ieq w 0)
    {v : Fin n → ℝ × ℝ} {η : ℝ}
    (hK : D.Keq v η) (hη : 0 ≤ η) (hslice : ∀ r, D.R r → cip v r = 0) :
    v = 0 ∧ η = 0 := by
  have hle := no_ascent hm (fun e => (hlam e).le) hK
  have hη0 : η = 0 := by nlinarith
  have hz : κ * η = 0 := by rw [hη0, mul_zero]
  have hI : D.Ieq v 0 := by
    refine ⟨fun i => ?_, active_equality hm hlam hK hz⟩
    have h := hK.1 i; rwa [hη0] at h
  have hR : D.R v := by linarith
  exact ⟨eq_zero_of_cip_self (hslice v hR), hη0⟩
end Chiquipoli.FirstOrder
