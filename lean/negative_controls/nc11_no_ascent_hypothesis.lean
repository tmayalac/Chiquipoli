-- NEGATIVE CONTROL. Must FAIL to compile.
-- Theorem 3.5's algebraic core without `0 ≤ η`. That hypothesis is what the
-- analytic half supplies (the competitors have perimeter at least L(p,ℓ));
-- without it the first variation being ≤ 0 says nothing, and η need not vanish.
import ChiquipoliLean
namespace Chiquipoli.FirstOrder
theorem bad {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] {D : Data n ι} {κ : ℝ}
    {α : Fin n → ℝ} {lam : ι → ℝ} (hκ : 0 < κ)
    (hm : D.MultiplierIdentity κ α lam) (hlam : ∀ e, 0 < lam e)
    (hIR : ∀ w : Fin n → ℝ × ℝ, D.Ieq w 0 → D.R w)
    {v : Fin n → ℝ × ℝ} {η : ℝ}
    (hK : D.Keq v η) (hslice : ∀ r, D.R r → cip v r = 0) :
    v = 0 ∧ η = 0 := by
  have hle := no_ascent hm (fun e => (hlam e).le) hK
  have hη0 : η = 0 := by nlinarith
  have hz : κ * η = 0 := by rw [hη0, mul_zero]
  have hI : D.Ieq v 0 := by
    refine ⟨fun i => ?_, active_equality hm hlam hK hz⟩
    have h := hK.1 i; rwa [hη0] at h
  exact ⟨eq_zero_of_cip_self (hslice v (hIR v hI)), hη0⟩
end Chiquipoli.FirstOrder
