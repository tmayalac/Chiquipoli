-- NEGATIVE CONTROL. Must FAIL to compile.
-- Theorem 6.4's radius is fixed by one inequality of `radius_of_certificate`,
-- 16 r^2 (Λ^2 + A^2) ≤ σ2 Λ^2, at the certified constants A = 67/1000,
-- Λ = 3/2500, σ2 = 17/625. At r = 663/1000000 it holds (3.16e-8 ≤ 3.92e-8);
-- at r = 1/1000 it is false (7.18e-8 > 3.92e-8). The proof below is the proof
-- of `A16_radius_at` with only the radius changed, and must not go through:
-- the certificate does not give a radius 50% larger than the article's.
import ChiquipoliLean
namespace Chiquipoli.Feasible
open Chiquipoli.FirstOrder
theorem bad {z : ℝ} (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) (h0 : 0 < z) (hpi : z < Real.pi)
    (q : Cfg 16) (m : ℝ)
    (hqs : ∀ i, elen (q (i + 1) - q i) = m) (hqd : ∀ i j, elen (q j - q i) ≤ 1)
    (hlm : 2 * Real.sin (z / 2) ≤ m)
    (hdist : distMod q m (A16p z) (2 * Real.sin (z / 2)) < 1 / 1000) :
    m = 2 * Real.sin (z / 2) ∧ Congruent q (A16p z) := by
  have hl : 0 < 2 * Real.sin (z / 2) := by have := sin_half_pos h0 hpi; linarith
  have hqs' : ∀ i, nsq (q (i + 1) - q i) = m ^ 2 := by
    intro i; rw [← elen_sq, hqs i]
  have hqd' : ∀ e, nsq (q ((A16Data z).b e) - q ((A16Data z).a e)) ≤ 1 := by
    intro e
    have h1 := hqd ((A16Data z).a e) ((A16Data z).b e)
    have h2 := elen_nonneg (q ((A16Data z).b e) - q ((A16Data z).a e))
    rw [← elen_sq]; nlinarith
  exact radius_of_certificate (A16Data z) (p := A16p z) hl rfl (A16_s_smul z) (A16_u_smul z)
    (A16_side_nsq hF) (A16_diam_nsq z) (A16_multiplier_identity z hF)
    (A := 67 / 1000) (Λ := 3 / 2500) (σ2 := 17 / 625) (r := 1 / 1000)
    (by norm_num) (A16_alpha_ge z hcb) (A16_lam_ge z hcb)
    (fun v dt horth => A16_coercive hsz hcb v dt horth) (by norm_num)
    q m hqs' hqd' hlm hdist
end Chiquipoli.Feasible
