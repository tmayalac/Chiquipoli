-- NEGATIVE CONTROL (family). Must FAIL to compile.
-- Infinitesimal rigidity with only the SIDE constraints (no diameter bars): an
-- n-gon with free diameters is flexible, so the Henneberg proof must not go
-- through without the diameter hypotheses.
import ChiquipoliFamily.A32
namespace Chiquipoli.Family.A32
open Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family
theorem bad (z : ℝ) (hsz : 0 < Real.sin z) (h₁ : clo ≤ Real.cos z) (h₂ : Real.cos z ≤ chi)
    (hl : L z ≠ 0) (w : Cfg 32) (hs : ∀ i, (dataOf (P z) (L z) ea eb).sideD w 0 i = 0) :
    (dataOf (P z) (L z) ea eb).R w := by
  exact Ieq_imp_R z hsz h₁ h₂ hl w ⟨hs, fun e => by simp [Data.diamD]⟩
end Chiquipoli.Family.A32
