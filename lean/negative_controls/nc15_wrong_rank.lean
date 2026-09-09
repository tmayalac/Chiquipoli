-- NEGATIVE CONTROL. Must FAIL to compile.
-- Claims rank D(e,d) = 31, i.e. that LICQ holds. It does not: the kernel is
-- exactly 3-dimensional, so the rank is 33 - 3 = 30. LICQ failing is the whole
-- reason Theorem 3.5 has to tolerate a multiplier family rather than a unique
-- multiplier vector, so this must not go through.
import ChiquipoliLean
namespace Chiquipoli.FirstOrder
open Module
theorem bad (z : ℝ) (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) :
    finrank ℝ (LinearMap.range (jacA16 z)) = 31 := by
  have hker : finrank ℝ (LinearMap.ker (jacA16 z)) = 3 := by
    rw [ker_jacA16 z hF hsz hcb,
        LinearMap.finrank_range_of_inj (rigidMap_injective z hsz hcb)]
    simp
  have h := LinearMap.finrank_range_add_finrank_ker (jacA16 z)
  rw [hker, finrank_domain] at h
  omega
end Chiquipoli.FirstOrder
