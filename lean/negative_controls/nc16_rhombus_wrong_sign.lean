-- NEGATIVE CONTROL. Must FAIL to compile.
-- Claims the rhombus deformation increases the perimeter for delta < 0 too.
-- It does not: the first variation is 16*delta/sqrt 41, which is negative
-- there, so the perimeter strictly DEcreases. If this compiled, the sign of
-- the first variation would be carrying no information and Proposition 3.8
-- would be vacuous.
import ChiquipoliLean
namespace Chiquipoli.FirstOrder
theorem bad (δ : ℝ) (hδ : δ < 0) :
    ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), rhoL δ 0 < rhoL δ t :=
  increases_to_the_right (rho_hasDerivAt δ) (by positivity)
end Chiquipoli.FirstOrder
