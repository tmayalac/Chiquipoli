-- NEGATIVE CONTROL. Must FAIL to compile.
-- Claims the Gram map (and hence the invertibility Lemma 3.4's implicit
-- function theorem step needs) is injective for ANY configuration, with no
-- distinctness hypothesis. It is not: at a configuration collapsed to a
-- single point, T3 = J∘p vanishes identically and the kernel picks up every
-- pure rotation, so injectivity fails. `gramLM_injective`'s actual proof
-- needs exactly the hypothesis omitted here.
import ChiquipoliLean
namespace Chiquipoli.FirstOrder
theorem bad {n : ℕ} (p : Fin n → ℝ × ℝ) : Function.Injective (gramLM p) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun d hd => ?_
  rw [LinearMap.mem_ker, gramLM_apply] at hd
  exact gram_nondegenerate (by assumption) (congrArg Prod.fst hd)
    (congrArg (Prod.fst ∘ Prod.snd) hd) (congrArg (Prod.snd ∘ Prod.snd) hd)
end Chiquipoli.FirstOrder
