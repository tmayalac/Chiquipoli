/-
Axiom audit.

A Lean proof that compiles is not automatically a proof of anything useful: it
could rest on `sorryAx` (an admitted goal). `#print axioms` is the check that
matters. Every theorem below must report exactly

    [propext, Classical.choice, Quot.sound]

which are the three standard axioms of Lean's classical foundation — and, in
particular, **not** `sorryAx`.

Run `lake env lean ChiquipoliLean/Audit.lean` to see the report, or
`scripts/verify.sh` to have it checked automatically.
-/
import ChiquipoliLean

namespace Chiquipoli

-- The multiple-angle bridge.
#print axioms cos_7
#print axioms sin_7

-- The generated polynomial layer agrees with the hand-written constructor.
#print axioms red3
#print axioms red13
#print axioms Fc_cos_eq_Ffun

-- Representative identities: one unconditional side, one conditional side,
-- one active diameter.
#print axioms side_0_1
#print axioms side_3_4
#print axioms side_12_13
#print axioms diam_3_12

-- Existence of the constructor root, and its uniqueness in the bracket.
#print axioms Fc_root_exists
#print axioms exists_constructor_root
#print axioms dFc_lower_bound
#print axioms hasDerivAt_Fc
#print axioms Fc_strictMonoOn
#print axioms Fc_root_unique
#print axioms Fc_root_existsUnique
#print axioms dFc_lower_bound_wide
#print axioms Fc_root_existsUnique_search
#print axioms constructor_root_unique_in_search
#print axioms constructor_root_existsUnique_article_search

-- The inactive margin and the diameter.
#print axioms inactive_4_12
#print axioms lt_one_4_12
#print axioms sqd_le_one
#print axioms diameter_eq_one

-- Strict convexity and the labelled cyclic order.
#print axioms convD_0_2
#print axioms cross_pos

-- Strictly positive multipliers and the stationarity identity.
#print axioms alpha_sum
#print axioms gradx_0
#print axioms stationarity_vertex
#print axioms mL0_pos
#print axioms multipliers_certified

-- I_eq = R_eq : the rigid motions are in the kernel, and nothing else is.
#print axioms dsq_rigid
#print axioms pivNe1
#print axioms reduced_kernel
#print axioms p1_fst_ne
#print axioms kernel_is_rigid
#print axioms exists_constructor_root_sin_pos

-- Strictly positive multipliers and the stationarity identity.

-- I_eq = R_eq : the rigid motions are in the kernel, and nothing else is.

-- The headline theorem.
#print axioms all_sides
#print axioms all_active_diameters
#print axioms A16_exists

-- The assembled certificate: the statement a referee should read.
#print axioms A16_certificate

-- Theorem 3.5, algebraic core: the abstract results and their discharge at A16.
#print axioms Chiquipoli.FirstOrder.no_ascent
#print axioms Chiquipoli.FirstOrder.multiplier_balance
#print axioms Chiquipoli.FirstOrder.active_equality
#print axioms Chiquipoli.FirstOrder.no_admissible_direction
#print axioms Chiquipoli.FirstOrder.no_admissible_direction_paper
#print axioms Chiquipoli.FirstOrder.A16_lam_pos
#print axioms Chiquipoli.FirstOrder.A16_Ieq_imp_R
#print axioms Chiquipoli.FirstOrder.A16_multiplier_identity
#print axioms Chiquipoli.FirstOrder.A16_no_admissible_direction

-- Proposition 3.8 and the Section 4 examples.
#print axioms Chiquipoli.FirstOrder.increases_to_the_right
#print axioms Chiquipoli.FirstOrder.not_isLocalMax
#print axioms Chiquipoli.FirstOrder.square_lam_pos
#print axioms Chiquipoli.FirstOrder.square_multiplier_identity
#print axioms Chiquipoli.FirstOrder.square_Ieq_imp_R
#print axioms Chiquipoli.FirstOrder.square_no_admissible_direction
#print axioms Chiquipoli.FirstOrder.rho_equilateral
#print axioms Chiquipoli.FirstOrder.rho_small
#print axioms Chiquipoli.FirstOrder.rho_diameter
#print axioms Chiquipoli.FirstOrder.rho_hasDerivAt
#print axioms Chiquipoli.FirstOrder.rhombus_perimeter_increases
#print axioms Chiquipoli.FirstOrder.rhombus_not_isLocalMax

-- Proposition 6.2(2): the certified side length and perimeter.
#print axioms Chiquipoli.cos_root_tight
#print axioms Chiquipoli.sq_side_bounds
#print axioms Chiquipoli.side_length_bounds
#print axioms Chiquipoli.perimeter_bounds

-- Proposition 6.2(6): rank D(e,d) = 30, by rank-nullity.
#print axioms Chiquipoli.FirstOrder.A16_kernel
#print axioms Chiquipoli.FirstOrder.rigidMap_injective
#print axioms Chiquipoli.FirstOrder.ker_jacA16
#print axioms Chiquipoli.FirstOrder.rank_eq_thirty

-- Lemma 3.6: the nondegeneracy the implicit function theorem consumes.
#print axioms Chiquipoli.FirstOrder.rigid_indep
#print axioms Chiquipoli.FirstOrder.gram_nondegenerate
#print axioms Chiquipoli.FirstOrder.rigid_inter_perp

-- Lemma 3.6, via the implicit function theorem: g exists, g(p) = id, and g is
-- strictly differentiable at p.
#print axioms Chiquipoli.FirstOrder.f2CLM_base_invertible
#print axioms Chiquipoli.FirstOrder.g_at_p
#print axioms Chiquipoli.FirstOrder.g_hasStrictFDerivAt
#print axioms Chiquipoli.FirstOrder.g_tendsto
#print axioms Chiquipoli.FirstOrder.g_eventually_iff

-- Theorem 3.5, the blow-up half (steps A-E). The feasible set, openness of the
-- convexity and margin conditions, the first-order limits, invariance under
-- Euclidean motions with the slice normalisation, and the assembly.
#print axioms Chiquipoli.Feasible.Keq_iff
#print axioms Chiquipoli.Feasible.eC_eq_zero_iff
#print axioms Chiquipoli.Feasible.dC_nonpos_iff
#print axioms Chiquipoli.Feasible.isOpen_convexOrdered
#print axioms Chiquipoli.Feasible.eventually_dC_neg_of_tendsto
#print axioms Chiquipoli.Feasible.eC_expand
#print axioms Chiquipoli.Feasible.dC_expand
#print axioms Chiquipoli.Feasible.eD_eq_zero_of_blowup
#print axioms Chiquipoli.Feasible.dD_nonpos_of_blowup
#print axioms Chiquipoli.Feasible.ip_rot
#print axioms Chiquipoli.Feasible.isFeasible_move
#print axioms Chiquipoli.Feasible.isFeasibleConvex_move
#print axioms Chiquipoli.Feasible.tendsto_normCfg
#print axioms Chiquipoli.Feasible.eventually_phiGeom_zero
#print axioms Chiquipoli.Feasible.slice_of_generators
#print axioms Chiquipoli.Feasible.no_blowup_sequence
#print axioms Chiquipoli.Feasible.eventually_no_better
#print axioms Chiquipoli.Feasible.eventually_congruent_of_no_worse
#print axioms Chiquipoli.Feasible.thm_3_5
#print axioms Chiquipoli.Feasible.thm_3_5_le

-- The chain closed: from the certified A16 coordinates to local maximality.
#print axioms Chiquipoli.Feasible.A16_bridge
#print axioms Chiquipoli.Feasible.A16_isFeasibleConvex
#print axioms Chiquipoli.Feasible.A16_active
#print axioms Chiquipoli.Feasible.A16_vertices_distinct
#print axioms Chiquipoli.Feasible.exists_A16_root_in_Ioo_pi
#print axioms Chiquipoli.Feasible.A16_strict_local_max
#print axioms Chiquipoli.Feasible.A16_locally_maximal

-- Proposition 4.2: the square, closed the same way.
#print axioms Chiquipoli.Feasible.square_bridge
#print axioms Chiquipoli.Feasible.square_isFeasibleConvex
#print axioms Chiquipoli.Feasible.square_strict_local_max

end Chiquipoli
