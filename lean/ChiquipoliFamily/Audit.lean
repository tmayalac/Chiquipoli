/-
Axiom audit of the family layer. Not imported by the library: `verify_family.sh`
compiles it and requires every theorem below to depend only on Lean's three
standard axioms `[propext, Classical.choice, Quot.sound]`.
-/
import ChiquipoliFamily

-- proved once, for every n
#print axioms Chiquipoli.Family.tbound
#print axioms Chiquipoli.Family.det_lb
#print axioms Chiquipoli.Family.sqd_ub
#print axioms Chiquipoli.Family.pin_bar
#print axioms Chiquipoli.Family.henneberg_step
#print axioms Chiquipoli.Family.small_of_lt
#print axioms Chiquipoli.Family.bars_of_Ieq
#print axioms Chiquipoli.Family.mult_of_stationary

-- A16, re-derived by the family pipeline
#print axioms Chiquipoli.Family.A16.Fc_root
#print axioms Chiquipoli.Family.A16.convexOrdered
#print axioms Chiquipoli.Family.A16.small
#print axioms Chiquipoli.Family.A16.equilateral
#print axioms Chiquipoli.Family.A16.active_eq
#print axioms Chiquipoli.Family.A16.stationary
#print axioms Chiquipoli.Family.A16.lam_pos
#print axioms Chiquipoli.Family.A16.Ieq_imp_R
#print axioms Chiquipoli.Family.A16.locally_maximal
#print axioms Chiquipoli.Family.A16.locally_maximal_at
#print axioms Chiquipoli.Family.A16.Fc_root_unique_search
#print axioms Chiquipoli.Family.A16.cos_mem_of_search
#print axioms Chiquipoli.Family.A16.locally_maximal_unique

-- A32
#print axioms Chiquipoli.Family.A32.Fc_root
#print axioms Chiquipoli.Family.A32.convexOrdered
#print axioms Chiquipoli.Family.A32.small
#print axioms Chiquipoli.Family.A32.equilateral
#print axioms Chiquipoli.Family.A32.active_eq
#print axioms Chiquipoli.Family.A32.stationary
#print axioms Chiquipoli.Family.A32.lam_pos
#print axioms Chiquipoli.Family.A32.Ieq_imp_R
#print axioms Chiquipoli.Family.A32.locally_maximal
#print axioms Chiquipoli.Family.A32.locally_maximal_at
#print axioms Chiquipoli.Family.A32.Fc_root_unique_search
#print axioms Chiquipoli.Family.A32.cos_mem_of_search
#print axioms Chiquipoli.Family.A32.locally_maximal_unique
