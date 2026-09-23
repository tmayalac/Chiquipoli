module A16Certificate

using LinearAlgebra
using IntervalArithmetic

export ACTIVE_EDGES, ROWS_MINOR, COLS_MINOR, OMITTED_COLUMNS,
       z_nominal, search_bounds, Xfun, Xprime, Yfun,
       Ffun, Fprime, coordinates, side_length, sqdist,
       build_jacobian, support_determinants, inactive_pairs,
       interval_abs_bound, regularity_test, krawczyk_linear,
       rigid_vectors, objective_covector, normalized_matrix,
       omitted_residual_matrix, rigid_annihilation_identities,
       assert_guaranteed,
       RPoly, ptrim, padd, psub, pmul, pscale, psq, pdivrem, iszeropoly,
       chebyshev, sqdist_poly, side_target_poly, diameter_target_poly,
       Fc_poly, exact_identity_certificate

# The module is split by role; `include` inserts each file here verbatim, so
# the module is the same code as when it was one file. Order matters only for
# the constants computed at load time at the end of exact_algebra.jl.
include(joinpath("a16", "data.jl"))
include(joinpath("a16", "guarantees.jl"))
include(joinpath("a16", "constructor.jl"))
include(joinpath("a16", "geometry.jl"))
include(joinpath("a16", "linear_algebra.jl"))
include(joinpath("a16", "exact_algebra.jl"))

end
