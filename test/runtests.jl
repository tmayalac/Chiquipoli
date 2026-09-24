using Test
include(joinpath(@__DIR__,"..","src","A16Certificate.jl"))
using .A16Certificate
include(joinpath(@__DIR__,"..","src","ExactIdentity.jl"))
using .ExactIdentity
include(joinpath(@__DIR__,"..","src","SmallPolygons.jl"))
using .SmallPolygons
include(joinpath(@__DIR__,"..","cases","exact_coords.jl"))
using SHA
include(joinpath(@__DIR__,"..","cases","optigon_exact.jl"))
include(joinpath(@__DIR__,"fixtures","optigon_reference.jl"))
using IntervalArithmetic
using LinearAlgebra
using SHA
using Random

# ---- General framework: literature benchmark ------------------------------
# Declared at top level: `const` is not allowed inside the outer testset.
const LITROOT = normpath(joinpath(@__DIR__, "..", "cases"))
loadcand(rel) = include(joinpath(LITROOT, rel, "candidate.jl"))

# One outer testset, so a failure anywhere does not abort the run. Without it a
# top-level @testset throws when it finishes and every later testset is
# skipped: a broken constructor used to stop the suite after two of twelve.
@testset verbose = true "Chiquipoli" begin

    include("constructor.jl")
    include("framework_guards.jl")
    include("exact_algebra.jl")
    include("certificate_stages.jl")
    include("literature.jl")
    include("regressions.jl")
    include("optigon.jl")

end  # @testset "Chiquipoli"
