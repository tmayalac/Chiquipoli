if !isdefined(Main, :A16Certificate)
    include(joinpath(@__DIR__, "..", "..", "src", "A16Certificate.jl"))
end
using .A16Certificate
using LinearAlgebra
using IntervalArithmetic
