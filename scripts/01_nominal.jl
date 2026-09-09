include(joinpath(@__DIR__, "_bootstrap.jl"))

function run_nominal()
    setprecision(BigFloat, 256)
    z = z_nominal
    p = coordinates(z)
    ell = side_length(z)
    A = build_jacobian(z)
    println("z = ", z)
    println("ell = ", ell)
    println("perimeter = ", 16ell)
    println("floating rank = ", rank(Float64.(A)))
    println("coordinates:")
    for i in 0:15
        println(i, "  ", p[i+1,1], "  ", p[i+1,2])
    end
end

(abspath(PROGRAM_FILE) == @__FILE__) && run_nominal()
