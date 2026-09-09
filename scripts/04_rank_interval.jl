include(joinpath(@__DIR__, "_bootstrap.jl"))

function run_rank_interval(; radius=big"1e-28")
    setprecision(BigFloat, 256)
    Z = interval(z_nominal-radius, z_nominal+radius)
    A = build_jacobian(Z)
    M = A[ROWS_MINOR,COLS_MINOR]
    assert_guaranteed(Z, "certificate box Z_cert")
    assert_guaranteed(M, "30x30 minor of D(e,d)")
    minor_pass,bound,_,_ = regularity_test(M)

    rigid_theorem = rigid_annihilation_identities()
    rank_upper_pass = rigid_theorem.translations && rigid_theorem.rotation
    final_pass = minor_pass && rank_upper_pass

    println("minor rows = ", ROWS_MINOR)
    println("minor columns = ", COLS_MINOR)
    println("regularity bound = ", bound)
    println("minor regular PASS = ", minor_pass)
    println("rigid-motion rank upper bound = algebraic theorem")
    println("rigid-motion explanation = ", rigid_theorem.explanation)
    println("rank 30 PASS = ", final_pass)

    return (pass=final_pass, bound=bound,
            minor_pass=minor_pass, rank_upper_pass=rank_upper_pass)
end

(abspath(PROGRAM_FILE) == @__FILE__) && run_rank_interval()
