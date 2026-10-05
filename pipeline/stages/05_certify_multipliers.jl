include(joinpath(@__DIR__, "_bootstrap.jl"))

function run_multipliers_interval(; radius=big"1e-28")
    setprecision(BigFloat, 256)
    Z = interval(z_nominal-radius, z_nominal+radius)
    A = build_jacobian(Z)
    M = normalized_matrix(A)
    g = objective_covector(eltype(A))

    # The paper normalises the one-parameter multiplier family by
    # lambda_{0,9} = 1/5 EXACTLY (Section 6, eq. for the normalisation, and
    # Table S2's caption, Online Resource 1). `interval(big"0.2")` is the thin interval at the
    # nearest 256-bit BigFloat to 1/5, which is NOT 1/5: it differs by about
    # 1e-78. Certifying with it proves the statement for fl(1/5) rather than
    # for the rational the paper names. Enclosing 1/5 with directed rounding
    # instead makes the certified statement literally the paper's, and costs
    # nothing: Krawczyk certifies the solution for EVERY right-hand side in
    # the box, hence in particular for the exact 1/5.
    onefifth = interval(BigFloat(1//5, RoundDown), BigFloat(1//5, RoundUp))
    @assert inf(onefifth) <= big"0.2" <= sup(onefifth)
    b = vcat(g[COLS_MINOR], onefifth)

    assert_guaranteed(Z, "certificate box Z_cert")
    assert_guaranteed(M, "normalized stationarity matrix")
    assert_guaranteed(b, "normalized right-hand side")

    reg_pass, reg_bound, _, _ = regularity_test(M)
    sol = krawczyk_linear(M,b)

    println("normalized matrix regularity bound = ", reg_bound)
    println("normalized matrix PASS = ", reg_pass)
    println("Krawczyk PASS = ", sol.pass)

    if !(reg_pass && sol.pass)
        # Same fields as the success return, so a failure is reported as a
        # FAIL gate in the certificate instead of crashing certify_a16.jl when it
        # reads a field that is not there (2026-09 external audit, D02).
        return (pass=false, reason="normalized multiplier solve failed",
                lambda_lower=nothing, alpha_sum=nothing,
                alpha_balance_diagnostic=false, multiplier_enclosure=nothing,
                omitted_bound=nothing, normalized_regularity_bound=reg_bound, Z=Z)
    end

    Y = sol.enclosure
    assert_guaranteed(Y, "Krawczyk multiplier enclosure")
    lambda_lower = minimum(inf(Y[i]) for i in 17:31)
    positivity_pass = lambda_lower > 0

    # DIAGNOSTIC ONLY, NOT A CERTIFICATE PILLAR (see docs/guide/provenance-mapping.md,
    # Bloque (C)). The paper itself calls sum(alpha)=-n "a check on computed
    # multipliers" (Section 3, remark after
    # prop:first-order-no-ascent), not a hypothesis of any theorem. It is
    # also not an independent fact to verify here: column 33 of D(e,d) (the
    # ell-row) is -1 on every side row and 0 on every diameter row, and that
    # row is already one of the 30 equations solved exactly by the Krawczyk
    # system above (COLS_MINOR includes column 33). So sum(alpha)=-16 is an
    # automatic algebraic consequence of `reg_pass && sol.pass`, already
    # exact given M's certified regularity -- it does not need, and does not
    # get, independent certification from this containment check. Checking
    # `in_interval(-16, alpha_sum)` only shows -16 is a *possible* value of
    # the sum; it is not by itself a proof of exact equality, and is not
    # treated as a gate on `final_pass` below.
    alpha_sum = sum(Y[i] for i in 1:16)
    alpha_balance_diagnostic = in_interval(-16, alpha_sum)

    # The selected equations imply that the residual is supported only on
    # x_1,y_1,x_8. Rigid invariance gives three homogeneous equations for
    # those three residual entries. Q regular implies the residual is zero.
    Q = omitted_residual_matrix(Z)
    assert_guaranteed(Q, "rigid-motion matrix Q on the omitted coordinates")
    omitted_pass, omitted_bound, _, _ = regularity_test(Q)

    println("sum alpha enclosure = ", alpha_sum)
    println("sum alpha contains -16 (diagnostic, not a gate) = ", alpha_balance_diagnostic)
    println("minimum lambda lower bound = ", lambda_lower)
    println("all lambdas positive PASS = ", positivity_pass)
    println("omitted residual matrix bound = ", omitted_bound)
    println("omitted equations recovered PASS = ", omitted_pass)

    final_pass =
        reg_pass && sol.pass && positivity_pass && omitted_pass

    return (pass=final_pass, reason="", lambda_lower=lambda_lower,
            alpha_sum=alpha_sum, alpha_balance_diagnostic=alpha_balance_diagnostic,
            multiplier_enclosure=Y, omitted_bound=omitted_bound,
            normalized_regularity_bound=reg_bound, Z=Z)
end

(abspath(PROGRAM_FILE) == @__FILE__) && run_multipliers_interval()
