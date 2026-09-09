include(joinpath(@__DIR__, "_bootstrap.jl"))

function run_geometry_interval(; radius=big"1e-28")
    setprecision(BigFloat, 256)
    Z = interval(z_nominal-radius, z_nominal+radius)
    assert_guaranteed(Z, "certificate box Z_cert")
    supports = support_determinants(Z)
    assert_guaranteed([v for (_,_,v) in supports], "support determinants")
    lower = [(i,j,inf(v)) for (i,j,v) in supports]
    worst_support = lower[argmin(last.(lower))]
    support_pass = worst_support[3] > 0

    inactive = inactive_pairs(Z)
    assert_guaranteed([v for (_,_,v) in inactive], "inactive squared distances")
    upper = [(i,j,sup(v)) for (i,j,v) in inactive]
    worst_inactive = upper[argmax(last.(upper))]
    inactive_pass = worst_inactive[3] < 1

    # Rigorous lower bound on the geometric margin. worst_inactive[3] is a
    # certified UPPER bound on the largest inactive squared distance; taking
    # 1 - sqrt(.) with outward interval rounding and extracting the infimum
    # yields a directed (rounded-down) lower bound on the true margin, rather
    # than a bare BigFloat that happens to round to nearest.
    margin_interval = 1 - sqrt(interval(worst_inactive[3]))
    margin = inf(margin_interval)

    println("worst support = ", worst_support)
    println("strict convexity PASS = ", support_pass)
    println("worst inactive pair = ", worst_inactive)
    println("inactive PASS = ", inactive_pass)
    println("distance margin (certified lower bound) = ", margin)

    # Active distances are diagnostics only until exact identities are written.
    p = coordinates(Z)
    println("active squared-distance diagnostics:")
    for e in ACTIVE_EDGES
        println(e, " => ", sqdist(p,e[1],e[2]))
    end
    return (support_pass=support_pass, inactive_pass=inactive_pass,
            worst_support=worst_support, worst_inactive=worst_inactive,
            margin=margin)
end

(abspath(PROGRAM_FILE) == @__FILE__) && run_geometry_interval()
