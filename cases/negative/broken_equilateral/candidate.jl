# NEGATIVE CONTROL: A16 with vertex p_1 nudged so the sides are no longer all
# equal. The framework MUST reject this (equilaterality block :FAIL, since the
# side² enclosures become disjoint — a rigorous refutation of equality).

let
    base = A16Certificate.coordinates(A16Certificate.z_nominal)
    P = copy(base)
    P[2,1] = base[2,1] + big"0.02"      # small tangential nudge, stays convex
    P[2,2] = base[2,2] + big"0.02"
    coords = function (t)
        return [interval(P[i,j]) for i in 1:16, j in 1:2]
    end
    Candidate(
        "neg-broken-equilateral", 16, coords, nothing,
        A16Certificate.ACTIVE_EDGES,
        Dict{Symbol,Any}(
            :reference => "perturbation of A16 (negative control)",
            :problem => "invalid: not equilateral",
            :status_literature => "N/A (synthetic negative control)",
            :expect => :reject,
            :targets => "equilaterality",
        ),
    )
end
