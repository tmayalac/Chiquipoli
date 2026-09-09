# NEGATIVE CONTROL: A16 scaled by 1.05, so the diameter is 1.05, not 1. The
# polygon is still convex and equilateral, but the declared active diameters no
# longer equal 1 (and an inactive pair now exceeds 1). The framework MUST reject
# this (active_graph+margin block :FAIL).

let
    base = A16Certificate.coordinates(A16Certificate.z_nominal)
    P = base .* big"1.05"
    coords = function (t)
        return [interval(P[i,j]) for i in 1:16, j in 1:2]
    end
    Candidate(
        "neg-wrong-diameter", 16, coords, nothing,
        A16Certificate.ACTIVE_EDGES,
        Dict{Symbol,Any}(
            :reference => "perturbation of A16 (negative control)",
            :problem => "invalid: diameter ≠ 1",
            :status_literature => "N/A (synthetic negative control)",
            :expect => :reject,
            :targets => "active_graph+margin",
        ),
    )
end
