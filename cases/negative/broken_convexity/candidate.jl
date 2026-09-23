# NEGATIVE CONTROL: A16 with vertex p_1 pushed deep inward, destroying strict
# convexity. The framework MUST reject this (convexity block :FAIL).
# `:expect => :reject` — the validator checks that at least one block fails.

let
    base = A16Certificate.coordinates(A16Certificate.z_nominal)   # 16×2 BigFloat
    P = copy(base)
    # pull p_1 toward the interior (centroid ≈ (0, 1/2)); breaks the left-turn.
    P[2,1] = base[2,1]*big"0.2"
    P[2,2] = base[2,2]*big"0.2" + big"0.45"
    coords = function (t)
        return [interval(P[i,j]) for i in 1:16, j in 1:2]
    end
    Candidate(
        "neg-broken-convexity", 16, coords, nothing,
        A16Certificate.ACTIVE_EDGES,
        Dict{Symbol,Any}(
            :reference => "perturbation of A16 (negative control)",
            :problem => "invalid: non-convex",
            :status_literature => "N/A (synthetic negative control)",
            :expect => :reject,
            :targets => "convexity",
        ),
    )
end
