# The general certifier refuses a malformed exact-identity hook.
# Included by runtests.jl inside the outer "Chiquipoli" testset; run the
# whole suite with `make test` (a file on its own lacks the shared setup).

# ---------------------------------------------------------------------------
# The Chebyshev basis and the two copies of the polynomial utilities.
#
# A typo in the T/U recurrence is already caught: inverting one sign there fails
# 39 assertions across four testsets, because the rational coordinate table
# would stop reproducing the trigonometric one. But it is caught downstream, far
# from the cause. These check the basis where it is defined, so a failure names
# the culprit.
#
# `A16Certificate` and `ExactIdentity` each carry their own copy of the rational
# polynomial utilities. They are deliberately independent — the second engine
# was written to be reusable without pulling in the A16 specialisation — but two
# copies can drift apart silently, and every exact identity in the package rests
# on both. The second testset holds them to each other.
# ---------------------------------------------------------------------------
@testset "certify rejects a malformed exact-identity hook" begin
    # `meta[:exact]` is supplied by the candidate, so its output is input to the
    # exact_identities block rather than a result of it, and its shape has to be
    # checked before its content is read. It was not: `all(f, [])` is true in
    # Julia, so a candidate returning two empty vectors was reported
    # ":PROVEN  0 sides + 0 active diameters" with structural_pass true — the
    # strongest label in the report, awarded for proving nothing. A short vector
    # was as bad: two statuses for a 16-gon passed while the other twenty nine
    # equalities went unexamined. No shipped candidate is affected; every one of
    # them returns the right lengths. The framework accepted the wrong ones.
    setprecision(BigFloat, 256)
    BF(x) = interval(BigFloat(x))
    aa = BF(1) / sqrt(BF(2)) / BF(2)
    square = t -> [aa aa; -aa aa; -aa -aa; aa -aa]
    exact_block(r) = r.blocks[findfirst(b -> b.name == "exact_identities", r.blocks)]

    for (why, hook) in [("empty",        sbox -> (Symbol[], Symbol[])),
                        ("too few",      sbox -> ([:PROVED, :PROVED], [:PROVED])),
                        ("too many",     sbox -> (fill(:PROVED, 9), fill(:PROVED, 2))),
                        ("diameters off", sbox -> (fill(:PROVED, 4), fill(:PROVED, 5)))]
        r = certify(Candidate("malformed-" * why, 4, square, nothing, [(0,2), (1,3)],
                              Dict{Symbol,Any}(:exact => hook)))
        @test exact_block(r).status == :FAIL
        @test !structural_pass(r)
    end

    # and a well-formed hook is still accepted
    r = certify(Candidate("well-formed", 4, square, nothing, [(0,2), (1,3)],
                          Dict{Symbol,Any}(:exact => sbox -> (fill(:PROVED, 4),
                                                              fill(:UNCONDITIONAL, 2)))))
    @test exact_block(r).status == :PROVEN
end
