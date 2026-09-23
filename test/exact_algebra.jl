# Exact algebra in Q[c]: Chebyshev basis, polynomial engines, Lemma 6.1.
# Included by runtests.jl inside the outer "Chiquipoli" testset; run the
# whole suite with `make test` (a file on its own lacks the shared setup).

@testset "Chebyshev basis against its closed forms" begin
    T, U = chebyshev(12)
    ev(q, x) = (a = 0//1; for i in length(q):-1:1; a = a * x + q[i]; end; a)
    # low orders written out by hand
    @test ptrim(T[0]) == RPoly([1//1])
    @test ptrim(T[1]) == RPoly([0//1, 1//1])
    @test ptrim(T[2]) == RPoly([-1//1, 0//1, 2//1])          # 2c² − 1
    @test ptrim(T[3]) == RPoly([0//1, -3//1, 0//1, 4//1])    # 4c³ − 3c
    @test ptrim(U[0]) == RPoly([1//1])
    @test ptrim(U[1]) == RPoly([0//1, 2//1])                 # 2c
    @test ptrim(U[2]) == RPoly([-1//1, 0//1, 4//1])          # 4c² − 1
    @test ptrim(U[3]) == RPoly([0//1, -4//1, 0//1, 8//1])    # 8c³ − 4c
    # the defining trigonometric identities, at 256 bits
    setprecision(BigFloat, 256)
    for z in (big"0.31", big"1.27", big"2.03", z_nominal)
        c = cos(z); sn = sin(z)
        for k in 0:12
            tk = sum(BigFloat(T[k][i+1]) * c^i for i in 0:length(T[k])-1)
            @test abs(tk - cos(k*z)) < big"1e-60"
            uk = sum(BigFloat(U[k][i+1]) * c^i for i in 0:length(U[k])-1)
            @test abs(sn * uk - sin((k+1)*z)) < big"1e-60"
        end
    end
    # leading coefficients: T_k and U_k are 2^(k-1) and 2^k for k ≥ 1
    for k in 1:12
        @test ptrim(T[k])[end] == Rational{BigInt}(2)^(k-1)
        @test ptrim(U[k])[end] == Rational{BigInt}(2)^k
    end
end

@testset "the two polynomial engines agree" begin
    EI = ExactIdentity
    # A fixed seed on purpose: a randomised failure that cannot be reproduced is
    # worse than no test, and this file is part of a certification pipeline.
    rng = Random.Xoshiro(20260908)
    rnd(n) = RPoly([Rational{BigInt}(rand(rng, -9:9), rand(rng, 1:5)) for _ in 1:n])
    for _ in 1:40
        a = ptrim(rnd(rand(rng, 1:7))); b = ptrim(rnd(rand(rng, 1:7)))
        iszeropoly(b) && continue
        @test ptrim(padd(a, b))          == EI.ptrim(EI.padd(a, b))
        @test ptrim(psub(a, b))          == EI.ptrim(EI.psub(a, b))
        @test ptrim(pmul(a, b))          == EI.ptrim(EI.pmul(a, b))
        @test iszeropoly(a)              == EI.iszeropoly(a)
        qa, ra = pdivrem(a, b); qb, rb = EI.pdivrem(a, b)
        @test ptrim(qa) == EI.ptrim(qb) && ptrim(ra) == EI.ptrim(rb)
        # and the division is exact over Q: a = q*b + r, always
        @test ptrim(padd(pmul(qa, b), ra)) == ptrim(a)
    end
end

@testset "Exact polynomial arithmetic" begin
    a = RPoly([-1//1,0//1,1//1])  # c^2 - 1
    b = RPoly([-1//1,1//1])       # c - 1
    q,r = pdivrem(a,b)
    @test iszeropoly(r)
    @test ptrim(padd(pmul(q,b),r)) == ptrim(a)

    a2 = RPoly([0//1,0//1,1//1])  # c^2
    q2,r2 = pdivrem(a2,b)
    @test !iszeropoly(r2)
end

# The docstring of `_peval` warns against a refactor that would silently stop
# being an enclosure for coefficients past the 256-bit mantissa. This pins down
# that the SHIPPED conversion is outward at exactly that scale, so the warning
# can never quietly become a description of the code.
@testset "coefficient conversion stays an enclosure past the mantissa" begin
    setprecision(BigFloat, 256) do
        for q in (Rational{BigInt}(BigInt(2)^260 + 1, 1),
                  Rational{BigInt}(-(BigInt(2)^300) - 7, 1),
                  Rational{BigInt}(BigInt(2)^260 + 1, BigInt(3)))
            I = interval(BigFloat, q)
            @test inf(I) <= q <= sup(I)          # a true enclosure
            @test isguaranteed(I)
        end
        # Horner over such coefficients inherits the property.
        big = RPoly([Rational{BigInt}(BigInt(2)^260 + 1, 1), 1//1])
        v = ExactIdentity._peval(big, interval(BigFloat, 1//1))
        @test inf(v) <= (BigInt(2)^260 + 2) <= sup(v)
        # ...and the banned refactor really does fail, which is why it is banned.
        n = BigInt(2)^260 + 1
        bad = interval(BigFloat(n)) / interval(BigFloat(BigInt(1)))
        @test !(inf(bad) <= n <= sup(bad))
    end
end

@testset "Exact side and diameter identities" begin
    for i in 0:15
        j = mod(i+1,16)
        cert = exact_identity_certificate(i, j, side_target_poly())
        @test cert.proved
        @test cert.reconstruction_ok
    end
    for (i,j) in ACTIVE_EDGES
        cert = exact_identity_certificate(i, j, diameter_target_poly())
        @test cert.proved
        @test cert.reconstruction_ok
    end
    # Discrimination check: an inactive pair must NOT be exactly a diameter.
    inactive_sample = [(4,12),(0,4),(1,10),(2,13)]
    for (i,j) in inactive_sample
        cert = exact_identity_certificate(i, j, diameter_target_poly())
        @test !cert.proved
    end
end

@testset "Numeric and exact constructors agree" begin
    # src/a16/ transcribes the constructor TWICE: once
    # trigonometrically (Xfun/Yfun, used by every interval gate) and once as
    # rational polynomials (_XC/_YC, used by all the exact algebra). Nothing
    # used to check that the two agree, so breaking one left the other proving
    # 31 identities about a different polygon.
    setprecision(BigFloat, 256)
    XC, YC = A16Certificate._XC, A16Certificate._YC
    horner(q, x) = (a = zero(x); for i in length(q):-1:1; a = a * x + BigFloat(q[i]); end; a)
    z = z_nominal; c = cos(z); s = sin(z); P = coordinates(z)
    @test length(XC) == 16 && length(YC) == 16
    for k in 0:15
        # vertex k is (sin z * XC_k(cos z), YC_k(cos z))
        @test abs(s * horner(XC[k+1], c) - P[k+1, 1]) < big"1e-70"
        @test abs(horner(YC[k+1], c) - P[k+1, 2]) < big"1e-70"
    end
end
