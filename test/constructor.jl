# The nominal constructor, its Jacobian, and interval smoke tests.
# Included by runtests.jl inside the outer "Chiquipoli" testset; run the
# whole suite with `make test` (a file on its own lacks the shared setup).

@testset "Static conventions" begin
    @test length(ACTIVE_EDGES) == 15
    @test length(ROWS_MINOR) == 30
    @test length(COLS_MINOR) == 30
    @test OMITTED_COLUMNS == [3,4,17]
end

@testset "Nominal constructor" begin
    setprecision(BigFloat,256)
    z = z_nominal
    p = coordinates(z)
    @test size(p) == (16,2)
    @test p[1,1] == 0
    @test p[1,2] == 0
    @test p[9,1] == 0
    @test p[9,2] == 1
    @test abs(Ffun(z)) < big"1e-25"
    @test abs(Fprime(z)) > big"1e-3"
end

@testset "Jacobian assembly" begin
    z = z_nominal
    A = build_jacobian(z)
    @test size(A) == (31,33)
    rx,ry,rr = rigid_vectors(z)
    @test maximum(abs.(A*rx)) < big"1e-30"
    @test maximum(abs.(A*ry)) < big"1e-30"
    @test maximum(abs.(A*rr)) < big"1e-25"
    @test rigid_annihilation_identities().translations
    @test rigid_annihilation_identities().rotation
end

@testset "Interval smoke tests" begin
    Z = interval(z_nominal-big"1e-28",z_nominal+big"1e-28")
    @test !in_interval(0, Fprime(Z))
    A = build_jacobian(Z)
    @test size(A[ROWS_MINOR,COLS_MINOR]) == (30,30)
    @test size(normalized_matrix(A)) == (31,31)
    @test size(omitted_residual_matrix(Z)) == (3,3)
end
