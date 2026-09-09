using LinearAlgebra
setprecision(BigFloat,128)
a = inv(2sqrt(big(2)))
p = [a a; -a a; -a -a; a -a]
ell = inv(sqrt(big(2)))
active = [(1,3),(2,4)]
A = zeros(BigFloat,6,9)
for i in 1:4
    j = mod1(i+1,4)
    s = (p[j,:]-p[i,:])/ell
    A[i,2i-1:2i] .= -s
    A[i,2j-1:2j] .= s
    A[i,9] = -1
end
for (k,(i,j)) in enumerate(active)
    u = p[j,:]-p[i,:]
    A[4+k,2i-1:2i] .= -u
    A[4+k,2j-1:2j] .= u
end
println("rank = ",rank(Matrix{Float64}(A)))
println("nullity = ",9-rank(Matrix{Float64}(A)))
