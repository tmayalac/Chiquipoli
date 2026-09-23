# Strict convexity and the inactive pairs: the quantities of Proposition 6.2(3)
# and (4), as functions of the constructor parameter.
#
# Part of module A16Certificate (src/A16Certificate.jl), which includes this
# file; it is not meant to be loaded on its own.

function support_determinants(z)
    p = coordinates(z)
    vals = Tuple{Int,Int,typeof(z)}[]
    for i in 0:15
        ip = mod(i+1,16)
        ex = p[ip+1,1]-p[i+1,1]
        ey = p[ip+1,2]-p[i+1,2]
        for j in 0:15
            (j == i || j == ip) && continue
            qx = p[j+1,1]-p[i+1,1]
            qy = p[j+1,2]-p[i+1,2]
            push!(vals,(i,j,ex*qy-ey*qx))
        end
    end
    return vals
end

function inactive_pairs(z)
    p = coordinates(z)
    active = Set(ACTIVE_EDGES)
    vals = Tuple{Int,Int,typeof(z)}[]
    for i in 0:15, j in (i+1):15
        (i,j) in active && continue
        push!(vals,(i,j,sqdist(p,i,j)))
    end
    return vals
end
