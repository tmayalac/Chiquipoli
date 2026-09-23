# The Bingane-Audet constructor at n = 16: the constructor equation F and its
# derivative, the side length, and the sixteen vertices.
#
# Part of module A16Certificate (src/A16Certificate.jl), which includes this
# file; it is not meant to be loaded on its own.

function search_bounds(T=BigFloat)
    p = T(pi)
    two = _lit(p, 2); sixteen = _lit(p, 16)
    return (two*asin(sin(p/sixteen)/two), p/sixteen)
end

function Xfun(t)
    two = _lit(t, 2); four = _lit(t, 4)
    return sin(t) - (two*cos(t) - one(t))*sin(four*t)
end

function Yfun(t)
    two = _lit(t, 2); four = _lit(t, 4)
    return cos(t) - (two*cos(t) - one(t))*cos(four*t)
end

function Xprime(t)
    two = _lit(t, 2); four = _lit(t, 4)
    return cos(t) + two*sin(t)*sin(four*t) - four*(two*cos(t) - one(t))*cos(four*t)
end

function Ffun(t)
    two = _lit(t, 2); four = _lit(t, 4); seven = _lit(t, 7)
    x = Xfun(t)
    return (two*x + sin(seven*t))^2 + cos(seven*t)^2 - four*sin(t/two)^2
end

function Fprime(t)
    two = _lit(t, 2); seven = _lit(t, 7); fourteen = _lit(t, 14)
    x = Xfun(t)
    xp = Xprime(t)
    return two*(two*x + sin(seven*t))*(two*xp + seven*cos(seven*t)) -
           fourteen*cos(seven*t)*sin(seven*t) - two*sin(t)
end

side_length(z) = _lit(z, 2)*sin(z/_lit(z, 2))

"""
    coordinates(z)

Explicit n=16 specialization of the Bingane--Audet constructor.

The formulas have been simplified so that no interval approximation to pi is
required. Row `i+1` is the labelled vertex p_i.
"""
function coordinates(z)
    p = fill(zero(z), 16, 2)
    x = Xfun(z)
    y = Yfun(z)
    # multiple-angle literals as guaranteed thin intervals (see `_lit`)
    k2 = _lit(z, 2); k3 = _lit(z, 3); k5 = _lit(z, 5); k6 = _lit(z, 6); k7 = _lit(z, 7)

    p[1,:] .= (zero(z), zero(z))
    p[2,:] .= (sin(k2*z)-sin(z), cos(z)-cos(k2*z))
    p[3,:] .= (sin(k3*z)-sin(z), cos(z)-cos(k3*z))
    p[4,:] .= (-x, y)
    p[5,:] .= (x+sin(k7*z), y+cos(k7*z))
    p[6,:] .= (x+sin(k6*z), y+cos(k6*z))
    p[7,:] .= (x+sin(k5*z), y+cos(k5*z))
    p[8,:] .= (sin(z), cos(z))
    p[9,:] .= (zero(z), one(z))
    p[10,:] .= (-sin(z), cos(z))
    p[11,:] .= (-x-sin(k5*z), y+cos(k5*z))
    p[12,:] .= (-x-sin(k6*z), y+cos(k6*z))
    p[13,:] .= (-x-sin(k7*z), y+cos(k7*z))
    p[14,:] .= (x, y)
    p[15,:] .= (sin(z)-sin(k3*z), cos(z)-cos(k3*z))
    p[16,:] .= (sin(z)-sin(k2*z), cos(z)-cos(k2*z))
    return p
end

sqdist(p, i, j) =
    (p[j+1,1]-p[i+1,1])^2 + (p[j+1,2]-p[i+1,2])^2
