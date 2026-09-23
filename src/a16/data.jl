# The fixed data of the A16 certificate: the active diameter graph, the rows and
# columns of the square minor used by the multiplier system, and the root literal.
#
# Part of module A16Certificate (src/A16Certificate.jl), which includes this
# file; it is not meant to be loaded on its own.

const ACTIVE_EDGES = [
    (0,7), (0,8), (0,9), (1,9), (2,9), (2,10), (3,10),
    (3,11), (3,12), (4,13), (5,13), (6,13), (6,14),
    (7,14), (7,15)
]

# Julia indices. Row 19 is d_{0,9}; columns 3,4,17 are x_1,y_1,x_8.
const ROWS_MINOR = vcat(collect(1:18), collect(20:31))
const OMITTED_COLUMNS = [3,4,17]
const COLS_MINOR = [j for j in 1:33 if !(j in OMITTED_COLUMNS)]

const z_nominal = big"0.19627037213032280086206121185805318446"
