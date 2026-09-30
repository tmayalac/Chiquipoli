/-
ChiquipoliFamily — the Lean certificates of the Bingane–Audet family `A_n`,
`n = 2^s`, produced by `lean/generators/family/gen_family.jl` from the same exact
arithmetic as the Julia certificate.

    lake build ChiquipoliFamily

`Basic.lean` holds everything that is proved once for all `n`; each `A<n>/`
directory is generated. See `lean/ChiquipoliFamily/README.md`.
-/
import ChiquipoliFamily.Basic
import ChiquipoliFamily.Optigon
import ChiquipoliFamily.Chebyshev
import ChiquipoliFamily.Polynomial.A16
import ChiquipoliFamily.Polynomial.A32
import ChiquipoliFamily.Polynomial.A64
