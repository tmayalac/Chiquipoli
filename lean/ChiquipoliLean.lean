/-
ChiquipoliLean — a Lean 4 / Mathlib formalization of the exact-algebra layer of
the A16 first-order certificate.

    import ChiquipoliLean

brings the whole development into scope. See `lean/README.md` for exactly what
is and what is not formalized here. The modules are grouped by role:

  Theory/       Theorem 3.5, Lemma 3.4 and Proposition 3.8 for an arbitrary
                configuration, with no reference to A16, and the abstract
                quantitative step behind the radius of Theorem 6.4
  Constructor/  the A16 constructor, its root, and Lemma 6.1
  Generated/    emitted by `lean/generators/*.jl` from the certified Julia
                arithmetic; never edited by hand (`verify.sh`, check 5)
  Instances/    the theory applied to A16, the square and the rhombus, and
                the explicit radius of Theorem 6.4 at A16

`Certificate.lean` assembles the six computational gates at one root, and
`Audit.lean` (not imported here) prints the axioms of every headline theorem.
-/

-- Theory: the general first-order criterion
import ChiquipoliLean.Theory.FirstOrder
import ChiquipoliLean.Theory.Instability
import ChiquipoliLean.Theory.Slice
import ChiquipoliLean.Theory.SliceIFT
import ChiquipoliLean.Theory.Feasible
import ChiquipoliLean.Theory.FeasibleOpen
import ChiquipoliLean.Theory.FeasibleTangent
import ChiquipoliLean.Theory.FeasibleRigid
import ChiquipoliLean.Theory.FeasibleMain
import ChiquipoliLean.Theory.Coercive
import ChiquipoliLean.Theory.Radius
import ChiquipoliLean.Theory.RadiusPrinted

-- Constructor: the A16 constructor and its root
import ChiquipoliLean.Constructor.Chebyshev
import ChiquipoliLean.Constructor.Coordinates
import ChiquipoliLean.Constructor.Identities
import ChiquipoliLean.Constructor.RootExists
import ChiquipoliLean.Constructor.SearchInterval
import ChiquipoliLean.Constructor.SideLength
import ChiquipoliLean.Constructor.A16Exists

-- Generated: emitted from Julia, checked byte for byte
import ChiquipoliLean.Generated.Polynomials
import ChiquipoliLean.Generated.Positivity
import ChiquipoliLean.Generated.InactiveMargin
import ChiquipoliLean.Generated.Diameter
import ChiquipoliLean.Generated.Convexity
import ChiquipoliLean.Generated.Multipliers
import ChiquipoliLean.Generated.Rank
import ChiquipoliLean.Generated.Radius
import ChiquipoliLean.Generated.RadiusPrinted

-- Instances: the theory at A16, the square and the rhombus
import ChiquipoliLean.Instances.A16FirstOrder
import ChiquipoliLean.Instances.A16Rank30
import ChiquipoliLean.Instances.A16LocalMax
import ChiquipoliLean.Instances.SquareAndRhombus
import ChiquipoliLean.Instances.SquareLocalMax
import ChiquipoliLean.Instances.A16Radius
import ChiquipoliLean.Instances.A16RadiusPrinted

-- The assembled certificate
import ChiquipoliLean.Certificate
