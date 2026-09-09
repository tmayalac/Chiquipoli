# The square: an exact certificate by hand

Read this before $A_{16}$. It is the analytic example of the article's
Section 4.1 (Lemma 4.1 and Proposition 4.2), and every step can be checked
without a computer.

The square of unit diameter has side $1/\sqrt2$. Its active equality Jacobian
has rank 6 in a space of dimension 9, so the kernel has dimension 3 and
coincides with the infinitesimal rigid motions: $\mathcal I_{\mathrm{eq}} =
R_{\mathrm{eq}}$, which is hypothesis (ii) of Theorem 3.5.

The two active diagonals carry multipliers $\sqrt2 > 0$ and the four sides
carry $\alpha_i = -1$, which is hypothesis (i). Note that
$\sum_i \alpha_i = -4 = -n$, as the multiplier balance requires.

Both hypotheses hold, so by Theorem 3.5 the square is a strict local maximiser
of perimeter, modulo orientation-preserving Euclidean motions, among convex
equilateral small quadrilaterals.

Run it with:

```bash
julia --project=../.. square_certificate.jl
```
