# Independent verification (second source)

This directory holds a second verification of the finding behind **Lemma 6.1**
of the article, carried out with a different method and a different library
from the main certificate. The finding, recorded in `docs/provenance-mapping.md`,
is that of the 31 exact equalities of the $A_{16}$ constructor, 29 are
unconditional trigonometric identities — valid for every real $z$ — and only 2,
the sides $\{3,4\}$ and $\{12,13\}$ (that is, $|p_4-p_3|=\ell$ and
$|p_{13}-p_{12}|=\ell$), are conditional, being nonzero constant multiples of
$F_c(c)$; in fact literally equal to $F(z)$.

This is the "independent SymPy verification" referred to in Remark 5.1 of the
supplementary material accompanying the article.

## Provenance, and what "independent" means here

Be precise about this, because the word is easy to overclaim.

- **Who produced it.** A second AI agent, from the same model family as the one
  that produced the main certificate, instructed explicitly *not* to read
  `src/`, `scripts/`, `test/` or `docs/provenance-mapping.md`, and to write its
  own code from scratch rather than adapt what already existed.
- **What it was given.** Only the explicit constructor formulas — the sixteen
  vertex coordinates and $F(t)$ — transcribed into the prompt and taken as the
  starting point. It was not asked to check that those formulas faithfully
  reproduce the Bingane–Audet construction, only to analyse the algebraic
  structure of those specific formulas.
- **What this is not.** It is not verification by a human mathematician, nor by
  a system from a different model family, nor a formal proof in a proof
  assistant. It is a second, independent computational implementation of the
  same algebraic argument. It is useful for ruling out that the result is an
  artefact of a specific bug in the first implementation, and it does not
  substitute for a human referee's judgement of the article itself.

The formal layer under `lean/` is the stronger check, and it is independent in
a different sense: it is kernel-verified rather than merely re-implemented.

## Method

- **Language and library:** Python with `sympy`. The main certificate uses
  Julia with hand-written exact rational arithmetic and no computer algebra
  library at all.
- **Same mathematics, written from scratch:** Chebyshev substitution, reduction
  to a polynomial in $c=\cos z$, and an exact divisibility check — implemented
  independently, not copied.
- **One check the main certificate does not perform:** it locates the root of
  $F$ on its own via `mpmath.findroot` at 60 digits, and re-derives the
  vertices directly from sine and cosine as a structural cross-check. See
  "structural-form check" in the output.

## Files

- `independent_sympy_check.py` — the script.
- `independent_sympy_check_output.txt` — its full output.

## Result

Agrees exactly with the main certificate on all 31 cases, including the exact
degree-12 polynomial for the two conditional ones: the quotient is 1, so
$D(c) \equiv F_c(c)$ term by term. The largest numerical residual at the root,
at 60 digits of working precision, is about $4\times10^{-58}$.
