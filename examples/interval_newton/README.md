# Interval Newton, in its smallest form

The operator that gives existence and uniqueness of a root in one step, applied
to $f(x) = x^2 - 2$ near $\sqrt2$. For $X = [1.4, 1.5]$ with midpoint
$m = 1.45$,

$$N(X) = m - \frac{f(m)}{f'(X)}.$$

If $0 \notin f'(X)$ and $N(X)$ lies strictly inside $X$, then $f$ has exactly
one root in $X$. That is the whole argument behind gate 1 of the $A_{16}$
certificate, at a scale where it can be checked by hand.

Worth doing: widen the radius until the inclusion fails, and watch where the
guarantee is lost. The operator does not merely fail to prove uniqueness — it
stops proving existence too.

```bash
julia --project=../.. newton_sqrt2.jl
```
