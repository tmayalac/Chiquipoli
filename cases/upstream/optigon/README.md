# Upstream OPTIGON constructor, verbatim

`cstrt_audet_ngon.jl` is the file `cstrt_ngon/cstrt_audet_ngon.jl` of OPTIGON,
copied **byte for byte**:

| | |
|---|---|
| Project | OPTIGON: Extremal small polygons, by Christian Bingane |
| Repository | https://github.com/cbingane/optigon |
| File | `cstrt_ngon/cstrt_audet_ngon.jl` |
| Size | 2681 bytes |
| SHA-256 | `376e838b87009f749c19dbee0407419f3c58b30021c406a952a01671aaf6d0ff` |
| Licence | MIT, Copyright (c) 2020 Christian Bingane (`LICENSE`, copied alongside) |
| Paper | C. Bingane and C. Audet, *Tight bounds on the maximal perimeter of convex equilateral small polygons*, Arch. Math. 119 (2022) 325–336 |

The SHA-256 is the one recorded when the file was first retrieved (2026-09-08).
It was confirmed again on 2026-09-24 against an independent download of the
repository (`optigon-master`).

**Nothing edits this file.** `cases/optigon_exact.jl` runs it unchanged, in
exact arithmetic, and the family certificate and the test suite require the
polygon and the equation it produces to be *exactly* those the certificate is
about. The test suite also checks the SHA-256 above, so a changed byte fails.

To check it against your own copy of OPTIGON:

    OPTIGON_DIR=/path/to/optigon julia --project=. test/runtests.jl

which additionally requires the file there to be byte-identical to this one.
