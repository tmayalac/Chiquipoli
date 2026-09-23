# Documentation map

Start with the repository `README.md`, whose "Repository map" says where every
part of the code lives. These are the documents behind it.

## Guide

What the package establishes, and how, as it stands today.

| Document | What it answers |
|---|---|
| [certificate-spec.md](guide/certificate-spec.md) | What the certificate asserts, gate by gate, and what it does not |
| [provenance-mapping.md](guide/provenance-mapping.md) | Which computed quantity backs which claim of the article |
| [scope-and-limitations.md](guide/scope-and-limitations.md) | The honest boundary: what is certified, what is assumed, what is out of scope |
| [theorem-3.5-formalisation.md](guide/theorem-3.5-formalisation.md) | How Theorem 3.5 was formalised in Lean 4, plan against outcome |
| [general-framework.md](guide/general-framework.md) | The framework behind the `n = 4, 6, 8` cases, not only `A16` |
| [literature-validation.md](guide/literature-validation.md) | How the published cases were reproduced, and what "reproduced" means |

## Audit records

Reviews of the package and how each point was closed. They are records: each
describes the repository as it was when it was written, so file paths in them
may predate the 2026-09 reorganisation. `CHANGELOG.md` maps every old path to
its current one.

| Document | What it records |
|---|---|
| [referee-report.md](audits/referee-report.md) | Points raised in review and how each was closed |
| [theory-audit.md](audits/theory-audit.md) | An adversarial reading of the mathematics, with its findings |

The Lean layer documents itself separately, in [`../lean/README.md`](../lean/README.md).
