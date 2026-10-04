# The article and its certificate

This folder is for a reader of *First Order Geometry of Equilateral Small
Polygons* who wants to check a statement of the article against the code. The
article prints only what its proofs use. Everything else is in its Online
Resource 1 (the supplement) and in the files listed below.

Paths are relative to the repository root. Lean paths are under
`lean/ChiquipoliLean/`.

## Table 3 of the article, row by row

| Row of Table 3 | Script | Field in `results/a16_certificate.toml` | Lean declaration |
|---|---|---|---|
| 29 differences ≡ 0; sides {3,4}, {12,13} = F_c | `pipeline/stages/06_prove_exact_identities.jl` | `exact_identities` | `all_sides`, `all_active_diameters` (`Constructor/A16Exists.lean`); `Fc_cos_eq_Ffun` (`Constructor/Coordinates.lean`) |
| det Q = y₁ − 1 < 0 | `pipeline/stages/05_certify_multipliers.jl` | `multipliers` (`omitted_residual_matrix_regularity_bound`) | (the exact argument of Subsection 6.4) |
| unique root in Z_root; no other root in I_search | `pipeline/stages/02_certify_root.jl` | `existence` | `constructor_root_existsUnique_article_search` (`Constructor/SearchInterval.lean`); `Fc_strictMonoOn_search` (`Generated/Positivity.lean`) |
| Z_root ⊂ int Z_cert | `pipeline/certify_a16.jl` | `box_nesting` | (Lean uses its own exact root bracket: `Constructor/RootExists.lean`) |
| ℓ and 16ℓ (Proposition 6.2(2)) | `pipeline/certify_a16.jl` | `side_length` | `side_length_bounds`, `perimeter_bounds` (`Constructor/SideLength.lean`) |
| min det > 0.00748 | `pipeline/stages/03_certify_geometry.jl` | `convexity` | `cross_pos` (`Generated/Convexity.lean`) |
| δ_inact > 0.00809 | `pipeline/stages/03_certify_geometry.jl` | `inactive_margin` | `sqd_le_one` (`Generated/Diameter.lean`) |
| ‖Id − C₀M₀‖ < 2·10⁻²⁵; min λ > 0.09186 | `pipeline/stages/05_certify_multipliers.jl` | `multipliers` | `multipliers_certified` (`Generated/Multipliers.lean`) |
| ‖Id − CM‖ < 1.5·10⁻²⁵ | `pipeline/stages/04_certify_rank.jl` | `rank` | `rank_eq_thirty` (`Instances/A16Rank30.lean`), by another route |
| ‖α‖₂ < 4.004; s₃₀(A)² ≥ 0.09119; r ≥ 6.63·10⁻⁴ | `pipeline/certify_radius.jl` | `results/radius_certificate.toml` | not formalised |
| I_eq = R_eq, Theorem 6.3 | (consequence) | — | `A16_Ieq_imp_R` (`Instances/A16FirstOrder.lean`); `A16_locally_maximal` (`Instances/A16LocalMax.lean`) |
| Theorem 3.5 | (not computed) | — | `thm_3_5` (`Theory/FeasibleMain.lean`) |
| Table 4, Proposition 6.5 and Theorem 6.6: A32 and A64 | `pipeline/certify_family.jl 32` / `64` | `results/family/A32.toml`, `A64.toml` | `Chiquipoli.Family.A32.published_locally_maximal`, `…A64…` (`lean/ChiquipoliFamily/Polynomial/`) |

The bounds in the Lean column are formalised at rounder constants than the
article prints; the supplement explains why, and why the Lean multipliers are
a different member of the same affine family.

## Where the rest is

- **Full-precision values:** each bound of Table 3 at twenty digits, with the
  critical pair {4,12} and the minimal multiplier edge {6,13}. See Section
  "The certified values in full" of Online Resource 1, and
  `results/a16_certificate.toml`.
- **The multiplier table** (31 midpoints, λ₀,₉ = 1/5): Online Resource 1. The
  enclosures themselves are `lambda_enclosure` and `alpha_enclosure` in
  `results/a16_certificate.toml`.
- **The published constructor, run unchanged in exact arithmetic:**
  - `cases/upstream/optigon/cstrt_audet_ngon.jl`, the upstream file, with its
    SHA-256;
  - `cases/optigon_exact.jl`, which runs it;
  - `lean/ChiquipoliFamily/Optigon.lean`, the Lean transcription.
- **Environment, versions and hashes:** the header of `logs/final_run.txt`, and
  the `[meta]` and `source_sha256` entries of every record.
- **Independent SymPy check of Lemma 6.1:**
  `tools/independent_check/independent_check.py`.
- **How the records are kept consistent with the tree:**
  `pipeline/check_records.jl` (`make check-records`). It checks every
  certificate verdict, the provenance and source hashes of every record, the
  published bounds against the certified values, and the Lean layer.

## Reproducing

```
julia --project=. -e "using Pkg; Pkg.instantiate()"
julia --project=. pipeline/certify_a16.jl      # the certificate, ~5 s
julia --project=. pipeline/certify_radius.jl   # the explicit radius
cd lean && ./verify.sh                         # the formal layer
```

`make check-all` runs everything, including the mutation and stress tests. It
takes about 70 minutes.
