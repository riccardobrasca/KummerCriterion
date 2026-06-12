# Blueprint for `flt-regular-bernoulli`

This directory contains a blueprint-style write-up of the mathematical
content of the project, with links to the corresponding checked entries.

## Structure

- `src/content.tex` — abstract, table of contents, and bibliography.
- `src/subsections/*.tex` — one chapter per part of the proof:
  - `introduction.tex` — history, main results, notation and conventions,
    and an outline of the proof.
  - `cm-splitting.tex` — CM field structure and the factorisation
    `h = h⁺ * h⁻`.
  - `hminus-formula.tex` — Dirichlet characters, generalised Bernoulli
    numbers, the analytic formula for the relative class number, and its
    reduction to Bernoulli numerators.
  - `cyclotomic-units.tex` — real cyclotomic units, the Kummer logarithm
    matrix, saturation, and the plus class-number index theorem.
  - `final.tex` — assembly of Kummer's criterion from the minus criterion and
    cyclotomic-unit index argument.
  - `irregular-primes-carlitz.tex` — Carlitz's finite-set escape proof that
    there are infinitely many irregular primes.
- `src/macros/` — LaTeX macro definitions for the online and PDF renderings.
- `src/web.tex` and `src/print.tex` — entry points for the online and PDF
  renderings of the same blueprint source.

## Building

Standard blueprint workflow:

```bash
cd blueprint/src
plastex web.tex                  # HTML version
latexmk -pdf print.tex          # PDF version
```

## Reading

The blueprint is intended to be readable on its own. Each definition and
theorem is stated in mathematical prose, with a `\lean{...}` annotation for
the corresponding checked entry. You should not need any auxiliary files to
understand the statements.

The `\uses{...}` macro records the (mathematical) dependency graph between
items; the blueprint tool turns this into a visualisation when the HTML
version is built.

## Status

The route to `KummerCriterion` is documented in the chapters
included by `src/content.tex`, which is the authoritative table of contents
for the blueprint.
