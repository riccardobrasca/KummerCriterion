# KummerCriterion: notes for Claude Code

## Build and checks

- Build with `lake exe cache get` followed by `lake build`. The default targets are
  `KummerCriterion`, `Challenge` and `Solution`.
- The Mathlib linter set from `lakefile.toml` is on: keep lines at most 100 characters,
  leave no unused `have`s, and do not follow a bare `simp` with further tactics.
- The `sorry` in `Challenge.lean` is intentional. It is the comparator challenge statement,
  and `Solution.lean` proves it from the project. Do not remove or "fix" that warning.
- CI (`.github/workflows/build.yml`) runs `lake build`, then doc-gen and the blueprint. The
  blueprint step runs `lake exe checkdecls blueprint/lean_decls`, so after renaming or
  deleting a declaration listed there, update that file and run the command locally.
- A parse error hides every later error in a file. After fixing one, rebuild that module alone
  with `lake build <Module.Name>` before running the full build again.

## Toolchain bumps

- A bump updates `lean-toolchain` and `lake-manifest.json` (commit message `bump`), then the
  build is fixed repo-wide, warnings included. Breakage comes from Mathlib and from
  flt-regular, whose "useless" commits delete thin wrapper lemmas: inline the underlying
  Mathlib lemma rather than re-adding the wrapper.
- Changes met in the September 2026 bump (Lean v4.35.0-rc2): `PowerSeries.derivative` and the
  `d⁄dX` notation take the ring implicitly, so `d⁄dX R f` becomes `d⁄dX f`; a set literal split
  over lines, `{f a\n  (g b)}`, misparses as set-builder notation, so parenthesise the element
  as `{(f a\n  (g b))}`.

## Style

- Use the `congr(...)` term elaborator, as in `congr(f $h)`, instead of `congrArg`,
  `congr_arg`, `congr_fun`, `DFunLike.congr_fun`, or a `by rw [h]` whose only job is to
  rewrite under a function (see Mathlib PR #43408). It elaborates each side separately, which
  also handles the case where `rw [h]` leaves an `x = x` goal that `rfl` rejects because the
  implicit arguments differ.
