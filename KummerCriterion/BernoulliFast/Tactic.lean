/-
Copyright (c) 2026 Bernoulli-Regular project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernoulli-Regular project contributors
-/
import KummerCriterion.BernoulliFast.Cbv
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Tactic for certifying Bernoulli number values

Provides the `bernoulli_decide` tactic which closes goals involving concrete
Bernoulli numbers by rewriting to the certified `Cbv.bernoulliFrac` evaluator
and normalizing it with `cbv`.

## Strategy

- Rewrite `bernoulli n` to `Cbv.toRat (Cbv.bernoulliFrac n)` via
 `← Cbv.bernoulliFrac_toRat_eq_bernoulli`.
- Run `cbv`, using the `Frac` and literal-list simprocs
 `KummerCriterion.BernoulliFast.Cbv`.

## Axioms

Only the standard axioms used by rational arithmetic. No `native_decide`; the
custom fraction representation is connected to `ℚ` by theorem-level proofs in
`KummerCriterion.BernoulliFast.Cbv`.
-/

namespace KummerCriterion.BernoulliFast

open Lean Elab Tactic

/-- `bernoulli_decide` closes goals involving concrete Bernoulli number
evaluations by rewriting to `Cbv.bernoulliFrac` and normalizing by `cbv`.

Supported goal shapes (with concrete numerals `n`, `p`, `z`, `q`):
- `bernoulli n = q` (full rational value in `ℚ`)
- `(bernoulli n).num = z`
- `(bernoulli n).den = d`
- `(p: ℤ) ∣ (bernoulli n).num`
- `¬ (p: ℤ) ∣ (bernoulli n).num` -/
elab "bernoulli_decide" : tactic => do
  let stx ← `(tactic|
    (rw [← Cbv.bernoulliFrac_toRat_eq_bernoulli]
     cbv))
  withTheReader Core.Context
    (fun ctx =>
      { ctx with
        maxHeartbeats := 1000000000
        options := (ctx.options.set `maxRecDepth 1000000000).set `cbv.maxSteps 20000000 }) do
    evalTactic stx

end KummerCriterion.BernoulliFast
