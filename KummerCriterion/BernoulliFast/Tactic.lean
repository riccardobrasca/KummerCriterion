/-
Copyright (c) 2026 Bernoulli-Regular project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernoulli-Regular project contributors
-/
module

public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
public meta import Std.Do.Triple.SpecLemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Tactic for certifying Bernoulli number values

Provides the `bernoulli_decide` tactic which closes goals involving concrete
Bernoulli numbers by rewriting to the certified `Cbv.bernoulliFrac` evaluator
and normalizing it with `cbv`.
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
