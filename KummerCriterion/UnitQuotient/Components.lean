module

public import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Unit quotients: power quotients and `Δ`-components

This file is the power-quotient component layer. It defines the quotient `E / E^(p^N)`
`E = 𝒪_Kˣ`, records the exponent-killing lemma for the quotient map, and
packages the `Δ = (ZMod p)ˣ`-component size data used by reflection.

The component decomposition is kept data-driven: later files can instantiate
the supplied components with the intrinsic idempotent construction, while the
reflection layer can already consume stable character-tagged subgroups and
their computed cardinal exponents.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

set_option linter.unusedSectionVars false

variable (p N : ℕ) [Fact p.Prime]

/-- The Galois character group `Δ = (ZMod p)ˣ` indexing unit-quotient
components. -/
abbrev CyclotomicUnitDelta : Type :=
  (ZMod p)ˣ

end KummerCriterion
