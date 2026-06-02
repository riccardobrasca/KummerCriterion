module

public import BernoulliRegular.Reflection.ResidueSymbol.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Non-canonical p-th power residue symbols

This file contains the older choice-dependent residue-symbol API used by some
algebraic Stickelberger support lemmas.  It is only the finite-field
definition and its elementary multiplicativity/vanishing facts.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]


























end Furtwaengler

end BernoulliRegular

end
