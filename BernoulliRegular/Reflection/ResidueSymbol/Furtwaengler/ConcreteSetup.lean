module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Setup
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Concrete Stickelberger setup (Layer 3, REF-18c2c4)

This file packages the arithmetic data needed to turn the abstract
`StickelbergerSetup` API into the concrete cyclotomic situation used by the
digit-sum Stickelberger congruence.

The bundle intentionally keeps the difficult arithmetic assertions as fields:
the prime `Q` above `ℓ`, the integral element `π = ζ_ℓ - 1`, and the residue
map from `𝓞 R'` to the finite field. Later Layer 3 tickets can strengthen this
data by proving the canonical identification of `Q` and constructing
Teichmüller lifts.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

end Furtwaengler

end BernoulliRegular
