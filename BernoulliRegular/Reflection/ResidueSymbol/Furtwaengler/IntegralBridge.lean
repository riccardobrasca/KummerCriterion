module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerCongruence

/-!
# Integral target bridge for Stickelberger Gauss sums

This file moves the concrete Furtwängler Gauss sums from the field target `R'`
to the ring of integers `𝓞 R'`.  The digit-sum congruence is measured at the
concrete prime ideal `Q : Ideal (𝓞 R')`, so later Layer 2 arguments need the
same character values and Gauss sum as actual algebraic integers.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w


end Furtwaengler

end BernoulliRegular
