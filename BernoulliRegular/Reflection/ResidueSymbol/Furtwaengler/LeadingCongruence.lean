module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IntegralBridge

/-!
# Binomial leading congruence for integral Stickelberger Gauss sums

This file proves the formal congruence step used by the trace-form
Stickelberger calculation.  Since `ζ_ℓ = 1 + π` in `𝓞 R'` and `π ∈ Q`,
the integral Gauss sum is congruent modulo `Q^(s+1)` to its binomial
expansion truncated at degree `s`.

The remaining trace/multinomial calculation identifies the first non-zero
coefficient of this truncated expression.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w


namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')









end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular
