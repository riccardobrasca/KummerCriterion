module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Concrete
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FullTeich.Part3

/-!
# Full Teichmuller Dwork product setup

Split from `DworkFactorization.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (F : FullTeichStickelbergerSetup ℓ p k K R')




end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
