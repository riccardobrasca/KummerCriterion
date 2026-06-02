module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Basic

/-!
# Concrete Artin-Hasse quotient facts

Split from `DworkFactorization.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')



















/-- The finite correction accumulated by iterating the Dwork recursion
`m` times from a quotient parameter `z`. -/
noncomputable def artinHasseExpIterCorrection
    (N : ℕ) (z : 𝓞 R' ⧸ S.Q ^ (N + 1)) : ℕ → 𝓞 R' ⧸ S.Q ^ (N + 1)
  | 0 => 1
  | m + 1 =>
      (artinHasseExpIterCorrection N z m) ^ ℓ *
        (PowerSeries.trunc (N + 1)
          ((rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N))).eval₂
            (RingHom.id (𝓞 R' ⧸ S.Q ^ (N + 1))) (z ^ (ℓ ^ m))









end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
