module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FullTeich
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.WittCarry.Part1

/-!
# Witt carry comparison for Dwork factorization

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









/-- Ordinary correction factor version of
`artinHasseExp_traceCarry_coord_factor_eq_zmod`.  This is the `Rps` analogue
needed before the carry telescope is converted to Artin-Hasse factors. -/
theorem rescaleExp_traceCarry_coord_factor_eq_zmod
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) (r : ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ r) ((F.traceCarry y).coeff r)))) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε *
          θ (WittVector.teichmuller ℓ
            (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r)))) := by
  dsimp only
  rw [← F.traceCarryCoeffZMod_frobeniusRoot_spec y r]












end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
