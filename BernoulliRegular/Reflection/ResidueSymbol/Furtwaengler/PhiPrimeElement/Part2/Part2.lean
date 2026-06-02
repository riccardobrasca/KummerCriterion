module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement.Part2.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

namespace PhiPrimeElement







/-- Source-side data for the conductor-flexible reciprocal-index K2-2
interface.

This is the flexible counterpart of `K2_2ReciprocalSourceData`: its `phi`
constructor is the actual descended reciprocal Gauss-sum element produced by
`ConductorFlexibleFullTeichDworkSetup.phiPrimeGenDescent`.  The K2 symbol
identity is intentionally ported separately, because the old proof still
uses the pair-cyclotomic `FullTeichDworkSetup` interface. -/
structure K2_2FlexibleReciprocalSourceData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R') where
  /-- The trace-form/Galois psi-shift compatibility needed for flexible
  descent to `𝓞 K`. -/
  h_psi :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.concrete.IsGalPsiShiftCompatible
  /-- The reciprocal-index Gauss sum has nonzero `p`-th power. -/
  h_ne_zero :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.gaussSumInt (p - 1) ^ p ≠ 0
/-- Target-side data for the conductor-flexible K2-2 theorem.

This is the target counterpart of `K2_2FlexibleReciprocalSourceData`: it
keeps the chosen over-prime and its residue characteristic, but does not ask
for the old pair-cyclotomic typeclass on `R'`. -/
structure K2_2FlexibleTargetData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (P' : Ideal (𝓞 K)) [P'.IsMaximal] where






end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end
