module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement.Part2.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

namespace PhiPrimeElement







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
