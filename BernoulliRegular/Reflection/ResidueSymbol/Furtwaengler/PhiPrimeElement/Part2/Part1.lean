module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement.Part1

/-!
# Data-carrying prime Φ-elements

The ideal-theoretic predicate `StickelbergerIdealEquality P` only says that
`stickelbergerIdeal P` is principal. Its extracted generator is therefore an
arbitrary generator, determined only up to a unit.

For K2-2 we need the actual Gauss-sum Φ element, not an arbitrary generator of
the same ideal. This file introduces a non-`Prop` object whose `gamma` field is
the element used in the residue-symbol theorem. The current constructor wires
in the existing `phiPrimeGenDescent S a` route from `CrossRingBridge.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

namespace PhiPrimeElement





/-! ### Bundled K2-2 interface -/

/-- Source-side data for the corrected K2-2 theorem.

This bundles the data saying that the source prime `P` is represented by the
actual descended Gauss-sum element `phiPrimeGenDescent S 1`.  The span field is
the mathematically substantive assertion that this concrete descended element,
not merely some arbitrary generator, generates the Stickelberger ideal. -/
structure K2_2SourceData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R') where
/-- Target-side data for the corrected K2-2 theorem.

The over-prime and its residue characteristic are kept as data because the
cross-ring Frobenius theorem is proved in a finite cyclotomic extension `R'`
above `K`.  This object is the honest interface for applying K2-2 at a target
prime `P'`. -/
structure K2_2TargetData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (P' : Ideal (𝓞 K)) [P'.IsMaximal] where


/-! ### Conductor-flexible source data -/


/-! ### Conductor-flexible reciprocal source data -/








end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end
