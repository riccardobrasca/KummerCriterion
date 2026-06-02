module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.Part2.Part2

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]



/-! ### Conjugation norm of the actual Φ product -/





/-- If `α` is semi-primary, then the Stickelberger principal generator
`α^Θ` is semi-primary. -/
theorem isSemiPrimary_stickelbergerPrincipalGen
    (hp_two : 2 ≤ p) {α : 𝓞 K}
    (hα : FLT37.IsSemiPrimary p (K := K) α) :
    FLT37.IsSemiPrimary p (K := K)
      (stickelbergerPrincipalGen (p := p) (K := K) α) := by
  unfold stickelbergerPrincipalGen
  refine isSemiPrimary_finset_prod
    (p := p) (K := K) (Finset.univ : Finset (CyclotomicUnitDelta p))
    (fun a =>
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^
        ((a : ZMod p).val)) ?_
  intro a _
  exact isSemiPrimary_pow
    (p := p) (K := K)
    (isSemiPrimary_cyclotomicRingOfIntegersEquiv
      (p := p) (K := K) hp_two a⁻¹ hα)
    ((a : ZMod p).val)



/-! ### Stickelberger principal generator under complex conjugation -/

/-- In an odd cyclotomic field, complex conjugation on `𝓞 K` is the
cyclotomic automorphism indexed by `-1`.

The proof compares the two rational Galois automorphisms on the field and
then restricts to the ring of integers. -/
theorem ringOfIntegersComplexConj_eq_cyclotomicRingOfIntegersEquiv_neg_one
    [IsCMField K] (hp_gt_two : 2 < p) (x : 𝓞 K) :
    ringOfIntegersComplexConj K x =
      cyclotomicRingOfIntegersEquiv (p := p) K (-1) x := by
  symm
  apply RingOfIntegers.ext
  change cyclotomicSigmaOfUnit (p := p) K (-1) (x : K) =
    complexConj K (x : K)
  rw [cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal (p := p) (K := K) hp_gt_two]
  rfl





/-! ### Stickelberger norm as the integer norm -/

end Furtwaengler

end BernoulliRegular

end

end
