module

public import KummerCriterion.UnitQuotient.DeltaAction
public import Mathlib.NumberTheory.NumberField.CMField
import KummerCriterion.UnitQuotient.ConjugationTrace
import Mathlib.Analysis.SpecialFunctions.Bernstein

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace KummerCriterion

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- In an odd cyclotomic field, complex conjugation on `𝓞 K` is the
cyclotomic automorphism indexed by `-1`. -/
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

end Furtwaengler

end KummerCriterion

end

end
