module

public import KummerCriterion.TotallyRealSubfield.ClassGroup
public import Mathlib.NumberTheory.Bernoulli
import KummerCriterion.HMinus.HMinusCriterion
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Minus class-number criterion for the cyclotomic-unit route

This file records the `h⁻`/Bernoulli-numerator API in the direction used by the
cyclotomic-unit proof of weak reflection.
-/

@[expose] public section

noncomputable section

open NumberField

namespace KummerCriterion

/-- Contrapositive form of `p_dvd_hMinus_iff_p_dvd_some_bernoulli`. -/
theorem bernoulli_nonzero_of_not_dvd_hMinus
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K] (hp_odd : p ≠ 2)
    (hminus : ¬ (p : ℕ) ∣ hMinus K) :
    ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
      ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num := fun k hk hk_range hnum =>
  hminus <|
    (p_dvd_hMinus_iff_p_dvd_some_bernoulli (p := p) (K := K) hp_odd).2
      ⟨k, hk, hk_range, hnum⟩

end KummerCriterion

end
