import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.Bridge
import BernoulliRegular.TotallyRealSubfield.ClassGroup

/-!
# Cor 8.19 forward formulation + contrapositive constructor

The `Cor8_19Bridge` structure stores the contrapositive form
`(¬ IsPthPower(pollaczekUnitPlus)) → ¬ p ∣ h⁺`. Mathematically, the
classical statement (Washington Cor 8.19) is the forward form
`p ∣ h⁺ → IsPthPower(pollaczekUnitPlus)`.

This file provides:
* The forward Prop `Cor8_19Forward`.
* A bridge constructor `cor8_19Bridge_of_forward` showing the forward
  form yields the contrapositive bundle field. Useful for callers
  who'd rather prove the forward form directly.

The mathematical content (Sinnott's index formula
`[(𝓞 K⁺)ˣ : C⁺] = h⁺(K)`) is unchanged either way; this is just a
re-packaging convenience.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §8.3,
  Cor 8.19.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]








end BernoulliRegular

end
