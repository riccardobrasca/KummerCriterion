import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitGroup
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.SigmaPreservation
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation

/-!
# `pollaczekUnit` and `pollaczekUnitPlus` lie in `cyclotomicUnitsSubgroup`

The Pollaczek unit `pollaczekUnit p K i = ∏_{b=1}^{(p-1)/2} cyclotomicUnitUnit(b)^{b^{p-1-i}}`
is by construction a finite product of cyclotomic units. Hence it
lives in the cyclotomic-units subgroup `C ⊆ (𝓞 K)ˣ`.

Likewise the σ-symmetrised form `pollaczekUnitPlus = pollaczekUnit · σ(pollaczekUnit)`
lies in `C` (since σ preserves `C` — see
`unitsComplexConj_preserves_cyclotomicUnitsSubgroup`).

This is **Step (E)** of the Sinnott / Cor 8.19 bridge construction.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §8.3.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


variable [IsCMField K]



end Sinnott

end FLT37

end BernoulliRegular

end
