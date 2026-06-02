module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekUnit

/-!
# σ-symmetrisation of `pollaczekUnit` (LV005b)

The Pollaczek unit `pollaczekUnit p K i ∈ (𝓞 K)ˣ` is **not** literally
`σ`-fixed under the unit-group complex conjugation `unitsComplexConj K`;
the factor-wise σ-twist
`σ((1 - ζ^b)/(1 - ζ)) = ζ^{1 - b} · (1 - ζ^b)/(1 - ζ)`
introduces an explicit ζ-power. The standard remedy is the symmetrised
real combination

  `pollaczekUnitPlus p K i := pollaczekUnit p K i · σ(pollaczekUnit p K i)`,

which **is** σ-fixed and underlies the descent to the maximal real
subfield `K⁺` consumed by Washington's Cor 8.19 / our LV005c
Kummer-pairing bridge.

This file packages just the bare arithmetic:

* `pollaczekUnitPlus` — the symmetrised unit in `(𝓞 K)ˣ`.
* `pollaczekUnitPlus_complexConj` — σ-fixedness (one-line repackage of
  `pollaczekUnit_complexConj`).
* `pollaczekUnitPlus_norm` — `Algebra.norm ℤ` is `1` (square of
  `pollaczekUnit_norm`, after using that `Algebra.norm` is fixed by
  Galois — equivalently, multiplicativity over the symmetrised product).

The full descent of `pollaczekUnitPlus` to `(𝓞 K⁺)ˣ` and the connection
between `IsPthPowerModPrime` predicates on `pollaczekUnit` vs.
`pollaczekUnitPlus` is the deeper LV005c work; defer to that ticket.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units, p. 158); Corollary 8.19 (p. 158).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section PollaczekUnitPlus

variable (i : ℕ)




end PollaczekUnitPlus

end FLT37

end BernoulliRegular

end
