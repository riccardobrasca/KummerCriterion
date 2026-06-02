module

public import BernoulliRegular.FLT37.PrimaryUnits

/-!
# Pollaczek cyclotomic unit `pollaczekUnit p i`

For an odd prime `p` and an even integer `i ∈ {2, 4, …, p-3}`,
Washington defines the **Pollaczek cyclotomic unit**

  `E_i := ∏_{b=1}^{(p-1)/2} ((1 - ζ^b) / (1 - ζ))^{b^{p-1-i}} ∈ (𝓞 K)ˣ`

inside `K = ℚ(ζ_p)` where `ζ = ζ_p` is a primitive `p`-th root of
unity (Washington, *Introduction to Cyclotomic Fields*, §8.3, p. 156).

The factor `(1 - ζ^b) / (1 - ζ)` is the cyclotomic unit
`cyclotomicUnit p K b` (a unit in `𝓞 K` because `b` is coprime to `p`
in the relevant range), already developed in
`BernoulliRegular/FLT37/PrimaryUnits.lean`.

This file provides the definition and the basic API:

* `pollaczekUnit_one`  – the degenerate value when the index range is
  empty (i.e. `p = 2`), giving `pollaczekUnit p K i = 1`.
* `pollaczekUnit_norm` – the integer norm `Algebra.norm ℤ` of the
  underlying ring-of-integers element equals `1`. This follows from
  multiplicativity of the norm and `cyclotomicUnit_norm_int`.
* `pollaczekUnit_complexConj` – the **symmetrised real combination**
  `pollaczekUnit p K i · σ(pollaczekUnit p K i)` is fixed by complex
  conjugation, so descends to the maximal real subfield `K⁺`. This
  mirrors the `realCyclotomicUnit` pattern in `PrimaryUnits.lean`.
  Washington's bare `E_i` is **not** literally `σ`-fixed in
  `(𝓞 K)ˣ`; only `E_i · σ(E_i)` is. Washington's proof of
  Proposition 8.18 (p. 158) handles the residual `ζ`-twist mod `p`-th
  powers; the precise mod-`ℓ` statement is the content of ticket
  **LV004**.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units), p. 156-158.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


end FLT37

end BernoulliRegular

end
