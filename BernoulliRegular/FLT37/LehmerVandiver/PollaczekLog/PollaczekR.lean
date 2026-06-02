module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekUnit

/-!
# Auxiliary Pollaczek cyclotomic unit `pollaczekR`

For an odd prime `p` and a non-negative integer `i`, Washington defines
the auxiliary cyclotomic element

  `R_i := ∏_{a=1}^{p-1} (ζ^{a/2} - ζ^{-a/2})^{a^{p-1-i}} ∈ 𝓞 K`

inside `K = ℚ(ζ_p)` where `ζ = ζ_p` is the standard primitive `p`-th
root of unity. Here `a/2` denotes `a · 2⁻¹` viewed in `ZMod p`; this is
well-defined because `2 ∈ ZMod p` is invertible whenever `p` is odd.

`R_i` is related to the Pollaczek unit `E_i = pollaczekUnit p K i`
(developed in `BernoulliRegular/FLT37/LehmerVandiver/PollaczekUnit.lean`)
by Pollaczek's identity (Washington, p. 158, line 5)

  `R_i^{g^i - 1} = E_i · α^p`     for some `α ∈ K^×`

with `g` a primitive root mod `p`. This file only **defines** `R_i` and
gives the basic factorisation API; Pollaczek's identity itself is the
content of the companion ticket **LV004d**.

## Key factorisation

Since `(ζ^{a/2} - ζ^{-a/2}) = ζ^{-a/2} · (ζ^{2·(a/2)} - 1)`, the product
`R_i` factors term-wise into a `ζ`-power times the simpler product
`∏_{a=1}^{p-1} (ζ^{2·(a/2)} - 1)^{a^{p-1-i}}`. Together with the
`ZMod p`-identity `2 · (a/2) = a`, the second factor is
`∏_{a=1}^{p-1} (ζ^a - 1)^{a^{p-1-i}}` (after using `ζ^p = 1`).

* `pollaczekRFactor_eq_neg_half_mul_sub` exposes the term-wise unit-zpow
  factorisation `ζ^{a/2} - ζ^{-a/2} = ζ^{-a/2} · (ζ^{2·(a/2)} - 1)`.
* `two_mul_pollaczekRExp` is the `ZMod p` identity `2 · (a/2) = a`.
* `zeta_unit_zpow_two_mul_pollaczekRExp_val_eq` lifts this to the
  unit-zpow identity `ζ^{2·(a/2).val} = ζ^a` using `ζ^p = 1`.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units), p. 158 (line 1, defining `R_i`).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section PollaczekR




end PollaczekR

section PollaczekRAPI

variable (i : ℕ)








end PollaczekRAPI

section PairUp

variable (i : ℕ)











end PairUp

end FLT37

end BernoulliRegular

end
