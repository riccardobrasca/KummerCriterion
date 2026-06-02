module

public import BernoulliRegular.FLT37.PrimaryConj
public import FltRegular.CaseII.AuxLemmas

/-!
# Class-group descent of primary `(α)` (ticket FLT37b2b2)

For primary `α ∈ 𝓞 K` with `(α) = 𝔞^p`, we want to conclude that the class
`[𝔞]` in `Cl(𝓞 K)` is `σ`-fixed, hence descends to `Cl(𝓞 K⁺)` and (under
Vandiver's conjecture) is trivial.

This file collects the **σ-equivariance of ideal equations** at the
`Ideal (𝓞 K)` level (FLT37b2b2-a). The deeper Kummer-style argument
(`σ α / α = u · v^p`) and the descent through the class group are
deferred to FLT37b2b2-b/c/d/e.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.4.
* Borevich–Shafarevich, *Number Theory*, §4.9.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

section IdealEquivariance

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]








end IdealEquivariance

/-! ## Class equality from a Kummer-style element relation (FLT37b2b2-c)

If `(α) = 𝔞^p` and there exist a unit `u : (𝓞 K)ˣ` together with elements
`a, b ∈ 𝓞 K` (representing `v = a/b` in `K`) satisfying the
denominators-cleared form `σ α · b^p = u · a^p · α`, then taking ideals
yields `(σ 𝔞 · (b))^p = ((a) · 𝔞)^p`. By unique factorisation in a
Dedekind domain, `σ 𝔞 · (b) = (a) · 𝔞`, which is exactly the
`ClassGroup.mk0_eq_mk0_iff` characterisation of `[σ 𝔞] = [𝔞]`. -/

section ClassEqualityFromKummer

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]





end ClassEqualityFromKummer

/-! ## Class descent via the `(p+1)/2` trick (FLT37b2b2-d, partial)

For `p` odd, the involution `σ` decomposes `Cl(𝓞 K)_p` into `±1` eigenspaces.
A `σ`-fixed `p`-torsion class `[𝔞]` automatically lies in the `+1` eigenspace,
and (away from `2`-torsion, which is trivial in the `p`-Sylow for `p` odd) the
`+1` eigenspace agrees with the image of `classGroupMap : Cl(𝓞 K⁺) → Cl(𝓞 K)`.

The argument we formalise here uses the auxiliary class `[𝔞 · σ𝔞] = [𝔞]²` and
the `(p+1)/2` trick: assuming that `[𝔞]²` is in the image of `classGroupMap`,
we can recover `[𝔞]` by raising to `(p+1)/2`.

The unconditional descent of `[𝔞 · σ𝔞]` to `Cl(𝓞 K⁺)` (the actual b2b2-d
content) requires Galois descent at the ideal level for `σ`-fixed ideals;
that step is left for a follow-up using the project's
`MulSemiringAction Gal(K/K⁺) (𝓞 K)` infrastructure. -/

section ClassDescent

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K




end ClassDescent

end FLT37

end BernoulliRegular

end
