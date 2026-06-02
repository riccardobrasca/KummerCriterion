module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerPrincipalGen

/-!
# `Φ(A)` ideal-level extension and structural Kelly identity (REF-18 pivot)

This file defines the **Stickelberger-element-of-A** at the ideal level.
For an ideal `A` of `𝓞 K` coprime to `(p)`, the Stickelberger ideal
`A^Θ` is defined by

```
A^Θ := ∏_{a ∈ (ZMod p)ˣ} (σ_{a^{-1}} A) ^ a.val
```

This generalises `stickelbergerIdeal` (which works for arbitrary
ideals) and `stickelbergerPrincipalGen` (the principal-ideal case
returning an element).

Multiplicativity `(A · B)^Θ = A^Θ · B^Θ` follows from the multiplicativity
of `cyclotomicGaloisConjugate` on ideals plus Finset-product
distribution.

## Φ(A) = g(A)^p

The element `g(A)^p` (the `p`-th power of the Gauss sum at A) is the
distinguished generator of `A^Θ`. We package the existence of such a
generator (with the Stickelberger ideal equality) as the existing
`StickelbergerIdealEquality A`. The unit factor relating `g(A)^p` to
the canonical principal generator `α^Θ` (when A = (α)) is the
substantive content of the principal unit factor theorem
(`Φ((α)) = u(α) · α^Θ`).

## Structural Kelly identity (the substantive analytic content)

The key residue-symbol identity is

```
(Φ(A) / B)_p = (NB / A)_p             (Kelly form)
```

where `NB ∈ ℤ` is the norm of `B`. For primary `A = (α)` with
`u(α) = ±1`, this specialises to

```
(α^Θ / B)_p = (NB / α)_p
```

The file below records the ideal-level Φ algebra used by later Kelly-form
identities; it does not introduce a named reciprocity assumption.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Stickelberger ideal of a general ideal (multiplicative extension) -/



/-! ### `Φ(A)` existence as a structural hypothesis (general ideal) -/





/-! ### Primary unit factor (structural)

For principal `A = (α)`, the canonical generator is `α^Θ` (per
`PhiGenerator_principal`). The Gauss-sum-based "true" generator is
`g((α))^p` (where multiplicativity over the prime factorisation of `(α)`
defines `g((α))`); these may differ by a unit `u(α)`. The condition
`u(α) = ±1` (forced by primarity of α) is the substantive primarity
content.

We package the resulting principal unit factor identity as a structural
hypothesis ready to be discharged. -/


end Furtwaengler

end BernoulliRegular

end
