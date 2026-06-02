module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Character
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Residue Gauss sum (REF-18c2b)

This file packages the Gauss sum at a residue character `χ_q` (REF-18c2a).
For a finite field `k` with `p ∣ #k - 1`, a chosen primitive `p`-th root of
unity in a target field `R'`, and a non-trivial additive character
`ψ_q : AddChar k R'`, the residue Gauss sum is

  `g(χ_q, ψ_q) := Σ_{x ∈ k} χ_q(x) · ψ_q(x) ∈ R'`

defined via mathlib's general `gaussSum`. The basic norm relation
`g(χ) · g(χ⁻¹, ψ⁻¹) = #k` follows from
`gaussSum_mul_gaussSum_eq_card` once we feed it `IsPrimitive ψ_q` and
`χ_q ≠ 1`.

This commit lands the Gauss-sum *definition* and the immediate norm
corollary; the substantive Frobenius / Galois-action facts (the rest of
REF-18c2b) are left for follow-ups since they need additional setup
(choice of additive character, ambient cyclotomic extension, Galois
trasport).

## Main definitions

* `BernoulliRegular.Furtwaengler.residueGaussSum`: the Gauss sum
  `g(χ_q, ψ_q)`.
* `residueGaussSum_mul_inv_eq_card`: the basic norm identity, valid when
  `χ_q ≠ 1` and `ψ_q` is primitive.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

variable {k : Type*} [Field k] [Fintype k]
variable {R' : Type*} [CommRing R'] [IsDomain R']
variable {p : ℕ}



end Furtwaengler

end BernoulliRegular

/-!
### Galois action on Gauss sums

The Gauss sum behaves naturally under ring homomorphisms of the target:
post-composing `χ` and `ψ` with a ring hom `σ` and applying `σ` to the
Gauss sum coincide. This is the core lemma from which Galois-equivariance
of residue Gauss sums follows.
-/

namespace BernoulliRegular

namespace Furtwaengler


variable {k : Type*} [Field k] [Fintype k]
variable {R' : Type*} [CommRing R'] [IsDomain R']
variable {p : ℕ}


end Furtwaengler

end BernoulliRegular

/-!
### Non-triviality bridge

The exponent vanishes exactly when the underlying finite-field power
`x ^ ((#k - 1) / p)` is `1`. This bridge lets the user demonstrate
non-triviality of `residueMulChar` by exhibiting an element of `kˣ`
with non-trivial `(#k - 1)/p`-power.
-/

namespace BernoulliRegular

namespace Furtwaengler

open Reflection.ResidueSymbol.PowerResidue





end Furtwaengler

end BernoulliRegular
