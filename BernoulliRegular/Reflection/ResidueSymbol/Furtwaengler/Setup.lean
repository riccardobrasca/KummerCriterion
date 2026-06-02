module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Stickelberger

/-!
# Stickelberger setup bundle (REF-18c2c1)

The remaining steps of REF-18c2c (q-adic valuation, Galois orbit, prime
factorisation, descent to `𝓞_K`) all share the same ambient data:

* a finite field `k` with `p ∣ #k − 1`,
* a target field `R'` containing both `μ_p` and a primitive additive
  character `ψ_q` on `k`,
* chosen primitive roots of unity in each.

This file packages that data as `StickelbergerSetup`, with accessors
for the residue character and Gauss sum specialised to the bundle.
Downstream sub-subtickets (c2-c5) consume the bundle directly so each
piece of the prime-ideal-level argument can refer to a single object
rather than carrying the same eight or nine implicit arguments.

The bundle is *minimal*: it carries only what the existing algebraic
core (the 22 theorems already proved in `Stickelberger.lean`) needs.
Specifically it requires `IsDomain R'` plus the chosen-root-of-unity
data; full `IsCyclotomicExtension {p, q} ℚ R'` typeclass instances are
*not* required at this layer — they will become relevant only when
REF-18c2c2 begins manipulating prime ideals of `𝓞_{R'}` and needs the
ring-of-integers structure.

## Main definitions

* `BernoulliRegular.Furtwaengler.StickelbergerSetup`: the bundle.
* `BernoulliRegular.Furtwaengler.StickelbergerSetup.residueChar`: the
  residue MulChar specialised to the bundle.
* `BernoulliRegular.Furtwaengler.StickelbergerSetup.gaussSum`: the
  residue Gauss sum specialised to the bundle.
* Accessor lemmas re-exporting REF-18c2c's algebraic core in
  bundle-aware form: `gaussSum_pow_p_eq_prod_jacobiSum`,
  `gaussSum_pow_p_isIntegral`, `gaussSum_pow_p_mem_closure`, etc.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Fintype k]
variable (R' : Type*) [CommRing R'] [IsDomain R']



end Furtwaengler

end BernoulliRegular
