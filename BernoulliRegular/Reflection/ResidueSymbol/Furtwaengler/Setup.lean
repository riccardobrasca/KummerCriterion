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

/-- The bundled data driving the Stickelberger prime factorisation argument:
a finite field `k`, a target domain `R'`, primitive `p`-th roots of unity in
both `kˣ` and `R'ˣ`, the divisibility `p ∣ #k − 1`, and a primitive additive
character `ψ_q : k → R'`. The residue character `χ_q` and its Gauss sum
`g(χ_q, ψ_q)` are then determined by the bundle. -/
structure StickelbergerSetup where
  /-- A primitive `p`-th root of unity in the residue field. -/
  zeta_q : kˣ
  /-- Witness of primitivity. -/
  hzeta_q : IsPrimitiveRoot zeta_q p
  /-- The cardinality compatibility condition: `p ∣ #k − 1`. -/
  hdiv : p ∣ Fintype.card k - 1
  /-- A primitive `p`-th root of unity in the target ring. -/
  zeta_R : R'ˣ
  /-- Witness of primitivity. -/
  hzeta_R : IsPrimitiveRoot zeta_R p

namespace StickelbergerSetup

variable {p k R'}
variable (S : StickelbergerSetup p k R')

/-- The residue `MulChar` specialised to the bundle. -/
def residueChar : MulChar k R' :=
  Furtwaengler.residueMulChar S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R


omit [IsDomain R'] in
/-- Bundle accessor: `χ_q^p = 1` as a `MulChar`. -/
theorem residueChar_pow_eq_one : S.residueChar ^ p = 1 :=
  Furtwaengler.residueMulChar_pow_eq_one_mulChar
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R


/-- Bundle accessor: `orderOf χ_q = p`. -/
theorem orderOf_residueChar : orderOf S.residueChar = p :=
  Furtwaengler.orderOf_residueMulChar
    S.zeta_q S.hzeta_q S.hdiv S.zeta_R S.hzeta_R








end StickelbergerSetup

end Furtwaengler

end BernoulliRegular
