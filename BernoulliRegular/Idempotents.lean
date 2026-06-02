module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.RingTheory.Idempotents

/-!
# Orthogonal idempotents associated to characters of a finite abelian group

For a finite abelian group `G` and a commutative ring `R` (integral domain)
in which `|G|` is invertible, and a character `χ : MulChar G R`, we define
the idempotent

`charIdempotent χ := (1/|G|) ∑_{σ ∈ G} χ(σ) · σ⁻¹ ∈ R[G]`

(Diekmann Definition 49). The family `{ε_χ}` over all characters is a system
of orthogonal idempotents satisfying `ε_χ · ε_χ = ε_χ` and `ε_χ · ε_ψ = 0`
for `χ ≠ ψ`; this is Diekmann Lemma 50 (T028).

## Main definitions

* `BernoulliRegular.charIdempotent`: the idempotent `ε_χ` in `MonoidAlgebra R G`.
* `BernoulliRegular.MonoidAlgebra.charComponentEquiv`: the ring isomorphism
  `R[G] ≃+* ∏_χ (ε_χ).Corner` expressing the group algebra as a product of
  corner rings indexed by characters (Diekmann Cor 51).

## Main results (T028)

* `BernoulliRegular.isIdempotentElem_charIdempotent`: `ε_χ · ε_χ = ε_χ`.
* `BernoulliRegular.charIdempotent_mul_of_ne`: `ε_χ · ε_ψ = 0` for `χ ≠ ψ`.
* `BernoulliRegular.orthogonalIdempotents_charIdempotent`: the family
  `{ε_χ}` (indexed by `MulChar G R`) is a system of orthogonal idempotents.

## Main results (T029)

* `BernoulliRegular.MulChar.sum_characters_eq_zero_of_finite_group`: for a
  finite commutative group `G` and an integral domain `R` with enough roots
  of unity, `∑_χ χ a = 0` whenever `a ≠ 1` (generalisation of
  `DirichletCharacter.sum_characters_eq_zero` from `ZMod n` to any finite
  abelian group).
* `BernoulliRegular.MulChar.sum_characters_eq`: the conditional formula
  `∑_χ χ a = |G|` if `a = 1`, else `0`.
* `BernoulliRegular.charIdempotent_sum_eq_one`: the character idempotents
  sum to `1` in `R[G]` (Diekmann Lemma 50 (3)).
* `BernoulliRegular.completeOrthogonalIdempotents_charIdempotent`: the
  character idempotents form a complete orthogonal system.
* `BernoulliRegular.MonoidAlgebra.charComponentEquiv`: the ring-level
  decomposition `R[G] ≃+* ∏_χ (ε_χ).Corner` (Diekmann Cor 51).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Finset MonoidAlgebra MulChar

open scoped Ring

-- These theorems are stated without `DecidableEq G` appearing in their types,
-- even though their proofs manipulate sums indexed by `G` (which uses it
-- internally via `MonoidAlgebra.single`). We keep `DecidableEq G` as a
-- global hypothesis here since it is genuinely needed for the definition
-- of `charIdempotent` itself; the linter warnings are silenced.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
variable {R : Type*} [CommRing R]


variable [Invertible ((Fintype.card G : R))]


/-! ### Orthogonality of the idempotents (Diekmann Lemma 50)

We prove:
* `isIdempotentElem_charIdempotent`: `ε_χ · ε_χ = ε_χ`;
* `charIdempotent_mul_of_ne`: `ε_χ · ε_ψ = 0` for `χ ≠ ψ`;
* `orthogonalIdempotents_charIdempotent`: the family is a system of
  orthogonal idempotents.

The main computation is the identity

`(∑_σ χ σ • e_{σ⁻¹}) * (∑_τ ψ τ • e_{τ⁻¹})
    = (∑_σ χ σ · ψ σ⁻¹) • (∑_ρ ψ ρ • e_{ρ⁻¹})`

obtained by expanding via `single_mul_single` and reindexing
`τ ↦ σ⁻¹ τ` in the inner sum. The character inner sum then evaluates
to `|G|` when `χ = ψ` and to `0` when `χ ≠ ψ`.
-/

section Orthogonality

variable (χ ψ : MulChar G R)

end Orthogonality


/-! ### Character-sum orthogonality relations (T029 / Step A)

We generalise mathlib's `DirichletCharacter.sum_characters_eq_zero` and
`DirichletCharacter.sum_characters_eq` from Dirichlet characters (characters
on `ZMod n`) to characters of any finite commutative group `G`. These are
the core identities

* `∑_{χ : MulChar G R} χ a = 0`                 if `a ≠ 1`,
* `∑_{χ : MulChar G R} χ a = |G| : R`           if `a = 1`,

which then imply completeness of the character idempotents.

The proofs mirror mathlib's `ZMod n` arguments almost verbatim, using
`MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity` together with the
bijective reindexing `χ' ↦ χ · χ'` (via `Group.mulLeft_bijective`), and the
counting identity `Nat.card (MulChar G R) = Nat.card Gˣ = Nat.card G`
(the second equality since `G` is a group and `toUnits : G ≃* Gˣ`).
-/

section CharacterSumAndCompleteness

-- Shared hypotheses for Steps A, B, C, D.
variable [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent G)]

-- `MulChar G R` is `Finite` whenever `Gˣ` is and `R` is a domain; we
-- upgrade this to a `Fintype` instance so `Finset.sum` over characters
-- type-checks.
attribute [local instance] Fintype.ofFinite

-- For a group `G`, `Monoid.exponent Gˣ = Monoid.exponent G`: `toUnits : G ≃* Gˣ`.



/-! ### Completeness of the character idempotents (T029 / Step B)

The idempotents `ε_χ` sum to `1` in `R[G]`. The computation, writing
`n := |G|` and `n⁻¹` for its inverse, is

```
∑_χ ε_χ
  = n⁻¹ • ∑_χ ∑_σ χ(σ) • e_{σ⁻¹}
  = n⁻¹ • ∑_σ (∑_χ χ(σ)) • e_{σ⁻¹}                     (swap order)
  = n⁻¹ • (∑_{σ = 1} n • e_{1} + ∑_{σ ≠ 1} 0 • e_{σ⁻¹})  (sum_characters_eq)
  = n⁻¹ • (n • e_1)
  = e_1 = 1.
```
-/


/-! ### Complete orthogonal idempotents + ring decomposition (T029 / Steps C, D)

Packaging the results above we obtain:

* `completeOrthogonalIdempotents_charIdempotent`: the structure
  `CompleteOrthogonalIdempotents (fun χ => ε_χ)`;
* `MonoidAlgebra.charComponentEquiv`: the induced ring isomorphism
  `R[G] ≃+* ∏_χ (ε_χ).Corner` from `CompleteOrthogonalIdempotents.ringEquivOfComm`.

This is the content of Diekmann Corollary 51 at the level of the group
ring. Module-level decompositions `M = ⊕_χ ε_χ M` for `R[G]`-modules `M`
follow by extension of scalars; we record only the ring-level statement
here (Step D in the ticket plan).
-/



/-! ### Plus-minus decomposition (Diekmann Cor 52 / T030)

For an involution `c : G` (`c * c = 1`) and a coefficient ring `R` with
`2` invertible, we define

`ε_+(c) := (1 + c) / 2`  and  `ε_-(c) := (1 - c) / 2`

and show they form the "even/odd" projections in `R[G]`:

* `ε_+(c) + ε_-(c) = 1`
* `ε_+(c) = ∑_{χ : χ(c) = 1} ε_χ` and `ε_-(c) = ∑_{χ : χ(c) = -1} ε_χ`.

For the specialisation `G = (ZMod p)ˣ` and `c = -1`, these recover the
classical "even character part" and "odd character part" projections.
-/

section PlusMinus

variable [Inv2 : Invertible (2 : R)]








end PlusMinus

end CharacterSumAndCompleteness

end BernoulliRegular
