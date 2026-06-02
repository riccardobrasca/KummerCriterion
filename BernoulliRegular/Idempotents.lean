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

/-- The character idempotent `ε_χ := (1/|G|) ∑_{σ ∈ G} χ(σ) · σ⁻¹ ∈ R[G]`
associated to a multiplicative character `χ : MulChar G R`. -/
def charIdempotent [Invertible ((Fintype.card G : R))] (χ : MulChar G R) :
    MonoidAlgebra R G :=
  ⅟(Fintype.card G : R) • ∑ σ : G, χ σ • MonoidAlgebra.single σ⁻¹ (1 : R)

variable [Invertible ((Fintype.card G : R))]

@[simp] lemma charIdempotent_def (χ : MulChar G R) :
    charIdempotent χ =
      ⅟(Fintype.card G : R) • ∑ σ : G, χ σ • MonoidAlgebra.single σ⁻¹ (1 : R) := rfl

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

/-- The explicit expansion of `ε_χ · ε_ψ` as a scalar multiple of the
basic character-weighted sum. Independent of whether `χ = ψ`. -/
lemma charIdempotent_mul_aux :
    charIdempotent χ * charIdempotent ψ =
      (⅟(Fintype.card G : R) * ⅟(Fintype.card G : R)) •
        ((∑ σ : G, χ σ * ψ σ⁻¹) •
          (∑ ρ : G, ψ ρ • MonoidAlgebra.single ρ⁻¹ (1 : R))) := by
  -- Pull out the two scalar factors and expand the product of sums.
  simp only [charIdempotent_def]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, Finset.sum_mul_sum]
  congr 1
  -- Reindex the inner sum `τ ↦ σ⁻¹ * ρ`. For each σ, this is a bijection.
  have inner : ∀ σ : G,
      (∑ τ : G, (χ σ • MonoidAlgebra.single σ⁻¹ (1 : R)) *
          (ψ τ • MonoidAlgebra.single τ⁻¹ (1 : R)))
      = ∑ ρ : G, (χ σ * ψ (σ⁻¹ * ρ)) • MonoidAlgebra.single ρ⁻¹ (1 : R) := by
    intro σ
    rw [← (Group.mulLeft_bijective σ⁻¹).sum_comp
      (g := fun τ => (χ σ • MonoidAlgebra.single σ⁻¹ (1 : R)) *
        (ψ τ • MonoidAlgebra.single τ⁻¹ (1 : R)))]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    -- single σ⁻¹ 1 * single (σ⁻¹ ρ)⁻¹ 1 = single ρ⁻¹ 1 (via `single_mul_single`).
    rw [smul_mul_assoc, mul_smul_comm, MonoidAlgebra.single_mul_single, mul_one,
      smul_smul]
    congr 2
    -- σ⁻¹ * (σ⁻¹ * ρ)⁻¹ = σ⁻¹ * (ρ⁻¹ * σ) = ρ⁻¹ (using CommGroup).
    rw [mul_inv_rev, inv_inv, ← mul_assoc, mul_comm σ⁻¹ ρ⁻¹, mul_assoc,
      inv_mul_cancel, mul_one]
  -- Now rewrite each inner sum and then factor using ∑ σ ∑ ρ = ∑ ρ ∑ σ.
  simp_rw [inner]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  -- Goal: ∑ σ, (χ σ * ψ (σ⁻¹ * ρ)) • e_{ρ⁻¹}
  --     = (∑ σ, χ σ * ψ σ⁻¹) • ψ ρ • e_{ρ⁻¹}
  rw [smul_smul, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, mul_assoc]

/-- The "inner character sum" `∑_σ χ σ · χ σ⁻¹` equals `|G|` for any character `χ`.
This is the diagonal case used to prove `ε_χ² = ε_χ`. -/
lemma sum_char_mul_char_inv_self :
    (∑ σ : G, χ σ * χ σ⁻¹) = (Fintype.card G : R) := by
  -- `χ σ * χ σ⁻¹ = χ (σ * σ⁻¹) = χ 1 = 1` for every σ, so the sum is `|G| * 1`.
  simp only [← map_mul, mul_inv_cancel, MulChar.map_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]




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
lemma hasEnoughRootsOfUnity_units_of_group :
    HasEnoughRootsOfUnity R (Monoid.exponent Gˣ) := by
  rw [Monoid.exponent_eq_of_mulEquiv (toUnits (G := G)).symm]
  infer_instance

/-- Generalisation of `DirichletCharacter.sum_characters_eq_zero` to any
finite commutative group `G`: for `a ≠ 1`, the sum of `χ a` over all
multiplicative characters `χ : MulChar G R` vanishes. -/
theorem MulChar.sum_characters_eq_zero_of_finite_group
    {a : G} (ha : a ≠ 1) :
    ∑ χ : MulChar G R, χ a = 0 := by
  have := hasEnoughRootsOfUnity_units_of_group (G := G) (R := R)
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity G R ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun _ ↦ rfl

/-- Generalisation of `DirichletCharacter.sum_characters_eq`: for any
`a : G`, the sum of `χ a` over all multiplicative characters
`χ : MulChar G R` equals `|G|` when `a = 1`, and `0` otherwise. -/
theorem MulChar.sum_characters_eq (a : G) :
    ∑ χ : MulChar G R, χ a =
      if a = 1 then (Fintype.card G : R) else 0 := by
  split_ifs with ha
  · -- `a = 1`: every character sends `1` to `1`, so the sum is `|MulChar G R|`.
    have := hasEnoughRootsOfUnity_units_of_group (G := G) (R := R)
    have hcardEq : Nat.card (MulChar G R) = Nat.card G :=
      (MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity G R).trans
        (Nat.card_congr (toUnits (G := G)).symm.toEquiv)
    simpa only [ha, MulChar.map_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card]
      using congrArg (Nat.cast (R := R)) hcardEq
  · exact MulChar.sum_characters_eq_zero_of_finite_group ha

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

/-- **Diekmann Lemma 50 (part 3)**: the family of character idempotents
`{ε_χ : χ : MulChar G R}` is complete, i.e. sums to `1` in `R[G]`. -/
theorem charIdempotent_sum_eq_one :
    ∑ χ : MulChar G R, charIdempotent χ = (1 : MonoidAlgebra R G) := by
  -- Expand the definition of `charIdempotent`, pull the common scalar
  -- `⅟|G|` out, swap the order of summation, and apply `sum_characters_eq`.
  simp only [charIdempotent_def]
  rw [← Finset.smul_sum, Finset.sum_comm]
  -- Goal: `⅟|G| • ∑ σ, ∑ χ, χ σ • single σ⁻¹ 1 = 1`.
  -- Inner sum: `∑ χ, χ σ • single σ⁻¹ 1 = ite (σ = 1) (|G| • single σ⁻¹ 1) 0`.
  -- After this rewrite, only `σ = 1` survives in the outer sum.
  have hrw : ∀ σ : G,
      (∑ χ : MulChar G R, χ σ • MonoidAlgebra.single σ⁻¹ (1 : R))
        = if σ = 1 then
            (Fintype.card G : R) • MonoidAlgebra.single σ⁻¹ (1 : R)
          else 0 := by
    intro σ
    rw [← Finset.sum_smul, MulChar.sum_characters_eq]
    split_ifs <;> simp only [zero_smul]
  simp_rw [hrw]
  rw [Finset.sum_ite_eq' Finset.univ (1 : G)
    (fun σ => ((Fintype.card G : R)) • MonoidAlgebra.single σ⁻¹ (1 : R)), if_pos]
  · -- Goal: `⅟|G| • (|G| • single (1:G)⁻¹ 1) = 1`.
    rw [inv_one, smul_smul, invOf_mul_self, one_smul]; rfl
  · exact Finset.mem_univ _

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




/-- Key computational identity: multiplication by `single c 1` scales each
character idempotent `ε_χ` by the eigenvalue `χ c`. -/
lemma single_mul_charIdempotent (c : G) (χ : MulChar G R) :
    MonoidAlgebra.single c (1 : R) * charIdempotent χ = χ c • charIdempotent χ := by
  rw [charIdempotent_def, mul_smul_comm, smul_comm (χ c) (⅟((Fintype.card G : R)))]
  congr 1
  calc MonoidAlgebra.single c (1 : R) *
      ∑ σ : G, χ σ • MonoidAlgebra.single σ⁻¹ (1 : R)
      = ∑ σ : G, χ σ • MonoidAlgebra.single (c * σ⁻¹) (1 : R) := by
        simp_rw [Finset.mul_sum, mul_smul_comm, MonoidAlgebra.single_mul_single, mul_one]
    _ = ∑ σ : G, χ (σ * c) • MonoidAlgebra.single (c * (σ * c)⁻¹) (1 : R) :=
        ((Group.mulRight_bijective c).sum_comp
          (fun σ => χ σ • MonoidAlgebra.single (c * σ⁻¹) (1 : R))).symm
    _ = ∑ σ : G, (χ c * χ σ) • MonoidAlgebra.single σ⁻¹ (1 : R) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [map_mul, mul_comm (χ σ) (χ c), mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = χ c • ∑ σ : G, χ σ • MonoidAlgebra.single σ⁻¹ (1 : R) := by
        simp_rw [Finset.smul_sum, smul_smul]




end PlusMinus

end CharacterSumAndCompleteness

end BernoulliRegular
