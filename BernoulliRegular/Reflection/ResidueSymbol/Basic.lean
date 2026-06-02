module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Power residue symbols

This file defines the finite-field and prime-ideal pieces of the power
residue symbol API used in the reflection argument. The ideal-level API keeps
the coprimality predicate explicit, so later reciprocity statements can record
their exact local hypotheses without hiding them in typeclass search.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace ResidueSymbol

namespace PowerResidue

open UniqueFactorizationMonoid

variable {k : Type*} [Field k] [Fintype k]
variable {p : ℕ}

/-- The finite-field value `x ^ ((#k - 1) / p)` used in the `p`-th power
residue symbol. -/
def finiteFieldUnit (_hdiv : p ∣ Fintype.card k - 1) (x : kˣ) : kˣ :=
  x ^ ((Fintype.card k - 1) / p)

theorem finiteFieldUnit_pow_eq_one (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    finiteFieldUnit hdiv x ^ p = 1 := by
  apply Units.ext
  change ((x : k) ^ ((Fintype.card k - 1) / p)) ^ p = (1 : k)
  rw [← pow_mul, Nat.div_mul_cancel hdiv]
  exact _root_.FiniteField.pow_card_sub_one_eq_one (x : k) x.ne_zero

theorem finiteFieldUnit_mem_zpowers [NeZero p] {zeta : kˣ} (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    finiteFieldUnit hdiv x ∈ Subgroup.zpowers zeta := by
  rw [hzeta.zpowers_eq]
  rw [mem_rootsOfUnity]
  exact finiteFieldUnit_pow_eq_one hdiv x

/-- Exponent form of the finite-field power residue symbol with respect to a
chosen primitive `p`-th root of unity. The actual residue-symbol value is
`zeta ^ finiteFieldExponent`. -/
def finiteFieldExponent [NeZero p] (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) : ZMod p :=
  hzeta.zmodEquivZPowers.symm
    (Additive.ofMul ⟨finiteFieldUnit hdiv x, finiteFieldUnit_mem_zpowers hzeta hdiv x⟩)

/-- The exponent form recovers the concrete finite-field unit
`x ^ ((#k - 1) / p)`. -/
theorem zeta_pow_finiteFieldExponent_val [NeZero p]
    {zeta : kˣ} (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    zeta ^ (finiteFieldExponent zeta hzeta hdiv x).val = finiteFieldUnit hdiv x := by
  have h := hzeta.zmodEquivZPowers.apply_symm_apply
    (Additive.ofMul
      (⟨finiteFieldUnit hdiv x, finiteFieldUnit_mem_zpowers hzeta hdiv x⟩ :
        Subgroup.zpowers zeta))
  have happ := congrArg (fun y : Additive (Subgroup.zpowers zeta) =>
    ((Additive.toMul y : Subgroup.zpowers zeta) : kˣ)) h
  change ((Additive.toMul
      (hzeta.zmodEquivZPowers (finiteFieldExponent zeta hzeta hdiv x)) :
        Subgroup.zpowers zeta) : kˣ) = finiteFieldUnit hdiv x at happ
  rw [← ZMod.natCast_zmod_val (finiteFieldExponent zeta hzeta hdiv x)] at happ
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat] at happ
  exact happ

theorem finiteFieldUnit_mul (hdiv : p ∣ Fintype.card k - 1) (x y : kˣ) :
    finiteFieldUnit hdiv (x * y) = finiteFieldUnit hdiv x * finiteFieldUnit hdiv y := by
  ext
  simp [finiteFieldUnit, mul_pow]



theorem finiteFieldExponent_mul [NeZero p] (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x y : kˣ) :
    finiteFieldExponent zeta hzeta hdiv (x * y) =
      finiteFieldExponent zeta hzeta hdiv x + finiteFieldExponent zeta hzeta hdiv y := by
  apply hzeta.zmodEquivZPowers.injective
  rw [map_add]
  simp only [finiteFieldExponent, AddEquiv.apply_symm_apply]
  ext
  exact congrArg (fun u : kˣ => (u : k)) (finiteFieldUnit_mul hdiv x y)









section PrimeIdeal

variable {R : Type*} [CommRing R]
variable (q : Ideal R) [q.IsMaximal]

/-- A quotient class represented by an element not in the prime ideal, as a
unit of the residue field. -/
def quotientUnitOfNotMem (x : R) (hx : x ∉ q) : (R ⧸ q)ˣ :=
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  Units.mk0 (Ideal.Quotient.mk q x) (by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hx)

theorem quotientUnitOfNotMem_mul {x y : R} (hx : x ∉ q) (hy : y ∉ q)
    (hxy : x * y ∉ q) :
    quotientUnitOfNotMem q (x * y) hxy =
      quotientUnitOfNotMem q x hx * quotientUnitOfNotMem q y hy := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  ext
  simp [quotientUnitOfNotMem]

/-- The `p`-th power residue symbol at a maximal ideal, in exponent form with
respect to a chosen primitive root of unity in the residue field. -/
def primeExponent {p : ℕ} [NeZero p] [Fintype (R ⧸ q)] (zeta_q : (R ⧸ q)ˣ)
    (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card (R ⧸ q) - 1) (x : R) (hx : x ∉ q) : ZMod p := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  exact finiteFieldExponent zeta_q hzeta_q hdiv (quotientUnitOfNotMem q x hx)

theorem primeExponent_mul {p : ℕ} [NeZero p] [Fintype (R ⧸ q)] (zeta_q : (R ⧸ q)ˣ)
    (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card (R ⧸ q) - 1) {x y : R}
    (hx : x ∉ q) (hy : y ∉ q) (hxy : x * y ∉ q) :
    primeExponent q zeta_q hzeta_q hdiv (x * y) hxy =
      primeExponent q zeta_q hzeta_q hdiv x hx +
        primeExponent q zeta_q hzeta_q hdiv y hy := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  rw [primeExponent, primeExponent, primeExponent]
  rw [← finiteFieldExponent_mul]
  congr
  exact quotientUnitOfNotMem_mul q hx hy hxy






end PrimeIdeal

section Ideals

variable {R : Type*} [CommRing R]


/-- Interface for an ideal-level power residue symbol away from `p * eta`.

The concrete construction by prime-ideal factorization is intentionally kept
separate from the API: downstream reciprocity theorems only need the symbol,
its coprimality domain, and multiplicativity. -/
structure IdealSymbol (p : ℕ) (eta : R) where

section IdealFactorization

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {p : ℕ}





end IdealFactorization

end Ideals

end PowerResidue

end ResidueSymbol
end Reflection
end BernoulliRegular
