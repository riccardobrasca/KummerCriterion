module

public import Mathlib.RingTheory.Teichmuller
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseUnitResidue

/-!
# Teichmüller residue-unit lifts at `lambda`

This file replaces the arbitrary residue lifts from
`KummerArtinHasseUnitResidue` by adic Teichmüller lifts in the completed
local integer ring.  This is the second piece of the explicit local
decomposition used by the Kummer--Artin--Hasse correction:

* identify the completed first residue quotient with the uncompleted residue
  quotient already used by the unit-residue map;
* construct the Teichmüller lift of each nonzero residue class;
* prove its residue and finite-order equations.

The construction uses `Perfection.teichmuller₀` and stays in the explicit
local model.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

-- The completed residue quotient instances expand through adic completion.
-- The explicit Teichmüller construction below repeatedly asks typeclass search
-- for the quotient ring structure, so this file raises the local budget.
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


/-- The residue quotient of the completed local integer ring. -/
abbrev LambdaCompletedResidueRing : Type _ :=
  LambdaLocalIntegerRing p K ⧸ LambdaMaximalIdeal p K

/-- The completed first residue quotient is canonically the same as the
uncompleted residue quotient, via `AdicCompletion.evalOneₐ`. -/
noncomputable def lambdaCompletedResidueEquivLocal :
    LambdaCompletedResidueRing p K ≃+* LambdaResidueRing p K :=
  (Ideal.quotEquivOfEq
      (Reflection.Local.completedLocalCyclotomicMaximalIdeal_eq_ker_evalOne
        (p := p) (K := K))).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (AdicCompletion.evalOneₐ
        (Reflection.Local.localCyclotomicMaximalIdeal p K)).toRingHom)
      (AdicCompletion.evalOneₐ_surjective
        (Reflection.Local.localCyclotomicMaximalIdeal p K)))


theorem lambdaCompletedResidueRing_natCard :
    Nat.card (LambdaCompletedResidueRing p K) = p :=
  (Nat.card_congr (lambdaCompletedResidueEquivLocal p K).toEquiv).trans
    (Reflection.Local.localCyclotomicResidueCard (p := p) (K := K))

instance lambdaCompletedResidueRing_finite :
    Finite (LambdaCompletedResidueRing p K) :=
  Nat.finite_of_card_ne_zero <| by
    rw [lambdaCompletedResidueRing_natCard (p := p) (K := K)]
    exact (Fact.out : Nat.Prime p).ne_zero

noncomputable instance lambdaCompletedResidueRing_fintype :
    Fintype (LambdaCompletedResidueRing p K) :=
  Fintype.ofFinite (LambdaCompletedResidueRing p K)

theorem lambdaCompletedResidueRing_card :
    Fintype.card (LambdaCompletedResidueRing p K) = p := by
  rw [← Nat.card_eq_fintype_card]
  exact lambdaCompletedResidueRing_natCard (p := p) (K := K)

instance lambdaCompletedResidueRing_charP :
    CharP (LambdaCompletedResidueRing p K) p :=
  charP_of_card_eq_prime (lambdaCompletedResidueRing_card (p := p) (K := K))

theorem lambdaCompletedResidueRing_pow_prime
    (x : LambdaCompletedResidueRing p K) :
    x ^ p = x := by
  let e : ZMod p ≃+* LambdaCompletedResidueRing p K :=
    ZMod.ringEquivOfPrime (LambdaCompletedResidueRing p K)
      (Fact.out : Nat.Prime p)
      (lambdaCompletedResidueRing_card (p := p) (K := K))
  calc
    x ^ p = e ((e.symm x) ^ p) := by
      rw [map_pow, RingEquiv.apply_symm_apply]
    _ = e (e.symm x) := by rw [ZMod.pow_card]
    _ = x := by simp

theorem lambdaCompletedResidueRing_symm_residueUnit_ne_zero
    (a : LambdaResidueUnitGroup p K) :
    (lambdaCompletedResidueEquivLocal p K).symm (a : LambdaResidueRing p K) ≠ 0 := by
  intro h
  have ha0 : (a : LambdaResidueRing p K) = 0 := by
    rw [← (lambdaCompletedResidueEquivLocal p K).apply_symm_apply
      (a : LambdaResidueRing p K), h, map_zero]
  exact a.ne_zero ha0

theorem lambdaCompletedResidueRing_symm_residueUnit_pow_sub_one
    (a : LambdaResidueUnitGroup p K) :
    ((lambdaCompletedResidueEquivLocal p K).symm (a : LambdaResidueRing p K)) ^
        (p - 1) = 1 := by
  let e : ZMod p ≃+* LambdaCompletedResidueRing p K :=
    ZMod.ringEquivOfPrime (LambdaCompletedResidueRing p K)
      (Fact.out : Nat.Prime p)
      (lambdaCompletedResidueRing_card (p := p) (K := K))
  have hc_ne :
      e.symm ((lambdaCompletedResidueEquivLocal p K).symm
        (a : LambdaResidueRing p K)) ≠ 0 := fun h =>
    lambdaCompletedResidueRing_symm_residueUnit_ne_zero (p := p) (K := K) a
      (by
        rw [← e.apply_symm_apply
          ((lambdaCompletedResidueEquivLocal p K).symm (a : LambdaResidueRing p K)),
          h, map_zero])
  calc
    ((lambdaCompletedResidueEquivLocal p K).symm (a : LambdaResidueRing p K)) ^
        (p - 1) =
      e ((e.symm ((lambdaCompletedResidueEquivLocal p K).symm
        (a : LambdaResidueRing p K))) ^ (p - 1)) := by
        rw [map_pow, RingEquiv.apply_symm_apply]
    _ = e 1 := by rw [ZMod.pow_card_sub_one_eq_one hc_ne]
    _ = 1 := by simp

/-- The constant perfection element attached to a nonzero residue class. -/
noncomputable def lambdaTeichmullerInput
    (a : LambdaResidueUnitGroup p K) :
    Perfection (LambdaCompletedResidueRing p K) p :=
  ⟨fun _ => (lambdaCompletedResidueEquivLocal p K).symm a,
    fun _ => lambdaCompletedResidueRing_pow_prime (p := p) (K := K) _⟩












end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
