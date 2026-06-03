module

public import KummerCriterion.UnitQuotient.PermutationCharacters
public import KummerCriterion.UnitQuotient.DeltaAction
public import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.RingTheory.ZMod.Torsion

/-!
# Unit quotients: the free character profile

This file records the representation-theoretic closing statement for the free
unit contribution. The permutation representation of
`Delta / {±1}` contains one copy of every quotient character. The free unit
part corresponds to the augmentation subrepresentation, so the trivial line is
removed and each nontrivial quotient character occurs with multiplicity one.

The comparison between the actual Dirichlet unit lattice and this augmentation
representation is the remaining number-theoretic input needed to turn this
abstract profile into the final `E/E^p` component statement.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

attribute [local instance] Fintype.ofFinite

variable (p : ℕ) [Fact p.Prime]

/-- For `p > 2`, the subgroup `{±1}` of `Delta = (ZMod p)^*` has order two. -/
theorem cyclotomicEvenDeltaSubgroup_card (hp_gt_two : 2 < p) :
    Fintype.card (CyclotomicEvenDeltaSubgroup p) = 2 := by
  change Fintype.card (Subgroup.zpowers (-1 : CyclotomicUnitDelta p)) = 2
  rw [Fintype.card_zpowers]
  have hp_ne_two : p ≠ 2 := by omega
  rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod p) p,
    if_neg hp_ne_two]

/-- For `p > 2`, the quotient `Delta / {±1}` has order `(p - 1) / 2`. -/
theorem cyclotomicEvenDelta_card (hp_gt_two : 2 < p) :
    Fintype.card (CyclotomicEvenDelta p) = (p - 1) / 2 := by
  have hcard :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CyclotomicEvenDeltaSubgroup p)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    show Fintype.card (CyclotomicUnitDelta p) = p - 1 by rw [ZMod.card_units],
    cyclotomicEvenDeltaSubgroup_card (p := p) hp_gt_two] at hcard
  have hmul : 2 * Fintype.card (CyclotomicEvenDelta p) = p - 1 := by
    rw [mul_comm]
    exact hcard.symm
  exact Nat.eq_div_of_mul_eq_right (by decide) hmul

end KummerCriterion

end
