module

public import BernoulliRegular.UnitQuotient.ModPReduction
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.RingTheory.ZMod.Torsion

/-!
# Unit quotients: the free character profile

This file records the representation-theoretic closing statement for the free
unit contribution.  The permutation representation of
`Delta / {±1}` contains one copy of every quotient character.  The free unit
part corresponds to the augmentation subrepresentation, so the trivial line is
removed and each nontrivial quotient character occurs with multiplicity one.

The comparison between the actual Dirichlet unit lattice and this augmentation
representation is the remaining number-theoretic input needed to turn this
abstract profile into the final `E/E^p` component statement.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

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

/-- The order of `Delta / {±1}` divides `p - 1`. -/
theorem cyclotomicEvenDelta_card_dvd_p_sub_one :
    Fintype.card (CyclotomicEvenDelta p) ∣ p - 1 := by
  have hcard :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CyclotomicEvenDeltaSubgroup p)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    show Fintype.card (CyclotomicUnitDelta p) = p - 1 by rw [ZMod.card_units]] at hcard
  exact ⟨Fintype.card (CyclotomicEvenDeltaSubgroup p), hcard⟩

/-- For `p > 2`, `p` does not divide the order of `Delta / {±1}`. -/
theorem cyclotomicEvenDelta_card_not_dvd_p (hp_gt_two : 2 < p) :
    ¬ p ∣ Fintype.card (CyclotomicEvenDelta p) := by
  have hlt : Fintype.card (CyclotomicEvenDelta p) < p := by
    rw [cyclotomicEvenDelta_card (p := p) hp_gt_two]
    omega
  intro hdiv
  exact not_le_of_gt hlt (Nat.le_of_dvd (Fintype.card_pos) hdiv)

/-- For `p > 2`, the order of `Delta / {±1}` is invertible in `ZMod p`. -/
@[implicit_reducible]
noncomputable def cyclotomicEvenDeltaCardInvertibleZMod (hp_gt_two : 2 < p) :
    Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
  invertibleOfCoprime (R := ZMod p)
    (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (cyclotomicEvenDelta_card_not_dvd_p (p := p) hp_gt_two)).symm)

/-- For `p > 2`, `2` is invertible in `ZMod p`. -/
@[implicit_reducible]
noncomputable def twoInvertibleZModOfPrimeGtTwo (hp_gt_two : 2 < p) :
    Invertible (2 : ZMod p) := by
  have hp_not_dvd_two : ¬ p ∣ 2 := fun hdiv =>
    not_le_of_gt hp_gt_two (Nat.le_of_dvd (by decide) hdiv)
  exact invertibleOfCoprime (R := ZMod p)
    (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_two).symm)

/-- `ZMod p` contains enough roots of unity for the quotient `Delta / {±1}`. -/
theorem cyclotomicEvenDelta_hasEnoughRootsOfUnity_zmod :
    HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent (CyclotomicEvenDelta p)) := by
  haveI : NeZero (p - 1) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩
  exact HasEnoughRootsOfUnity.of_dvd (ZMod p)
    ((Group.exponent_dvd_card (G := CyclotomicEvenDelta p)).trans
      (cyclotomicEvenDelta_card_dvd_p_sub_one (p := p)))







end BernoulliRegular

end
