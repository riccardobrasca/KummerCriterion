module

public import BernoulliRegular.UnitQuotient.FreeCharacterProfile

/-!
# Unit quotients: complex conjugation and augmentation traces

This file identifies the action of -1 with complex conjugation on infinite
places and computes the trace of the augmentation action through the even
quotient.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

open Finset

set_option linter.unusedSectionVars false

attribute [local instance] Fintype.ofFinite
attribute [local instance] NumberField.Units.instZLattice_unitLattice

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Complex conjugation as a rational Galois automorphism of the cyclotomic
field. -/
noncomputable def cyclotomicComplexConjGal
    (hp_gt_two : 2 < p) : Gal(K / ℚ) := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.IsCMField K hp_gt_two
  exact
    { (NumberField.IsCMField.complexConj K).toRingEquiv with
      commutes' := fun q => by
        exact map_ratCast
          ((NumberField.IsCMField.complexConj K).toRingEquiv.toRingHom) q }

/-- Under the standard cyclotomic Galois identification, complex conjugation
is the element `-1` of `(ZMod p)^*`. -/
theorem cyclotomicGalEquivZMod_complexConjGal_eq_neg_one
    (hp_gt_two : 2 < p) :
    cyclotomicGalEquivZMod (p := p) K
        (cyclotomicComplexConjGal (p := p) K hp_gt_two) = -1 := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.IsCMField K hp_gt_two
  let c : Gal(K / ℚ) := cyclotomicComplexConjGal (p := p) K hp_gt_two
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hzeta_torsion : hζ.unit' ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _ _).2
      (isOfFinOrder_iff_pow_eq_one.2
        ⟨p, (Fact.out : p.Prime).pos, hζ.unit'_pow⟩)
  have hconj_inv :
      NumberField.IsCMField.complexConj K
          (IsCyclotomicExtension.zeta p ℚ K) =
        (IsCyclotomicExtension.zeta p ℚ K)⁻¹ := by
    have hconj :=
      NumberField.IsCMField.complexConj_torsion
        (K := K) ⟨hζ.unit', hzeta_torsion⟩
    simpa using hconj
  have hζ_inv :
      (IsCyclotomicExtension.zeta p ℚ K)⁻¹ =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_one_add_one (Fact.out : p.Prime).ne_zero]
    exact hζ.pow_eq_one
  have hc :
      c (IsCyclotomicExtension.zeta p ℚ K) =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    simpa [c, cyclotomicComplexConjGal, hζ_inv] using hconj_inv
  have hpow :
      (IsCyclotomicExtension.zeta p ℚ K) ^
          (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    calc
      (IsCyclotomicExtension.zeta p ℚ K) ^
          (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val
          = c (IsCyclotomicExtension.zeta p ℚ K) := by
              symm
              exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
                (n := p) (K := K) c hζ.pow_eq_one
      _ = (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := hc
  apply Units.ext
  have hpow' := hpow
  rw [(hζ.isOfFinOrder (Fact.out : p.Prime).ne_zero).pow_inj_mod, ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val,
    Nat.cast_sub (Fact.out : p.Prime).one_le,
    ZMod.natCast_self, zero_sub, Nat.cast_one] at hpow'
  simpa [c, cyclotomicGalEquivZMod] using hpow'

/-- The Galois automorphism indexed by `-1` is complex conjugation. -/
theorem cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal
    (hp_gt_two : 2 < p) :
    cyclotomicSigmaOfUnit (p := p) K (-1) =
      cyclotomicComplexConjGal (p := p) K hp_gt_two := by
  apply (cyclotomicGalEquivZMod (p := p) K).injective
  rw [cyclotomicGalEquivZMod_sigmaOfUnit,
    cyclotomicGalEquivZMod_complexConjGal_eq_neg_one (p := p) (K := K) hp_gt_two]

end BernoulliRegular

end
