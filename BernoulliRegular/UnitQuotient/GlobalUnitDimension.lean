module

public import BernoulliRegular.UnitQuotient.FreeProjectorRanges
public import Mathlib.Algebra.Module.ZMod

/-!
# Unit quotients: global unit component dimensions

This file assembles `REF-07d`.  The map

```text
E / E^p -> (E / E_tors) / p
```

has the cyclotomic torsion line as kernel.  The kernel is the Teichmuller
line, so it has no even eigenspace.  Therefore the already proved free-part
dimension statement lifts to the actual quotient `E/E^p` for every nontrivial
even character.  The final theorem specializes this to the standard
`j`-power character with `2 <= j <= p - 3`.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

open Finset MonoidAlgebra

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

private theorem characterProjector_mem_eigenspace
    {G R M : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    [Field R] [AddCommGroup M] [Module R M]
    [Invertible (Fintype.card G : R)] [Invertible (2 : R)]
    [HasEnoughRootsOfUnity R (Monoid.exponent G)]
    (ρ : Representation R G M) (χ : MulChar G R) (x : M) :
    ∀ a : G,
      ρ a (ρ.asAlgebraHom (charIdempotent (G := G) (R := R) χ) x) =
        χ a • ρ.asAlgebraHom (charIdempotent (G := G) (R := R) χ) x := by
  intro a
  rw [← Representation.asAlgebraHom_single_one ρ a]
  rw [← Module.End.mul_apply, ← map_mul,
    single_mul_charIdempotent (G := G) (R := R) a χ, map_smul]
  rfl

/-- For a character `χ : G →* R`, the character idempotent acts as the
identity on its eigenspace: any `x` with `ρ a x = χ(a) · x` for every
`a ∈ G` is fixed by `e_χ`. -/
theorem characterProjector_apply_of_mem_eigenspace
    {G R M : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    [CommRing R] [AddCommGroup M] [Module R M]
    [Invertible (Fintype.card G : R)]
    (ρ : Representation R G M) (χ : MulChar G R) {x : M}
    (hx : ∀ a : G, ρ a x = χ a • x) :
    ρ.asAlgebraHom (charIdempotent (G := G) (R := R) χ) x = x := by
  classical
  calc
    ρ.asAlgebraHom (charIdempotent (G := G) (R := R) χ) x
        = ⅟(Fintype.card G : R) •
            ∑ a : G, χ a • ρ a⁻¹ x := by
          simp [charIdempotent_def, map_sum]
    _ = ⅟(Fintype.card G : R) • ∑ _a : G, x := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          rw [hx a⁻¹, smul_smul, ← map_mul, mul_inv_cancel, MulChar.map_one, one_smul]
    _ = x := by
          rw [Finset.sum_const, Finset.card_univ]
          rw [← Nat.cast_smul_eq_nsmul R (Fintype.card G) x]
          rw [smul_smul, invOf_mul_self, one_smul]

private theorem characterProjector_intertwines
    {G R V W : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    [Field R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [Invertible (Fintype.card G : R)]
    (ρV : Representation R G V) (ρW : Representation R G W)
    (f : V →ₗ[R] W) (hf : ∀ (a : G) (x : V), f (ρV a x) = ρW a (f x))
    (χ : MulChar G R) (x : V) :
    f (ρV.asAlgebraHom (charIdempotent (G := G) (R := R) χ) x) =
      ρW.asAlgebraHom (charIdempotent (G := G) (R := R) χ) (f x) := by
  classical
  simp [charIdempotent_def, map_sum, hf]

/-- For `p > 2`, the order of `Delta = (ZMod p)^*` is invertible in
`ZMod p`. -/
@[implicit_reducible]
noncomputable def cyclotomicUnitDeltaCardInvertibleZMod (hp_gt_two : 2 < p) :
    Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) := by
  rw [show Fintype.card (CyclotomicUnitDelta p) = p - 1 by rw [ZMod.card_units]]
  have hp_not_dvd : ¬ p ∣ p - 1 :=
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  exact invertibleOfCoprime (R := ZMod p)
    (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd).symm)

/-- `ZMod p` contains enough roots of unity for `Delta`. -/
theorem cyclotomicUnitDelta_hasEnoughRootsOfUnity_zmod :
    HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent (CyclotomicUnitDelta p)) := by
  haveI : NeZero (p - 1) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩
  exact HasEnoughRootsOfUnity.of_dvd (ZMod p)
    ((Group.exponent_dvd_card (G := CyclotomicUnitDelta p)).trans
      (by rw [ZMod.card_units]))

/-- Additive `ZMod p`-module structure on `E/E^p`. -/
instance cyclotomicUnitPowerQuotientModuleZMod :
    Module (ZMod p)
      (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    simpa using cyclotomicUnitPowerQuotient_pow_eq_one (p := p) (N := 1) K x.toMul

/-- The actual `Delta` action on `E/E^p`, as a `ZMod p`-linear action after
passing to additive notation. -/
noncomputable def cyclotomicUnitPowerQuotientLinearEquivZMod
    (a : CyclotomicUnitDelta p) :
    Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K) ≃ₗ[ZMod p]
      Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K) where
  toFun :=
    (MulEquiv.toAdditive
      ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).toFun
  invFun :=
    (MulEquiv.toAdditive
      ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).invFun
  left_inv :=
    (MulEquiv.toAdditive
      ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).left_inv
  right_inv :=
    (MulEquiv.toAdditive
      ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).right_inv
  map_add' :=
    (MulEquiv.toAdditive
      ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).map_add
  map_smul' c x :=
    ZMod.map_smul
      ((MulEquiv.toAdditive
        ((cyclotomicUnitModPDeltaAction (p := p) K).toMulAut a)).toAddMonoidHom) c x


/-- The actual `Delta` action on `E/E^p` as a linear representation. -/
noncomputable def cyclotomicUnitPowerQuotientDeltaActionZMod :
    CyclotomicUnitDelta p →*
      (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K) ≃ₗ[ZMod p]
        Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) where
  toFun := cyclotomicUnitPowerQuotientLinearEquivZMod (p := p) K
  map_one' := by
    ext x
    apply Additive.ext
    simp [cyclotomicUnitPowerQuotientLinearEquivZMod]
  map_mul' := by
    intro a b
    ext x
    apply Additive.ext
    simp [cyclotomicUnitPowerQuotientLinearEquivZMod]

/-- The actual `Delta` representation on `E/E^p`. -/
noncomputable def cyclotomicUnitPowerQuotientDeltaRepresentation :
    Representation (ZMod p) (CyclotomicUnitDelta p)
      (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K)


/-- The `χ`-eigenspace in the actual quotient `E/E^p`. -/
def cyclotomicUnitPowerQuotientDeltaCharacterEigenspace
    (χ : MulChar (CyclotomicUnitDelta p) (ZMod p)) :
    Submodule (ZMod p)
      (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) where
  carrier := {x | ∀ a,
    cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K a x = χ a • x}
  zero_mem' := by
    intro a
    simp
  add_mem' hx hy := by
    intro a
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' c x hx := by
    intro a
    rw [map_smul, hx a, smul_smul, smul_smul, mul_comm]

/-- The full `Delta` character projector on `E/E^p`. -/
noncomputable def cyclotomicUnitPowerQuotientDeltaCharacterProjector
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicUnitDelta p) (ZMod p)) :
    Module.End (ZMod p)
      (Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) := by
  classical
  letI : Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  exact (cyclotomicUnitPowerQuotientDeltaRepresentation (p := p) K).asAlgebraHom
    (charIdempotent (G := CyclotomicUnitDelta p) (R := ZMod p) χ)

theorem cyclotomicUnitPowerQuotientDeltaCharacterProjector_mem_eigenspace
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicUnitDelta p) (ZMod p))
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    cyclotomicUnitPowerQuotientDeltaCharacterProjector (p := p) K hp_gt_two χ x ∈
      cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K χ := by
  classical
  letI : Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  letI : Invertible (2 : ZMod p) := twoInvertibleZModOfPrimeGtTwo (p := p) hp_gt_two
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent (CyclotomicUnitDelta p)) :=
    cyclotomicUnitDelta_hasEnoughRootsOfUnity_zmod (p := p)
  exact characterProjector_mem_eigenspace
    (ρ := cyclotomicUnitPowerQuotientDeltaRepresentation (p := p) K) χ x

/-- The full `Delta` representation on the reduced free quotient. -/
noncomputable def cyclotomicUnitFreePartModPDeltaRepresentation :
    Representation (ZMod p) (CyclotomicUnitDelta p)
      (CyclotomicUnitFreePartModP (p := p) K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (cyclotomicUnitFreePartModPDeltaActionZMod (p := p) K)

/-- The full `Delta` character projector on the reduced free quotient. -/
noncomputable def cyclotomicUnitFreePartModPDeltaCharacterProjector
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicUnitDelta p) (ZMod p)) :
    Module.End (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) := by
  classical
  letI : Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  exact (cyclotomicUnitFreePartModPDeltaRepresentation (p := p) K).asAlgebraHom
    (charIdempotent (G := CyclotomicUnitDelta p) (R := ZMod p) χ)

/-- The map `E/E^p -> (E/E_tors)/p`, in additive `ZMod p`-linear form. -/
noncomputable def cyclotomicUnitPowerQuotientToFreePartModPLinear :
    Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K) →ₗ[ZMod p]
      CyclotomicUnitFreePartModP (p := p) K :=
  (MonoidHom.toAdditiveLeft
      (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K)).toZModLinearMap p



theorem cyclotomicUnitPowerQuotientToFreePartModPLinear_equivariant
    (a : CyclotomicUnitDelta p)
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K
        (cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K a x) =
      cyclotomicUnitFreePartModPDeltaActionZMod (p := p) K a
        (cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K x) := by
  have h :=
    cyclotomicUnitPowerQuotientToFreePartModP_equivariant
      (p := p) (K := K) a x.toMul
  change
    (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
        ((cyclotomicUnitModPDeltaAction (p := p) K).act a x.toMul)).toAdd =
      cyclotomicUnitFreePartModPLinearEquiv (p := p) K a
        ((cyclotomicUnitPowerQuotientToFreePartModP (p := p) K x.toMul).toAdd)
  simpa [cyclotomicUnitFreePartModPMulEquiv] using congrArg Multiplicative.toAdd h


theorem cyclotomicUnitPowerQuotientToFreePartModPLinear_projector
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicUnitDelta p) (ZMod p))
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K
        (cyclotomicUnitPowerQuotientDeltaCharacterProjector (p := p) K hp_gt_two χ x) =
      cyclotomicUnitFreePartModPDeltaCharacterProjector (p := p) K hp_gt_two χ
        (cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K x) := by
  classical
  letI : Invertible (Fintype.card (CyclotomicUnitDelta p) : ZMod p) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  exact characterProjector_intertwines
    (ρV := cyclotomicUnitPowerQuotientDeltaRepresentation (p := p) K)
    (ρW := cyclotomicUnitFreePartModPDeltaRepresentation (p := p) K)
    (f := cyclotomicUnitPowerQuotientToFreePartModPLinear (p := p) K)
    (fun a x => cyclotomicUnitPowerQuotientToFreePartModPLinear_equivariant
      (p := p) (K := K) a x)
    χ x











end BernoulliRegular

end
