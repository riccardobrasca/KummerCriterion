module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ModPRepresentation

/-!
# Unit quotients: actual free quotient eigenspaces

This file packages the actual Delta and even-Delta eigenspaces in the reduced
free quotient, proves projector landing and decomposition statements, and
records the odd-character vanishing result.
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


/-- The actual `χ`-eigenspace of the reduced free quotient for the factored
`Delta / {±1}` action. -/
def cyclotomicUnitFreePartModPEvenCharacterEigenspace
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p)) :
    Submodule (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) where
  carrier := {x | ∀ a,
    cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two a x =
      χ a • x}
  zero_mem' := by
    intro a
    simp
  add_mem' hx hy := by
    intro a
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' c x hx := by
    intro a
    rw [map_smul, hx a, smul_smul, smul_smul, mul_comm]




/-- The character idempotent projector lands in the corresponding actual
eigenspace. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p))
    (x : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x ∈
      cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ := by
  classical
  letI : Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
    cyclotomicEvenDeltaCardInvertibleZMod (p := p) hp_gt_two
  letI : Invertible (2 : ZMod p) :=
    twoInvertibleZModOfPrimeGtTwo (p := p) hp_gt_two
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent (CyclotomicEvenDelta p)) :=
    cyclotomicEvenDelta_hasEnoughRootsOfUnity_zmod (p := p)
  intro a
  change
    cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two a
        (cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x) =
      χ a • cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x
  rw [← Representation.asAlgebraHom_single_one
    (cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two) a]
  simp only [cyclotomicUnitFreePartModPEvenCharacterProjector]
  rw [← Module.End.mul_apply, ← map_mul,
    single_mul_charIdempotent (G := CyclotomicEvenDelta p) (R := ZMod p) a χ, map_smul]
  rfl

/-- The character idempotent projectors sum to the identity on the reduced
free quotient. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_sum_apply
    (hp_gt_two : 2 < p) (x : CyclotomicUnitFreePartModP (p := p) K) :
    (∑ χ : MulChar (CyclotomicEvenDelta p) (ZMod p),
        cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x) = x := by
  classical
  letI : Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
    cyclotomicEvenDeltaCardInvertibleZMod (p := p) hp_gt_two
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent (CyclotomicEvenDelta p)) :=
    cyclotomicEvenDelta_hasEnoughRootsOfUnity_zmod (p := p)
  let ρ := cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two
  calc
    (∑ χ : MulChar (CyclotomicEvenDelta p) (ZMod p),
        cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x)
        = (ρ.asAlgebraHom
            (∑ χ : MulChar (CyclotomicEvenDelta p) (ZMod p),
              charIdempotent (G := CyclotomicEvenDelta p) (R := ZMod p) χ)) x := by
            simp [cyclotomicUnitFreePartModPEvenCharacterProjector, ρ, map_sum]
    _ = x := by
      rw [charIdempotent_sum_eq_one (G := CyclotomicEvenDelta p) (R := ZMod p)]
      simp [ρ]




/-- Distinct even characters have disjoint actual eigenspaces in the reduced
free quotient. -/
theorem cyclotomicUnitFreePartModPEvenCharacterEigenspace_inf_eq_bot_of_ne
    (hp_gt_two : 2 < p)
    {χ ψ : MulChar (CyclotomicEvenDelta p) (ZMod p)} (hχψ : χ ≠ ψ) :
    cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ ⊓
      cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two ψ =
        ⊥ := by
  classical
  have hsep : ∃ a, χ a ≠ ψ a := by
    by_contra h
    apply hχψ
    ext a
    by_contra ha
    exact h ⟨a, ha⟩
  rcases hsep with ⟨a, ha⟩
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_bot]
    have hxχ := hx.1 a
    have hxψ := hx.2 a
    have hsame : χ a • x = ψ a • x := by
      rw [← hxχ, ← hxψ]
    have hzero : (χ a - ψ a) • x = 0 := by
      rw [sub_smul, hsame, sub_self]
    exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ha)
  · intro hx
    rw [Submodule.mem_bot] at hx
    rw [hx]
    exact Submodule.zero_mem _


end BernoulliRegular

end
