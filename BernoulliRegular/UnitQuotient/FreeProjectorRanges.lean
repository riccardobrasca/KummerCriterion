module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison
public import Mathlib.LinearAlgebra.Projection

/-!
# Unit quotients: ranges of free-unit character projectors

This file continues `REF-07c6c2b`.  The actual reduced free-unit quotient has
character idempotent projectors for the factored action of `Delta / {±1}`.
Here we prove that these projectors are precisely the projections onto the
actual character eigenspaces.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

attribute [local instance] Fintype.ofFinite

private theorem LinearMap.trace_eq_finrank_range_of_isIdempotentElem
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e : Module.End F V) (he : IsIdempotentElem e) :
    LinearMap.trace F V e = (Module.finrank F (LinearMap.range e) : F) := by
  classical
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    LinearMap.IsIdempotentElem.isProj_range e he
  calc
    LinearMap.trace F V e =
        LinearMap.trace F V
          (((LinearMap.range e).prodEquivOfIsCompl (LinearMap.ker e) hproj.isCompl).conj
            (LinearMap.prodMap LinearMap.id 0)) :=
          congrArg (LinearMap.trace F V)
            (LinearMap.IsProj.eq_conj_prodMap hproj)
    _ = LinearMap.trace F ((LinearMap.range e) × (LinearMap.ker e))
          (LinearMap.prodMap LinearMap.id 0) := by
          rw [LinearMap.trace_conj']
    _ = (Module.finrank F (LinearMap.range e) : F) := by
          rw [LinearMap.trace_prodMap']
          simp

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Character projectors commute with the factored even `Delta` action. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_commute_action
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p))
    (a : CyclotomicEvenDelta p)
    (x : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two a
        (cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x) =
      cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ
        (cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two a x) := by
  classical
  letI : Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
    cyclotomicEvenDeltaCardInvertibleZMod (p := p) hp_gt_two
  let ρ := cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two
  change ρ a
        (cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x) =
      cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ (ρ a x)
  rw [← Representation.asAlgebraHom_single_one ρ a]
  change
    ρ.asAlgebraHom (MonoidAlgebra.single a (1 : ZMod p))
        ((ρ.asAlgebraHom
          (charIdempotent (G := CyclotomicEvenDelta p) (R := ZMod p) χ)) x) =
      (ρ.asAlgebraHom
        (charIdempotent (G := CyclotomicEvenDelta p) (R := ZMod p) χ))
        (ρ.asAlgebraHom (MonoidAlgebra.single a (1 : ZMod p)) x)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

/-- A character projector preserves every actual even-character eigenspace. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace_of_mem
    (hp_gt_two : 2 < p)
    (χ ψ : MulChar (CyclotomicEvenDelta p) (ZMod p))
    {x : CyclotomicUnitFreePartModP (p := p) K}
    (hx : x ∈ cyclotomicUnitFreePartModPEvenCharacterEigenspace
      (p := p) K hp_gt_two ψ) :
    cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x ∈
      cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two ψ := by
  intro a
  rw [cyclotomicUnitFreePartModPEvenCharacterProjector_commute_action
    (p := p) (K := K) hp_gt_two χ a x, hx a, map_smul]

/-- On the `χ`-eigenspace, every different character projector vanishes. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_apply_eq_zero_of_mem_ne
    (hp_gt_two : 2 < p)
    {χ ψ : MulChar (CyclotomicEvenDelta p) (ZMod p)} (hχψ : χ ≠ ψ)
    {x : CyclotomicUnitFreePartModP (p := p) K}
    (hx : x ∈ cyclotomicUnitFreePartModPEvenCharacterEigenspace
      (p := p) K hp_gt_two χ) :
    cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two ψ x = 0 := by
  have hmem :
      cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two ψ x ∈
        cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ ⊓
          cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two ψ :=
    ⟨cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace_of_mem
        (p := p) (K := K) hp_gt_two ψ χ hx,
      cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace
        (p := p) (K := K) hp_gt_two ψ x⟩
  have hbot := cyclotomicUnitFreePartModPEvenCharacterEigenspace_inf_eq_bot_of_ne
    (p := p) (K := K) hp_gt_two hχψ
  have hzero :
      cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two ψ x ∈
        (⊥ : Submodule (ZMod p) (CyclotomicUnitFreePartModP (p := p) K)) := by
    rwa [← hbot]
  simpa using hzero

/-- The `χ`-projector is the identity on the actual `χ`-eigenspace. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_apply_of_mem_eigenspace
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p))
    {x : CyclotomicUnitFreePartModP (p := p) K}
    (hx : x ∈ cyclotomicUnitFreePartModPEvenCharacterEigenspace
      (p := p) K hp_gt_two χ) :
    cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x = x := by
  calc
    cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ x =
        ∑ ψ : MulChar (CyclotomicEvenDelta p) (ZMod p),
          cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two ψ x :=
          (Finset.sum_eq_single χ
            (fun ψ _hψ hψχ =>
              cyclotomicUnitFreePartModPEvenCharacterProjector_apply_eq_zero_of_mem_ne
                (p := p) (K := K) hp_gt_two (Ne.symm hψχ) hx)
            (fun hχ => (hχ (Finset.mem_univ χ)).elim)).symm
    _ = x := cyclotomicUnitFreePartModPEvenCharacterProjector_sum_apply
      (p := p) (K := K) hp_gt_two x

/-- The range of a character idempotent projector is exactly the corresponding
actual even-character eigenspace. -/
theorem cyclotomicUnitFreePartModPEvenCharacterProjector_range_eq_eigenspace
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p)) :
    LinearMap.range
        (cyclotomicUnitFreePartModPEvenCharacterProjector (p := p) K hp_gt_two χ) =
      cyclotomicUnitFreePartModPEvenCharacterEigenspace (p := p) K hp_gt_two χ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact cyclotomicUnitFreePartModPEvenCharacterProjector_mem_eigenspace
      (p := p) (K := K) hp_gt_two χ y
  · intro hx
    exact ⟨x,
      cyclotomicUnitFreePartModPEvenCharacterProjector_apply_of_mem_eigenspace
        (p := p) (K := K) hp_gt_two χ hx⟩





end BernoulliRegular

end
