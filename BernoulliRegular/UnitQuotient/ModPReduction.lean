module

public import BernoulliRegular.UnitQuotient.PermutationCharacters
public import BernoulliRegular.UnitQuotient.TorsionCharacter
public import Mathlib.LinearAlgebra.FreeModule.ModN

/-!
# Unit quotients: reduction of the free quotient modulo `p`

This file proves the formal reduction step used in `REF-07c4`.

There is no natural map in the direction

```text
E/E_tors -> E/E^p,
```

because torsion units can have nontrivial image modulo `p`-th powers.  The
canonical map goes the other way after removing the torsion contribution:

```text
E/E^p -> (E/E_tors) / p.
```

It is obtained by sending a unit to its class in the Dirichlet free quotient
and then reducing that additive quotient modulo `p`.  The map kills `p`-th
powers, contains the torsion image in its kernel, and is equivariant for the
actual cyclotomic `Delta = (ZMod p)^*` action.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The subgroup `p * (E/E_tors)` inside the additive Dirichlet free quotient. -/
abbrev CyclotomicUnitFreePartPMultipleSubmodule :
    Submodule ℤ (CyclotomicUnitFreePart K) :=
  LinearMap.range (LinearMap.lsmul ℤ (CyclotomicUnitFreePart K) p)

/-- The mod-`p` reduction of the additive Dirichlet free quotient. -/
abbrev CyclotomicUnitFreePartModP : Type _ :=
  ModN (CyclotomicUnitFreePart K) p

/-- The quotient map `(E/E_tors) -> (E/E_tors)/p`. -/
abbrev cyclotomicUnitFreePartModPClass :
    CyclotomicUnitFreePart K →+ CyclotomicUnitFreePartModP (p := p) K :=
  ModN.mkQ p

/-- The free quotient map, with the multiplicative unit group written
additively. -/
def cyclotomicUnitFreeClassAdd :
    Additive (CyclotomicUnitGroup K) →+ CyclotomicUnitFreePart K :=
  (cyclotomicUnitFreeClass K).toAdditive


/-- Units mapped to the free quotient and then reduced modulo `p`. -/
def cyclotomicUnitToFreePartModPAdd :
    Additive (CyclotomicUnitGroup K) →+ CyclotomicUnitFreePartModP (p := p) K :=
  (cyclotomicUnitFreePartModPClass (p := p) K).comp
    (cyclotomicUnitFreeClassAdd K)


/-- Multiplicative form of the map from units to the mod-`p` free quotient. -/
def cyclotomicUnitToFreePartModPMul :
    CyclotomicUnitGroup K →*
      Multiplicative (CyclotomicUnitFreePartModP (p := p) K) :=
  AddMonoidHom.toMultiplicativeRight
    (cyclotomicUnitToFreePartModPAdd (p := p) K)


/-- The map to the reduced free quotient kills `p`-th powers. -/
theorem cyclotomicUnitToFreePartModPMul_pow_eq_one
    (u : CyclotomicUnitGroup K) :
    cyclotomicUnitToFreePartModPMul (p := p) K (u ^ p) = 1 := by
  apply Multiplicative.ext
  change cyclotomicUnitFreePartModPClass (p := p) K
      (Additive.ofMul (cyclotomicUnitFreeClass K (u ^ p))) = 0
  rw [map_pow, ofMul_pow]
  change ModN.mkQ p (p • Additive.ofMul (cyclotomicUnitFreeClass K u)) = 0
  change (Submodule.Quotient.mk (p • Additive.ofMul (cyclotomicUnitFreeClass K u)) :
      CyclotomicUnitFreePartModP (p := p) K) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨Additive.ofMul (cyclotomicUnitFreeClass K u), by simp [LinearMap.lsmul_apply]⟩

/-- The canonical map `E/E^p -> (E/E_tors)/p`. -/
def cyclotomicUnitPowerQuotientToFreePartModP :
    CyclotomicUnitPowerQuotient (p := p) (N := 1) K →*
      Multiplicative (CyclotomicUnitFreePartModP (p := p) K) :=
  QuotientGroup.lift
    (CyclotomicUnitPowerSubgroup (p := p) (N := 1) K)
    (cyclotomicUnitToFreePartModPMul (p := p) K)
    (by
      rintro _ ⟨u, rfl⟩
      simpa using cyclotomicUnitToFreePartModPMul_pow_eq_one (p := p) (K := K) u)

@[simp]
theorem cyclotomicUnitPowerQuotientToFreePartModP_apply_class
    (u : CyclotomicUnitGroup K) :
    cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
        (cyclotomicUnitPowerClass (p := p) (N := 1) K u) =
      Multiplicative.ofAdd
        (cyclotomicUnitFreePartModPClass (p := p) K
          (Additive.ofMul (cyclotomicUnitFreeClass K u))) := by
  rfl




/-- The actual cyclotomic action preserves the subgroup of `p`-multiples in
the additive free quotient. -/
theorem cyclotomicUnitFreePartPMultipleSubmodule_map
    (a : CyclotomicUnitDelta p) :
    (CyclotomicUnitFreePartPMultipleSubmodule (p := p) K).map
        (cyclotomicUnitFreePartLinearEquiv (p := p) K a : CyclotomicUnitFreePart K →ₗ[ℤ]
          CyclotomicUnitFreePart K) =
      CyclotomicUnitFreePartPMultipleSubmodule (p := p) K := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := hy
    exact ⟨cyclotomicUnitFreePartLinearEquiv (p := p) K a z, by
      simp [LinearMap.lsmul_apply]⟩
  · rintro x hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨p • (cyclotomicUnitFreePartLinearEquiv (p := p) K a).symm z, ?_, ?_⟩
    · exact ⟨(cyclotomicUnitFreePartLinearEquiv (p := p) K a).symm z, by
        simp [LinearMap.lsmul_apply]⟩
    · simp

/-- The cyclotomic action on the free quotient reduced modulo `p`. -/
def cyclotomicUnitFreePartModPLinearEquiv
    (a : CyclotomicUnitDelta p) :
    CyclotomicUnitFreePartModP (p := p) K ≃ₗ[ℤ]
      CyclotomicUnitFreePartModP (p := p) K :=
  Submodule.Quotient.equiv
    (CyclotomicUnitFreePartPMultipleSubmodule (p := p) K)
    (CyclotomicUnitFreePartPMultipleSubmodule (p := p) K)
    (cyclotomicUnitFreePartLinearEquiv (p := p) K a)
    (cyclotomicUnitFreePartPMultipleSubmodule_map (p := p) (K := K) a)

@[simp]
theorem cyclotomicUnitFreePartModPLinearEquiv_apply_class
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePart K) :
    cyclotomicUnitFreePartModPLinearEquiv (p := p) K a
        (cyclotomicUnitFreePartModPClass (p := p) K x) =
      cyclotomicUnitFreePartModPClass (p := p) K
        (cyclotomicUnitFreePartLinearEquiv (p := p) K a x) :=
  rfl

/-- Multiplicative form of the mod-`p` free quotient action. -/
def cyclotomicUnitFreePartModPMulEquiv
    (a : CyclotomicUnitDelta p) :
    MulAut (Multiplicative (CyclotomicUnitFreePartModP (p := p) K)) :=
  AddEquiv.toMultiplicative
    (cyclotomicUnitFreePartModPLinearEquiv (p := p) K a).toAddEquiv

@[simp]
theorem cyclotomicUnitFreePartModPMulEquiv_apply_class
    (a : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreePartModPMulEquiv (p := p) K a
        (Multiplicative.ofAdd
          (cyclotomicUnitFreePartModPClass (p := p) K
            (Additive.ofMul (cyclotomicUnitFreeClass K u)))) =
      Multiplicative.ofAdd
        (cyclotomicUnitFreePartModPClass (p := p) K
          (Additive.ofMul
            (cyclotomicUnitFreeClass K (cyclotomicUnitEquiv (p := p) K a u)))) :=
  rfl

/-- The canonical map `E/E^p -> (E/E_tors)/p` is equivariant for the actual
cyclotomic action. -/
theorem cyclotomicUnitPowerQuotientToFreePartModP_equivariant
    (a : CyclotomicUnitDelta p)
    (x : CyclotomicUnitPowerQuotient (p := p) (N := 1) K) :
    cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
        ((cyclotomicUnitModPDeltaAction (p := p) K).act a x) =
      cyclotomicUnitFreePartModPMulEquiv (p := p) K a
        (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K x) := by
  refine QuotientGroup.induction_on x ?_
  intro u
  change cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
      ((cyclotomicUnitModPDeltaAction (p := p) K).act a
        (cyclotomicUnitPowerClass (p := p) (N := 1) K u)) =
    cyclotomicUnitFreePartModPMulEquiv (p := p) K a
      (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
        (cyclotomicUnitPowerClass (p := p) (N := 1) K u))
  rw [cyclotomicUnitPowerQuotientDeltaAction_act_mk,
    cyclotomicUnitPowerQuotientToFreePartModP_apply_class,
    cyclotomicUnitPowerQuotientToFreePartModP_apply_class,
    cyclotomicUnitFreePartModPMulEquiv_apply_class]

end BernoulliRegular

end
