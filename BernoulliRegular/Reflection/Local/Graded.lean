module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import BernoulliRegular.Reflection.Local.Endpoint

/-!
# First graded piece of the principal-unit filtration

This file begins the REF-10d2 first graded-piece layer.  It constructs the
standard homomorphism from multiplicative principal units to the additive
cotangent space `I / I^2`, sending `u` to `u - 1`, and identifies its kernel.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Ideal

section OneUnitsCotangent

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The first graded map on congruence-one units, `u ↦ u - 1 mod I^2`. -/
noncomputable def oneUnitsCotangentHom :
    oneUnitsSubgroup I →* Multiplicative I.Cotangent where
  toFun u := Multiplicative.ofAdd (I.toCotangent ⟨(u : Rˣ) - 1, u.2⟩)
  map_one' := by
    rw [← ofAdd_zero]
    apply congrArg Multiplicative.ofAdd
    rw [I.toCotangent_eq_zero]
    simp
  map_mul' u v := by
    rw [← ofAdd_add]
    apply congrArg Multiplicative.ofAdd
    rw [← map_add]
    rw [I.toCotangent_eq]
    change (((((u : oneUnitsSubgroup I) : Rˣ) * ((v : oneUnitsSubgroup I) : Rˣ) : Rˣ) :
        R) - 1 - (((u : Rˣ) : R) - 1 + (((v : Rˣ) : R) - 1)) ∈ I ^ 2)
    have hprod : (((u : Rˣ) : R) - 1) * (((v : Rˣ) : R) - 1) ∈ I ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul u.2 v.2
    convert hprod using 1
    simp [Units.val_mul]
    ring


theorem mem_oneUnitsCotangentHom_ker {u : oneUnitsSubgroup I} :
    u ∈ (oneUnitsCotangentHom I).ker ↔ ((u : Rˣ) : R) - 1 ∈ I ^ 2 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have hzero : I.toCotangent ⟨((u : Rˣ) : R) - 1, u.2⟩ = 0 :=
      Multiplicative.ofAdd.injective (by simpa [oneUnitsCotangentHom] using h)
    exact (I.toCotangent_eq_zero _).mp hzero
  · intro h
    have hzero : I.toCotangent ⟨((u : Rˣ) : R) - 1, u.2⟩ = 0 :=
      (I.toCotangent_eq_zero _).mpr h
    simp [oneUnitsCotangentHom, hzero]


end OneUnitsCotangent

end Ideal

namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The localized uniformizer `zeta_p - 1` at `lambda`. -/
noncomputable def localCyclotomicUniformizer : localCyclotomicRing p K :=
  algebraMap (𝓞 K) (localCyclotomicRing p K)
    ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1)

theorem localCyclotomicMaximalIdeal_eq_span_uniformizer :
    localCyclotomicMaximalIdeal p K = Ideal.span {localCyclotomicUniformizer p K} := by
  rw [← localCyclotomicMaximalIdeal_eq_map p K]
  simp [localCyclotomicUniformizer, cyclotomicLambda, zetaPrime, Ideal.map_span]

theorem localCyclotomicMaximalIdeal_isPrincipal :
    Submodule.IsPrincipal (localCyclotomicMaximalIdeal p K) := by
  rw [localCyclotomicMaximalIdeal_eq_span_uniformizer]
  rw [Submodule.isPrincipal_iff]
  exact ⟨localCyclotomicUniformizer p K, rfl⟩

theorem localCyclotomicMaximalIdeal_ne_bot :
    localCyclotomicMaximalIdeal p K ≠ ⊥ := by
  intro h
  have hcomap := congrArg (Ideal.comap (algebraMap (𝓞 K) (localCyclotomicRing p K))) h
  rw [localCyclotomicMaximalIdeal_comap] at hcomap
  have hbot : cyclotomicLambda p K = ⊥ := by
    simpa using hcomap
  exact zetaPrime_ne_bot p K (by simpa [cyclotomicLambda] using hbot)

/-- The global cyclotomic prime `lambda` is maximal. -/
theorem cyclotomicLambda_isMaximal :
    (cyclotomicLambda p K).IsMaximal := by
  simpa [cyclotomicLambda] using
    (Ideal.IsPrime.isMaximal (zetaPrime_isPrime p K) (zetaPrime_ne_bot p K))

/-- The global residue ring at `lambda` has cardinality `p`. -/
theorem globalCyclotomicResidueCard :
    Nat.card (𝓞 K ⧸ cyclotomicLambda p K) = p := by
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    simp
  have hAbs : Ideal.absNorm (cyclotomicLambda p K) = p := by
    simpa [cyclotomicLambda, zetaPrime] using
      (IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one p 0 hζ)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hAbs
  exact hAbs

/-- The local residue ring at `lambda` has cardinality `p`. -/
theorem localCyclotomicResidueCard :
    Nat.card (localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K) = p := by
  letI : (cyclotomicLambda p K).IsMaximal := cyclotomicLambda_isMaximal (p := p) (K := K)
  have hlocal_global :
      Nat.card (localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K) =
        Nat.card (𝓞 K ⧸ cyclotomicLambda p K) := by
    have hbij := Ideal.bijective_algebraMap_quotient_residueField (cyclotomicLambda p K)
    exact (Nat.card_congr (Equiv.ofBijective
      (algebraMap (𝓞 K ⧸ cyclotomicLambda p K)
        ((cyclotomicLambda p K).ResidueField)) hbij)).symm
  exact hlocal_global.trans (globalCyclotomicResidueCard (p := p) (K := K))

end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular
