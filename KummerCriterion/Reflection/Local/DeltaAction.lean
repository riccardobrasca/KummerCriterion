module

public import KummerCriterion.Reflection.Local.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import KummerCriterion.UnitQuotient.DeltaAction
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Cyclotomic action on lambda-local and completed units

This file starts. It proves that the cyclotomic
`Delta = (ZMod p)^*` automorphisms preserve the distinguished prime
`lambda = (zeta_p - 1)`, hence act on the localization at `lambda` and preserve
the local principal-unit filtration. It also lifts those automorphisms through
the lambda-adic completion.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace KummerCriterion
namespace Reflection
namespace Local

section CompletionLift

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem evalₐ_factor_pow_le {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  simp only [AdicCompletion.evalₐ, AlgHom.coe_comp, Function.comp_apply,
    AlgHom.ofLinearMap_apply]
  have htrans :
      AdicCompletion.transitionMap I R hmn ((AdicCompletion.eval I R n) x) =
        ((AdicCompletion.eval I R m) x) :=
    AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := R) hmn x
  rw [← htrans]
  induction ((AdicCompletion.eval I R n) x) using Quotient.inductionOn' with
  | h r =>
    rfl

theorem ideal_pow_map_ringEquiv_eq_of_map_eq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) (n : ℕ) :
    (I ^ n).map (e : R →+* R) = I ^ n := by
  rw [Ideal.map_pow, he]

theorem ideal_pow_le_comap_ringEquiv_of_map_eq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) (n : ℕ) :
    I ^ n ≤ (I ^ n).comap (e : R →+* R) := by
  rw [← Ideal.map_le_iff_le_comap]
  exact (ideal_pow_map_ringEquiv_eq_of_map_eq (I := I) e he n).le

theorem ideal_map_ringEquiv_symm_eq_of_map_eq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) :
    I.map (e.symm : R →+* R) = I := by
  have h := congrArg (fun J : Ideal R => J.map (e.symm : R →+* R)) he
  simpa using h.symm

noncomputable def adicCompletionRingHomOfIdealMapEqFamily
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) (n : ℕ) :
    AdicCompletion I R →+* R ⧸ I ^ n :=
  (Ideal.quotientMap (I ^ n) (e : R →+* R)
    (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)).comp
    (AdicCompletion.evalₐ I n).toRingHom

theorem adicCompletionRingHomOfIdealMapEqFamily_compatible
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp
        (adicCompletionRingHomOfIdealMapEqFamily (I := I) e he n) =
      adicCompletionRingHomOfIdealMapEqFamily (I := I) e he m := by
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply]
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
        (Ideal.quotientMap (I ^ n) (e : R →+* R)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)
          (AdicCompletion.evalₐ I n x)) =
      Ideal.quotientMap (I ^ m) (e : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he m)
        (AdicCompletion.evalₐ I m x)
  rw [← evalₐ_factor_pow_le (I := I) hmn x]
  induction AdicCompletion.evalₐ I n x using Quotient.inductionOn' with
  | h r =>
    rfl

/-- A ring automorphism preserving `I` lifts to an endomorphism of the
`I`-adic completion. -/
noncomputable def adicCompletionRingHomOfIdealMapEq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) :
    AdicCompletion I R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I
    (adicCompletionRingHomOfIdealMapEqFamily (I := I) e he)
    (fun hmn => adicCompletionRingHomOfIdealMapEqFamily_compatible (I := I) e he hmn)

@[simp]
theorem evalₐ_adicCompletionRingHomOfIdealMapEq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I)
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (adicCompletionRingHomOfIdealMapEq (I := I) e he x) =
      Ideal.quotientMap (I ^ n) (e : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)
        (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom I
    (adicCompletionRingHomOfIdealMapEqFamily (I := I) e he)
    (fun hmn => adicCompletionRingHomOfIdealMapEqFamily_compatible (I := I) e he hmn)
    n x

theorem quotientMap_ringEquiv_symm_apply_quotientMap_ringEquiv
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I)
    (n : ℕ) (x : R ⧸ I ^ n) :
    Ideal.quotientMap (I ^ n) (e.symm : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e.symm
          (ideal_map_ringEquiv_symm_eq_of_map_eq (I := I) e he) n)
        (Ideal.quotientMap (I ^ n) (e : R →+* R)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n) x) =
      x := by
  induction x using Quotient.inductionOn' with
  | h r =>
    change Ideal.Quotient.mk (I ^ n) (e.symm (e r)) =
      Ideal.Quotient.mk (I ^ n) r
    rw [RingEquiv.symm_apply_apply]

theorem quotientMap_ringEquiv_apply_quotientMap_ringEquiv_symm
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I)
    (n : ℕ) (x : R ⧸ I ^ n) :
    Ideal.quotientMap (I ^ n) (e : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)
        (Ideal.quotientMap (I ^ n) (e.symm : R →+* R)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e.symm
            (ideal_map_ringEquiv_symm_eq_of_map_eq (I := I) e he) n) x) =
      x := by
  induction x using Quotient.inductionOn' with
  | h r =>
    change Ideal.Quotient.mk (I ^ n) (e (e.symm r)) =
      Ideal.Quotient.mk (I ^ n) r
    rw [RingEquiv.apply_symm_apply]

/-- A ring automorphism preserving `I` lifts to an automorphism of the
`I`-adic completion. -/
noncomputable def adicCompletionRingEquivOfIdealMapEq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) :
    AdicCompletion I R ≃+* AdicCompletion I R where
  __ := adicCompletionRingHomOfIdealMapEq (I := I) e he
  invFun :=
    adicCompletionRingHomOfIdealMapEq (I := I) e.symm
      (ideal_map_ringEquiv_symm_eq_of_map_eq (I := I) e he)
  left_inv x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n
        (adicCompletionRingHomOfIdealMapEq (I := I) e.symm
          (ideal_map_ringEquiv_symm_eq_of_map_eq (I := I) e he)
          (adicCompletionRingHomOfIdealMapEq (I := I) e he x)) =
      AdicCompletion.evalₐ I n x
    rw [evalₐ_adicCompletionRingHomOfIdealMapEq,
      evalₐ_adicCompletionRingHomOfIdealMapEq,
      quotientMap_ringEquiv_symm_apply_quotientMap_ringEquiv (I := I) e he n]
  right_inv x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n
        (adicCompletionRingHomOfIdealMapEq (I := I) e he
          (adicCompletionRingHomOfIdealMapEq (I := I) e.symm
            (ideal_map_ringEquiv_symm_eq_of_map_eq (I := I) e he) x)) =
      AdicCompletion.evalₐ I n x
    rw [evalₐ_adicCompletionRingHomOfIdealMapEq,
      evalₐ_adicCompletionRingHomOfIdealMapEq,
      quotientMap_ringEquiv_apply_quotientMap_ringEquiv_symm (I := I) e he n]

@[simp]
theorem evalₐ_adicCompletionRingEquivOfIdealMapEq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I)
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (adicCompletionRingEquivOfIdealMapEq (I := I) e he x) =
      Ideal.quotientMap (I ^ n) (e : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)
        (AdicCompletion.evalₐ I n x) :=
  evalₐ_adicCompletionRingHomOfIdealMapEq (I := I) e he n x

end CompletionLift

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The cyclotomic automorphism sends `zeta_p - 1` into the distinguished
prime `(zeta_p - 1)`. -/
theorem cyclotomicRingOfIntegersEquiv_zeta_sub_one_mem_lambda
    (a : CyclotomicUnitDelta p) :
    cyclotomicRingOfIntegersEquiv (p := p) K a
        ((zeta_spec p ℚ K).toInteger - 1) ∈ cyclotomicLambda p K := by
  have hdiv :
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (a : ZMod p).val - 1 := by
    simpa using
      sub_dvd_pow_sub_pow ((zeta_spec p ℚ K).toInteger : 𝓞 K) (1 : 𝓞 K)
        (a : ZMod p).val
  rw [cyclotomicLambda, zetaPrime, Ideal.mem_span_singleton]
  change ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
    cyclotomicRingOfIntegersEquiv (p := p) K a ((zeta_spec p ℚ K).toInteger - 1)
  rw [map_sub, map_one]
  change ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
    cyclotomicSigmaOfUnit (p := p) K a • (zeta_spec p ℚ K).toInteger - 1
  rw [cyclotomicSigmaOfUnit_smul_zetaInteger]
  exact hdiv

theorem cyclotomicRingOfIntegersEquiv_map_lambda_le (a : CyclotomicUnitDelta p) :
    (cyclotomicLambda p K).map
        (cyclotomicRingOfIntegersEquiv (p := p) K a : 𝓞 K →+* 𝓞 K) ≤
      cyclotomicLambda p K := by
  rw [cyclotomicLambda, zetaPrime, Ideal.map_span, Ideal.span_le]
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_singleton_iff] at hy
  subst hy
  exact cyclotomicRingOfIntegersEquiv_zeta_sub_one_mem_lambda (p := p) (K := K) a

theorem cyclotomicRingOfIntegersEquiv_comap_lambda (a : CyclotomicUnitDelta p) :
    cyclotomicLambda p K =
      (cyclotomicLambda p K).comap
        (cyclotomicRingOfIntegersEquiv (p := p) K a : 𝓞 K →+* 𝓞 K) := by
  ext x
  constructor
  · intro hx
    exact cyclotomicRingOfIntegersEquiv_map_lambda_le (p := p) (K := K) a
      (Ideal.mem_map_of_mem _ hx)
  · intro hx
    rw [Ideal.mem_comap] at hx
    have hinv :
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
            (cyclotomicRingOfIntegersEquiv (p := p) K a x) ∈ cyclotomicLambda p K :=
      cyclotomicRingOfIntegersEquiv_map_lambda_le (p := p) (K := K) a⁻¹
        (Ideal.mem_map_of_mem
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ : 𝓞 K →+* 𝓞 K) hx)
    have hcomp :
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
            (cyclotomicRingOfIntegersEquiv (p := p) K a x) = x := by
      rw [← cyclotomicRingOfIntegersEquiv_mul_apply]
      simp
    simpa [hcomp] using hinv

end CyclotomicSetup

end Local
end Reflection
end KummerCriterion

end
