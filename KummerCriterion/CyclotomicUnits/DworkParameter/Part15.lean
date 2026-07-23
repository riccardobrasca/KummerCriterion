module

public import KummerCriterion.CyclotomicUnits.DworkParameter.Part12
public import KummerCriterion.CyclotomicUnits.DworkParameter.Part8Conjugation
import KummerCriterion.CyclotomicUnits.DworkParameter.Part14
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open scoped NumberField Topology WithZero

namespace KummerCriterion
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

open Furtwaengler.KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

namespace Conjugation

theorem continuous_valuedCompletionCyclotomicEquiv
    (a : CyclotomicUnitDelta p) :
    Continuous (valuedCompletionCyclotomicEquiv (p := p) K a) := by
  let v : Valuation K ℤᵐ⁰ := (lambdaHeightOneSpectrum p K).valuation K
  let σ : K ≃+* K := (cyclotomicSigmaOfUnit (p := p) K a).toRingEquiv
  let w : Valuation K ℤᵐ⁰ := v.comap σ.toRingHom
  let h : v.IsEquiv w :=
    lambdaValuation_isEquiv_comap_cyclotomicSigma (p := p) (K := K) a
  change Continuous fun x : ValuedCompletion p K =>
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
      (UniformSpace.Completion.map (WithVal.congr w v σ)
        (UniformSpace.Completion.map (WithVal.congr v w (RingEquiv.refl K))
          x.toCompletion))
  exact
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv K
      (lambdaHeightOneSpectrum p K)).symm.continuous.comp <|
      UniformSpace.Completion.continuous_map.comp <|
        UniformSpace.Completion.continuous_map.comp <|
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv K
            (lambdaHeightOneSpectrum p K)).continuous

theorem valuedCompletionCyclotomicEquiv_rationalToLambdaCompletionRingHom
    (a : CyclotomicUnitDelta p)
    (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) :
    valuedCompletionCyclotomicEquiv (p := p) K a
        (rationalToLambdaCompletionRingHom (p := p) (K := K) x) =
      rationalToLambdaCompletionRingHom (p := p) (K := K) x := by
  have hecont : Continuous (valuedCompletionCyclotomicEquiv (p := p) K a) :=
    continuous_valuedCompletionCyclotomicEquiv (p := p) (K := K) a
  have hfcont : Continuous (rationalToLambdaCompletionRingHom (p := p) (K := K)) := by
    exact
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv K
        (lambdaHeightOneSpectrum p K)).symm.continuous.comp <|
        UniformSpace.Completion.continuous_map.comp <|
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv ℚ
            (lambdaRationalHeightOneSpectrum p)).continuous
  refine DenseRange.induction_on
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap ℚ
      (lambdaRationalHeightOneSpectrum p)) x
    (isClosed_eq (hecont.comp hfcont) hfcont) ?_
  intro y
  let vQ := (lambdaRationalHeightOneSpectrum p).valuation ℚ
  rw [show algebraMap ℚ
        ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) y =
      ((WithVal.toVal vQ y : WithVal vQ) :
        (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) from rfl]
  rw [rationalToLambdaCompletionRingHom_coe]
  change valuedCompletionCyclotomicEquiv (p := p) K a
      (algebraMap K (ValuedCompletion p K) (algebraMap ℚ K y)) =
    algebraMap K (ValuedCompletion p K) (algebraMap ℚ K y)
  rw [valuedCompletionCyclotomicEquiv_algebraMap]
  simp

@[simp]
theorem valuedIntegerComplexConj_rationalPadicIntegerToValuedInteger
    (x : RationalPadicIntegerRing p) :
    valuedIntegerComplexConj (p := p) K
        (rationalPadicIntegerToValuedInteger (p := p) (K := K) x) =
      rationalPadicIntegerToValuedInteger (p := p) (K := K) x := by
  apply Subtype.ext
  change valuedCompletionCyclotomicEquiv (p := p) K (-1)
      (rationalToLambdaCompletionRingHom (p := p) (K := K)
        (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)) =
    rationalToLambdaCompletionRingHom (p := p) (K := K)
      (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
  exact valuedCompletionCyclotomicEquiv_rationalToLambdaCompletionRingHom
    (p := p) (K := K) (-1) x

@[simp]
theorem dworkCompleteComplexConj_algebraMap_rationalPadicInteger
    (x : RationalPadicIntegerRing p) :
    dworkCompleteComplexConj (p := p) K
        (algebraMap (RationalPadicIntegerRing p)
          (DworkCompleteIntegerRing p K) x) =
      algebraMap (RationalPadicIntegerRing p)
        (DworkCompleteIntegerRing p K) x := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalₐ_dworkCompleteComplexConj]
  simp [algebraMap_rationalPadicInteger_dworkComplete_apply]

end Conjugation

/-- The completed fixed subring under complex conjugation. -/
def dworkFixedSubalgebra :
    Subalgebra (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) where
  carrier := {x | Conjugation.dworkCompleteComplexConj (p := p) K x = x}
  algebraMap_mem' x := by
    change Conjugation.dworkCompleteComplexConj (p := p) K
        (algebraMap (RationalPadicIntegerRing p)
          (DworkCompleteIntegerRing p K) x) =
      algebraMap (RationalPadicIntegerRing p)
        (DworkCompleteIntegerRing p K) x
    exact Conjugation.dworkCompleteComplexConj_algebraMap_rationalPadicInteger
      (p := p) (K := K) x
  zero_mem' := by
    simp
  one_mem' := by
    simp
  add_mem' hx hy := by
    change Conjugation.dworkCompleteComplexConj (p := p) K (_ + _) = _ + _
    rw [map_add, hx, hy]
  mul_mem' hx hy := by
    change Conjugation.dworkCompleteComplexConj (p := p) K (_ * _) = _ * _
    rw [map_mul, hx, hy]

def dworkSignedCoefficients
    (a : Fin (p - 1) → RationalPadicIntegerRing p) :
    Fin (p - 1) → RationalPadicIntegerRing p :=
  fun i => (-1 : RationalPadicIntegerRing p) ^ (i : ℕ) * a i

set_option maxHeartbeats 800000 in
-- Needed for normalizing nested rational-integer algebra maps.
theorem dworkCompleteComplexConj_powerLinearMap
    (hp_two : 2 < p)
    (a : Fin (p - 1) → RationalPadicIntegerRing p) :
    Conjugation.dworkCompleteComplexConj (p := p) K
        (dworkParameterPowerLinearMap p K a) =
      dworkParameterPowerLinearMap p K (dworkSignedCoefficients p a) := by
  classical
  rw [dworkParameterPowerLinearMap_apply, dworkParameterPowerLinearMap_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [map_mul, Conjugation.dworkCompleteComplexConj_algebraMap_rationalPadicInteger,
    map_pow, Conjugation.dworkCompleteComplexConj_dworkParameter_eq_neg
      (p := p) (K := K) hp_two]
  dsimp [dworkSignedCoefficients]
  rw [map_mul, map_pow]
  rw [neg_pow]
  rw [map_mul]
  have hsign :
      (-1 : DworkCompleteIntegerRing p K) ^ (i : ℕ) =
        algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
          ((rationalPadicIntegerToValuedInteger (p := p) (K := K)
            (-1 : RationalPadicIntegerRing p)) ^ (i : ℕ)) := by
    rw [← map_pow]
    rw [← algebraMap_rationalPadicInteger_dworkComplete_apply (p := p) (K := K)]
    simp
  rw [hsign]
  ring_nf

theorem rationalPadicInteger_two_ne_zero :
    (2 : RationalPadicIntegerRing p) ≠ 0 := by
  intro h
  have hval :
      ((2 : RationalPadicIntegerRing p) :
        (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) = 0 :=
    congrArg Subtype.val h
  letI : CharZero ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) :=
    algebraRat.charZero ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
  exact (by norm_num :
    (2 : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) ≠ 0) hval

theorem dworkParameterPowerLinearMap_odd_coeff_eq_zero_of_fixed
    (hp_two : 2 < p)
    {a : Fin (p - 1) → RationalPadicIntegerRing p}
    (ha_fixed :
      Conjugation.dworkCompleteComplexConj (p := p) K
          (dworkParameterPowerLinearMap p K a) =
        dworkParameterPowerLinearMap p K a)
    (i : Fin (p - 1)) (hi : Odd (i : ℕ)) :
    a i = 0 := by
  have hmap :
      dworkParameterPowerLinearMap p K (dworkSignedCoefficients p a) =
        dworkParameterPowerLinearMap p K a := by
    rw [← dworkCompleteComplexConj_powerLinearMap (p := p) (K := K) hp_two a,
      ha_fixed]
  have hcoeff :=
    congrFun (dworkParameterPowerLinearMap_injective (p := p) (K := K) hmap) i
  dsimp [dworkSignedCoefficients] at hcoeff
  rw [hi.neg_one_pow] at hcoeff
  have hneg : -(a i) = a i := by
    simpa using hcoeff
  have htwo : (2 : RationalPadicIntegerRing p) * a i = 0 := by
    calc
      (2 : RationalPadicIntegerRing p) * a i = a i + a i := by ring
      _ = a i + -(a i) := by nth_rw 2 [← hneg]
      _ = 0 := add_neg_cancel (a i)
  exact (mul_eq_zero.mp htwo).resolve_left
    (rationalPadicInteger_two_ne_zero (p := p))

set_option synthInstance.maxHeartbeats 80000 in
-- Needed for the fixed-subalgebra inherited additive-monoid instance.
instance instAddCommMonoidDworkFixedSubalgebra :
    AddCommMonoid (dworkFixedSubalgebra p K) :=
  inferInstance

/-- Even exponents among `0,..., p - 2`, used to index the real fixed basis. -/
abbrev dworkEvenPowerIndex : Type :=
  {i : Fin (p - 1) // Even (i : ℕ)}

/-- Extend an even-indexed coefficient family by zero on odd powers. -/
def dworkEvenCoeffExtend :
    (dworkEvenPowerIndex p → RationalPadicIntegerRing p) →ₗ[RationalPadicIntegerRing p]
      (Fin (p - 1) → RationalPadicIntegerRing p) where
  toFun a i := if hi : Even (i : ℕ) then a ⟨i, hi⟩ else 0
  map_add' a b := by
    ext i
    by_cases hi : Even (i : ℕ) <;> simp [hi]
  map_smul' c a := by
    ext i
    by_cases hi : Even (i : ℕ) <;> simp [hi]

@[simp]
theorem dworkSignedCoefficients_evenCoeffExtend
    (a : dworkEvenPowerIndex p → RationalPadicIntegerRing p) :
    dworkSignedCoefficients p (dworkEvenCoeffExtend p a) =
      dworkEvenCoeffExtend p a := by
  ext i
  by_cases hi : Even (i : ℕ)
  · simp [dworkSignedCoefficients, hi.neg_one_pow]
  · simp [dworkSignedCoefficients, dworkEvenCoeffExtend, hi]

set_option synthInstance.maxHeartbeats 80000 in
-- Needed for bundled linear-map instance synthesis over the fixed subalgebra.
/-- The even-power expansion map into the fixed subalgebra. -/
def dworkEvenPowerLinearMap (hp_two : 2 < p) :
    (dworkEvenPowerIndex p → RationalPadicIntegerRing p) →ₗ[RationalPadicIntegerRing p]
      dworkFixedSubalgebra p K where
  toFun a :=
    ⟨dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p a), by
      change Conjugation.dworkCompleteComplexConj (p := p) K
          (dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p a)) =
        dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p a)
      rw [dworkCompleteComplexConj_powerLinearMap (p := p) (K := K) hp_two,
        dworkSignedCoefficients_evenCoeffExtend]⟩
  map_add' a b := by
    apply Subtype.ext
    change dworkParameterPowerLinearMap p K
        (dworkEvenCoeffExtend p (a + b)) =
      dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p a) +
        dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p b)
    rw [map_add, map_add]
  map_smul' c a := by
    apply Subtype.ext
    change dworkParameterPowerLinearMap p K
        (dworkEvenCoeffExtend p (c • a)) =
      c • dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p a)
    rw [map_smul, map_smul]

theorem dworkEvenPowerLinearMap_injective (hp_two : 2 < p) :
    Function.Injective (dworkEvenPowerLinearMap (p := p) (K := K) hp_two) := by
  intro a b hab
  have hfull :
      dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p a) =
        dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p b) :=
    congrArg Subtype.val hab
  have hext :=
    dworkParameterPowerLinearMap_injective (p := p) (K := K) hfull
  apply funext
  intro i
  have hi := congrFun hext i.1
  simpa [dworkEvenCoeffExtend, i.2] using hi

theorem dworkEvenPowerLinearMap_surjective (hp_two : 2 < p) :
    Function.Surjective (dworkEvenPowerLinearMap (p := p) (K := K) hp_two) := by
  intro x
  rcases dworkParameterPowerLinearMap_surjective (p := p) (K := K) x.1 with ⟨a, ha⟩
  have ha_fixed :
      Conjugation.dworkCompleteComplexConj (p := p) K
          (dworkParameterPowerLinearMap p K a) =
        dworkParameterPowerLinearMap p K a := by
    rw [ha]
    exact x.2
  have hodd : ∀ i : Fin (p - 1), Odd (i : ℕ) → a i = 0 :=
    fun i hi => dworkParameterPowerLinearMap_odd_coeff_eq_zero_of_fixed
      (p := p) (K := K) hp_two ha_fixed i hi
  let b : dworkEvenPowerIndex p → RationalPadicIntegerRing p := fun i => a i.1
  refine ⟨b, ?_⟩
  apply Subtype.ext
  change dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p b) = x.1
  rw [← ha]
  congr 1
  ext i
  by_cases hi : Even (i : ℕ)
  · simp [dworkEvenCoeffExtend, b, hi]
  · have hio : Odd (i : ℕ) := Nat.not_even_iff_odd.mp hi
    simp [dworkEvenCoeffExtend, hi, hodd i hio]

theorem dworkEvenPowerLinearMap_bijective (hp_two : 2 < p) :
    Function.Bijective (dworkEvenPowerLinearMap (p := p) (K := K) hp_two) :=
  ⟨dworkEvenPowerLinearMap_injective (p := p) (K := K) hp_two,
    dworkEvenPowerLinearMap_surjective (p := p) (K := K) hp_two⟩

noncomputable def dworkFixedEvenPowerBasis (hp_two : 2 < p) :
    Module.Basis (dworkEvenPowerIndex p) (RationalPadicIntegerRing p)
      (dworkFixedSubalgebra p K) :=
  (Pi.basisFun (RationalPadicIntegerRing p) (dworkEvenPowerIndex p)).map
    (LinearEquiv.ofBijective (dworkEvenPowerLinearMap (p := p) (K := K) hp_two)
      (dworkEvenPowerLinearMap_bijective (p := p) (K := K) hp_two))

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end KummerCriterion

end
