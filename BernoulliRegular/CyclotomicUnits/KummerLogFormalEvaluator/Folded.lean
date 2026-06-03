import BernoulliRegular.CyclotomicUnits.KummerLogFormalEvaluator.Representatives

/-!
# Folded same-prime finite logarithm representatives

This file contains the folded same-prime finite-log representatives and the
normalized quotient bridge.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open BernoulliRegular.Reflection.Local
open scoped BigOperators NumberField PowerSeries

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- The cyclotomic action transports the unscaled normalized Artin-Hasse
finite coordinate to the scaled coordinate in the matching finite quotient. -/
theorem quotient_mk_valuedIntegerCyclotomicEquiv_dworkParameterNormalizedCoordApprox
    (a : CyclotomicUnitDelta p) (N : ℕ) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a
          (dworkParameterNormalizedCoordApprox (p := p) (K := K) N)) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (scaledDworkParameterNormalizedCoordApprox
          (p := p) (K := K) (a : ZMod p) N) := by
  classical
  let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
  let e : ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
    Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a
  have hnormalized :
      Ideal.quotientMap (I ^ (N + 1)) (e : ValuedIntegerRing p K →+* ValuedIntegerRing p K)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e
            (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
              (p := p) (K := K) a) (N + 1))
          (Ideal.Quotient.mk (I ^ (N + 1))
            (dworkParameterNormalizedApprox (p := p) (K := K) N)) =
        Ideal.Quotient.mk (I ^ (N + 1))
          (scaledDworkParameterNormalizedApprox
            (p := p) (K := K) (a : ZMod p) N) := by
    have h :=
      Conjugation.quotientMap_evalIntegralPowerSeriesMod_cyclotomic
        (p := p) (K := K) a
        (integralArtinHasseNormalizedExpMinusOneSeries p K)
        (integralArtinHasseNormalizedExpMinusOneSeries_map_valuedIntegerCyclotomicEquiv
          (p := p) (K := K) a)
        (dworkParameter p K) (N + 1)
    rw [Conjugation.dworkCompleteCyclotomicEquiv_dworkParameter] at h
    rw [← quotient_mk_dworkParameterNormalizedApprox_eq_evalIntegralPowerSeriesMod
        (p := p) (K := K) N,
      ← quotient_mk_scaledDworkParameterNormalizedApprox_eq_evalIntegralPowerSeriesMod
        (p := p) (K := K) (a : ZMod p) N] at h
    simpa [I, e] using h
  have hcoord := congrArg (fun z =>
      z - (1 : ValuedIntegerRing p K ⧸ I ^ (N + 1))) hnormalized
  simpa [I, e, dworkParameterNormalizedCoordApprox,
    scaledDworkParameterNormalizedCoordApprox, map_sub] using hcoord

omit [NumberField.IsCMField K] in
/-- The unscaled normalized Artin-Hasse finite logarithm at the Dwork
parameter approximant, at the Kummer precision. -/
noncomputable def dworkParameterNormalizedFiniteLogApprox :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1) :=
  Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
      p - 1 ≤ (p - 2) + 1)
    (samePrimeFiniteLog (p := p) (K := K) (p - 2)
      (dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2))
      (dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
        (p := p) (K := K) (p - 2)))

omit [NumberField.IsCMField K] in
/-- The scaled normalized Artin-Hasse finite logarithm at the Dwork parameter
approximant, at the Kummer precision. -/
noncomputable def scaledDworkParameterNormalizedFiniteLogApprox
    (a : ZMod p) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1) :=
  Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
      p - 1 ≤ (p - 2) + 1)
    (samePrimeFiniteLog (p := p) (K := K) (p - 2)
      (scaledDworkParameterNormalizedCoordApprox
        (p := p) (K := K) a (p - 2))
      (scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
        (p := p) (K := K) a (p - 2)))

omit [NumberField.IsCMField K] in
/-- The scaled normalized Artin-Hasse finite logarithm is the cyclotomic image
of the unscaled normalized finite logarithm at the Kummer precision. -/
theorem samePrimeFiniteLog_scaledNormalizedCoordApprox_eq_quotientMap
    (a : CyclotomicUnitDelta p) :
    samePrimeFiniteLog (p := p) (K := K) (p - 2)
        (scaledDworkParameterNormalizedCoordApprox
          (p := p) (K := K) (a : ZMod p) (p - 2))
        (scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
          (p := p) (K := K) (a : ZMod p) (p - 2)) =
      Ideal.quotientMap ((lambdaIdeal p K) ^ ((p - 2) + 1))
        (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a)
          (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
            (p := p) (K := K) a) ((p - 2) + 1))
        (samePrimeFiniteLog (p := p) (K := K) (p - 2)
          (dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2))
          (dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
            (p := p) (K := K) (p - 2))) := by
  classical
  let e : ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
    Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a
  let x : ValuedIntegerRing p K :=
    dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2)
  let y : ValuedIntegerRing p K :=
    scaledDworkParameterNormalizedCoordApprox
      (p := p) (K := K) (a : ZMod p) (p - 2)
  have hx : x ∈ lambdaIdeal p K := by
    simpa [x] using
      dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
        (p := p) (K := K) (p - 2)
  have hy : y ∈ lambdaIdeal p K := by
    simpa [y] using
      scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
        (p := p) (K := K) (a : ZMod p) (p - 2)
  have hex : e x ∈ lambdaIdeal p K := by
    simpa [e, x] using
      Conjugation.valuedIntegerCyclotomicEquiv_mem_lambdaIdeal
        (p := p) (K := K) a hx
  have hsub : e x - y ∈ (lambdaIdeal p K) ^ ((p - 2) + 1) := by
    have hq :=
      quotient_mk_valuedIntegerCyclotomicEquiv_dworkParameterNormalizedCoordApprox
        (p := p) (K := K) a (p - 2)
    simpa [e, x, y] using Ideal.Quotient.eq.mp hq
  have hlog :
      samePrimeFiniteLog (p := p) (K := K) (p - 2) (e x) hex =
        samePrimeFiniteLog (p := p) (K := K) (p - 2) y hy :=
    samePrimeFiniteLog_eq_of_sub_mem (p := p) (K := K) hex hy hsub
  have hmap :=
    Conjugation.samePrimeFiniteLog_quotientMap_cyclotomic
      (p := p) (K := K) (N := p - 2) a hx
  simpa [e, x, y] using hlog.symm.trans hmap.symm

omit [NumberField.IsCMField K] in
/-- Factoring a cyclotomic quotient map to lower lambda-adic precision commutes
with first factoring the source quotient. -/
theorem quotientMap_valuedIntegerCyclotomicEquiv_factorPow
    {M N : ℕ} (hMN : M ≤ N) (a : CyclotomicUnitDelta p)
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
        (Ideal.quotientMap ((lambdaIdeal p K) ^ N)
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a :
            ValuedIntegerRing p K →+* ValuedIntegerRing p K)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
            (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a)
            (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
              (p := p) (K := K) a) N)
          x) =
      Ideal.quotientMap ((lambdaIdeal p K) ^ M)
        (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a)
          (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
            (p := p) (K := K) a) M)
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hMN x) := by
  refine Quotient.inductionOn' x ?_
  intro x
  rfl

set_option maxHeartbeats 2000000 in
-- The statement contains the p-level lambda quotient and two finite-log
-- approximants; elaborating the quotient type needs a local heartbeat bump.
omit [NumberField.IsCMField K] in
/-- Coordinate form of
`samePrimeFiniteLog_scaledNormalizedCoordApprox_eq_quotientMap`. -/
theorem valuedLambdaQuotientDworkCoeffModP_scaledNormalizedFiniteLog_eq_smul
    (a : CyclotomicUnitDelta p) (i : Fin (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (scaledDworkParameterNormalizedFiniteLogApprox
          (p := p) (K := K) (a : ZMod p)) =
      (a : ZMod p) ^ (i : ℕ) *
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) := by
  unfold scaledDworkParameterNormalizedFiniteLogApprox
  rw [samePrimeFiniteLog_scaledNormalizedCoordApprox_eq_quotientMap
    (p := p) (K := K) a]
  rw [quotientMap_valuedIntegerCyclotomicEquiv_factorPow
    (p := p) (K := K) (M := p - 1) (N := (p - 2) + 1)
    (by omega) a]
  have hcoord :=
    valuedLambdaQuotientDworkCoeffModP_quotientMap_cyclotomic
      (p := p) (K := K) a i
      (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K))
  simpa [dworkParameterNormalizedFiniteLogApprox,
    scaledDworkParameterNormalizedFiniteLogApprox] using hcoord

omit [NumberField.IsCMField K] in
/-- CU-11f2b2c reduced to the unscaled normalized Artin-Hasse finite-log
coordinate.  The scaled denominator contributes by the cyclotomic action,
hence the factor `1 - c^i`. -/
theorem valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_one_sub_pow_mul_unscaled
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (i : Fin (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
            p - 1 ≤ (p - 2) + 1)
          (kummerLogDworkArtinHasseSpecializedFiniteLog
            (p := p) (K := K) hp_three a)) =
      (1 - (kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^ (i : ℕ)) *
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) := by
  let δ : CyclotomicUnitDelta p := kummerLogColumnDelta (p := p) hp_three a
  rw [kummerLogDworkArtinHasseSpecializedFiniteLog_factorPow_eq_normalizedApprox_logs
    (p := p) (K := K) hp_three a]
  rw [valuedLambdaQuotientDworkCoeffModP_sub]
  change
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) -
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (scaledDworkParameterNormalizedFiniteLogApprox
          (p := p) (K := K)
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)) =
    (1 - (kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^ (i : ℕ)) *
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K))
  rw [show (kummerLogColumnIndex (p := p) hp_three a : ZMod p) =
      (δ : ZMod p) by rfl]
  rw [valuedLambdaQuotientDworkCoeffModP_scaledNormalizedFiniteLog_eq_smul
    (p := p) (K := K) δ i]
  ring

end CyclotomicUnits
end BernoulliRegular

end
