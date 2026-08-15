module

public import KummerCriterion.CyclotomicUnits.KummerLogNormalization.Part2
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
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

open NumberField
open NumberField.IsCMField
open IsCyclotomicExtension
open KummerCriterion.Reflection.Local
open scoped BigOperators NumberField

namespace KummerCriterion
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- The quotient-sum comparison expands mapped polynomial powers and the
-- factorial-weighted formal source at the same time.
omit [NumberField.IsCMField K] in
theorem quotient_mk_samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeQuotientMap (p := p) (K := K) N
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x) =
      samePrimeQuotientMap (p := p) (K := K) N (x ^ d) *
        (samePrimeRIntegralRatToQuotient (p := p) (K := K) N
          (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n)) := by
  classical
  let q : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    samePrimeQuotientMap (p := p) (K := K) N
  let φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    samePrimeRIntegralRatToQuotient (p := p) (K := K) N
  let xbar_d : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    q (x ^ d)
  have hterm : ∀ n ∈ Finset.Icc 1 d,
      q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) =
        xbar_d *
          φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) := by
    intro n _hn
    have hqcoeff :
        q (((samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x) ^ n).coeff d) =
          (PowerSeries.coeff
            (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
            ((samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
              (p := p) (K := K) N x) ^ n) := by
      change Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d) =
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
            (p := p) (K := K) N x) ^ n)
      exact quotient_mk_samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq
        (p := p) (K := K) N n d hx
    calc
      q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x)
          =
        ((d.factorial / n : ℕ) :
            ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
          ((-1 :
            ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
            (PowerSeries.coeff
              (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
              ((samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
                (p := p) (K := K) N x) ^ n) := by
          simp only [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator,
            map_mul, map_natCast, map_pow]
          rw [hqcoeff]
          simp only [map_neg, map_one]
          ring_nf
      _ =
        xbar_d *
          φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) := by
          have hformal :
              φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) =
                ((d.factorial / n : ℕ) :
                    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
                  ((-1 :
                    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
                    (PowerSeries.coeff
                      (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
                      ((PowerSeries.map q
                        (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)) ^ n) :=
            samePrime_rIntegralRatToQuotient_normalizedFactorialWeightedLogCoeff
              (p := p) (K := K) N d n
          rw [coeff_samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries_pow
            (p := p) (K := K) N n d x]
          let a : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
            ((d.factorial / n : ℕ) :
              ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1))
          let b : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
            ((-1 :
              ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1))
          let c : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
            (PowerSeries.coeff
              (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
              ((PowerSeries.map q
                (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)) ^ n)
          let z : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := q (x ^ d)
          have hformal' :
              φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) =
                a * b * c :=
            hformal
          change a * b * (z * c) =
            xbar_d *
              φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n)
          rw [hformal']
          ring
  calc
    q (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x)
        =
      ∑ n ∈ Finset.Icc 1 d,
        q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) := by
        rw [map_sum]
    _ =
      ∑ n ∈ Finset.Icc 1 d,
        xbar_d *
          φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        exact hterm n hn
    _ =
      xbar_d *
        ∑ n ∈ Finset.Icc 1 d,
          φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) :=
        (Finset.mul_sum (s := Finset.Icc 1 d)
          (f := fun n => φ
            (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n))
          xbar_d).symm
    _ =
      q (x ^ d) *
        φ (∑ n ∈ Finset.Icc 1 d,
          rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) := by
        have hmapsum :
            (∑ n ∈ Finset.Icc 1 d,
              φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n)) =
              φ (∑ n ∈ Finset.Icc 1 d,
                rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) :=
          (map_sum φ
            (fun n => rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n)
            (Finset.Icc 1 d)).symm
        rw [hmapsum]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (n d : ℕ) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x) ^ n).coeff d ∈
      (lambdaIdeal p K) ^ d := by
  induction n generalizing d with
  | zero =>
      by_cases hd : d = 0
      · subst d
        simp
      · simp [Polynomial.coeff_one, hd]
  | succ n ih =>
      rw [pow_succ, Polynomial.coeff_mul]
      refine Ideal.sum_mem _ ?_
      intro a ha
      have hsum : a.1 + a.2 = d := by
        simpa using (Finset.mem_antidiagonal.mp ha)
      have hleft :
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x) ^ n).coeff a.1 ∈
            (lambdaIdeal p K) ^ a.1 :=
        ih a.1
      have hright :
          (samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x).coeff a.2 ∈
            (lambdaIdeal p K) ^ a.2 :=
        samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_mem_lambdaIdeal_pow
          (p := p) (K := K) N hx a.2
      have hmul :
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly
                (p := p) (K := K) N x) ^ n).coeff a.1 *
              (samePrimeFiniteArtinHasseNormalizedCoordPoly
                (p := p) (K := K) N x).coeff a.2 ∈
            (lambdaIdeal p K) ^ (a.1 + a.2) := by
        simpa [pow_add] using Ideal.mul_mem_mul hleft hright
      simpa [hsum] using hmul

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
        (p := p) (K := K) N n d x ∈
      (lambdaIdeal p K) ^ d :=
  Ideal.mul_mem_left _ _
    (samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) N hx n d)

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_zero_of_lt
    (N : ℕ) (x : ValuedIntegerRing p K) {n d : ℕ} (hdn : d < n) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x) ^ n).coeff d = 0 := by
  have h :=
    coeff_pow_coe_eq_zero_of_lt_of_constantCoeff_eq_zero
      (samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x)
      (samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_zero
        (p := p) (K := K) N x) hdn
  simpa [← Polynomial.coe_pow, Polynomial.coeff_coe] using h

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_le_of_mem_support
    (N : ℕ) (x : ValuedIntegerRing p K) {n d : ℕ}
    (hd : d ∈ ((samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x) ^ n).support) :
    n ≤ d := by
  by_contra hnd
  have hdn : d < n := Nat.lt_of_not_ge hnd
  have hcoeff :
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) N x) ^ n).coeff d = 0 :=
    samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_zero_of_lt
      (p := p) (K := K) N x hdn
  exact (Polynomial.mem_support_iff.mp hd) hcoeff

omit [NumberField.IsCMField K] in
/-- Unsigned homogeneous finite-log term attached to the degree-`d`
coefficient of the `n`-th power of the normalized Artin-Hasse coordinate. -/
noncomputable def samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore
    (N n d : ℕ) (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  if hn : n = 0 then 0 else
    if hnd : n ≤ d then
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
        (((samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) N x) ^ n).coeff d)
        (samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
          (p := p) (K := K) N hx n d)
        (samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd)
    else 0

omit [NumberField.IsCMField K] in
/-- Signed homogeneous finite-log term attached to the degree-`d`
coefficient of the `n`-th power of the normalized Artin-Hasse coordinate. -/
noncomputable def samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
    (N n d : ℕ) (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore
      (p := p) (K := K) N n d x hx

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_signed_eval
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hn : n ≠ 0) (hnd : n ≤ d) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
        (p := p) (K := K) N n d x hx =
      ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
          (((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d)
          (samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
            (p := p) (K := K) N hx n d)
          (samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd) := by
  simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore, hn, hnd]

omit [NumberField.IsCMField K] in
noncomputable def samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
    (N d : ℕ) (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ∑ a ∈ (Finset.Icc 1 d).attach,
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
      (p := p) (K := K) N a.1 d x hx

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_eval_sum
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N a.1 d x)
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
            have hden : a.1.factorization p * (p - 1) ≤ d :=
              samePrimeFiniteArtinHasse_den_exponent_le (p := p)
                (Nat.ne_zero_of_lt ha1) had
            simpa [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator] using
              Ideal.pow_le_pow_right hden
                (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
                  (p := p) (K := K) N a.1 d hx)) := by
  classical
  unfold samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
  refine Finset.sum_congr rfl ?_
  intro a _ha
  have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
  have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
  have han : a.1 ≠ 0 := Nat.ne_zero_of_lt ha1
  have hden : a.1.factorization p * (p - 1) ≤ d :=
    samePrimeFiniteArtinHasse_den_exponent_le (p := p) han had
  have hcoeff :
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) N x) ^ a.1).coeff d ∈
        (lambdaIdeal p K) ^ d :=
    samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) N hx a.1 d
  have hsign :
      (((-1 : ValuedIntegerRing p K) ^ (a.1 + 1)) *
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ a.1).coeff d) ∈
        (lambdaIdeal p K) ^ d :=
    Ideal.mul_mem_left _ _ hcoeff
  have hnum0 :
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
          (p := p) (K := K) N a.1 d x ∈
        (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0) := by
    simpa [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator] using
      Ideal.pow_le_pow_right hden hsign
  have hmk :
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          ((-1 : ValuedIntegerRing p K) ^ (a.1 + 1)) =
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^
          (a.1 + 1)) := by
    simp
  rw [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_signed_eval
    (p := p) (K := K) N a.1 d hx han had]
  rw [← hmk]
  rw [← samePrimeNatDivEvalAtDegree_mul_left (p := p) (K := K) han
    ((-1 : ValuedIntegerRing p K) ^ (a.1 + 1)) hcoeff hsign hden]
  rw [samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval (p := p) (K := K)
    han hsign hden hnum0]
  exact samePrimeNatDivEval_eq_of_eq (p := p) (K := K) han
    (by simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator])
    hnum0 _

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- The proof expands quotient sums and same-prime denominator transport termwise.
omit [NumberField.IsCMField K] in
/-- Multiplying a normalized homogeneous finite-log degree slice by `d!`
clears the same-prime denominators and gives the factorial-weighted numerator
sum in the finite quotient. -/
theorem natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    ((d.factorial : ℕ) :
        ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx =
    samePrimeQuotientMap (p := p) (K := K) N
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) := by
  classical
  let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)
  let q : ValuedIntegerRing p K →+* A :=
    samePrimeQuotientMap (p := p) (K := K) N
  let z : ℕ → ValuedIntegerRing p K := fun n =>
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
      (p := p) (K := K) N n d x
  have hz0 : ∀ n ∈ Finset.Icc 1 d,
      z n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + 0) := by
    intro n hnI
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hnI).2
    have hden : n.factorization p * (p - 1) ≤ d :=
      samePrimeFiniteArtinHasse_den_exponent_le (p := p)
        (Nat.ne_zero_of_lt hn1) hnd
    simpa [z] using
      Ideal.pow_le_pow_right hden
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) N n d hx)
  have hdegree :
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := p) (K := K) N d x hx =
        ∑ a ∈ (Finset.Icc 1 d).attach,
          samePrimeNatDivEval (p := p) (K := K) N a.1 0
            (by
              have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
              exact Nat.ne_zero_of_lt ha1)
            (z a.1) (hz0 a.1 a.2) := by
    simpa [z] using
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_eval_sum
        (p := p) (K := K) N d hx
  rw [hdegree, Finset.mul_sum]
  calc
    ∑ a ∈ (Finset.Icc 1 d).attach,
        ((d.factorial : ℕ) : A) *
          samePrimeNatDivEval (p := p) (K := K) N a.1 0
            (by
              have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
              exact Nat.ne_zero_of_lt ha1)
            (z a.1) (hz0 a.1 a.2)
        =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        q (((d.factorial / a.1 : ℕ) : ValuedIntegerRing p K) * z a.1) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
        have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
        have han : a.1 ≠ 0 := Nat.ne_zero_of_lt ha1
        have hdiv : a.1 ∣ d.factorial :=
          Nat.dvd_factorial (Nat.pos_of_ne_zero han) had
        have hfac : (d.factorial / a.1) * a.1 = d.factorial :=
          Nat.div_mul_cancel hdiv
        have hnat :
            ((d.factorial : ℕ) : A) =
              ((d.factorial / a.1 : ℕ) : A) * ((a.1 : ℕ) : A) := by
          rw [← Nat.cast_mul, hfac]
        have hnatdiv :
            ((a.1 : ℕ) : A) *
                samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
                  (z a.1) (hz0 a.1 a.2) =
              q (z a.1) := by
          simpa [q, A, samePrimeQuotientMap] using
            samePrimeNatDivEval_natCast_mul_eq_mk
              (p := p) (K := K) (N := N) (n := a.1) (s := 0) han
              (z := z a.1) (hz0 a.1 a.2)
        calc
          ((d.factorial : ℕ) : A) *
              samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
                (z a.1) (hz0 a.1 a.2)
              =
            ((d.factorial / a.1 : ℕ) : A) *
              (((a.1 : ℕ) : A) *
                samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
                  (z a.1) (hz0 a.1 a.2)) := by
              rw [hnat]
              ring
          _ =
            ((d.factorial / a.1 : ℕ) : A) * q (z a.1) := by
              rw [hnatdiv]
          _ =
            q (((d.factorial / a.1 : ℕ) : ValuedIntegerRing p K) * z a.1) := by
              change q (((d.factorial / a.1 : ℕ) : ValuedIntegerRing p K)) *
                  q (z a.1) =
                q (((d.factorial / a.1 : ℕ) : ValuedIntegerRing p K) * z a.1)
              rw [map_mul]
    _ =
      samePrimeQuotientMap (p := p) (K := K) N
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z n) := by
        rw [map_sum]
        simpa [q] using
          (Finset.sum_attach (s := Finset.Icc 1 d)
            (f := fun n : ℕ =>
              q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z n)))

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- This is the exact source bridge used by the coefficient-level evaluator:
-- it combines denominator clearing with the formal normalized log coefficient.
omit [NumberField.IsCMField K] in
/-- Factorial-cleared normalized homogeneous degree slice, expressed through
the formal normalized Artin-Hasse logarithm coefficient. -/
theorem natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_formal
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    ((d.factorial : ℕ) :
        ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx =
    samePrimeQuotientMap (p := p) (K := K) N (x ^ d) *
      samePrimeRIntegralRatToQuotient (p := p) (K := K) N
        (∑ n ∈ Finset.Icc 1 d,
          rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) := by
  rw [natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq
    (p := p) (K := K) N d hx]
  exact quotient_mk_samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
    (p := p) (K := K) N d hx

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- This repeats the Part5 factorial-cleared comparison with the normalized
-- formal source. The formal hypothesis is a concrete coefficient equality,
-- not a bundled finite-log assumption.
omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_zero_of_not_mem_support
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hd : d ∉ ((samePrimeFiniteArtinHasseNormalizedCoordPoly
      (p := p) (K := K) N x) ^ n).support) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
      (p := p) (K := K) N n d x hx = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore]
  by_cases hnd : n ≤ d
  · have hcoeff_zero :
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d = 0 := by
      simpa [Polynomial.mem_support_iff] using hd
    have hcoeff :
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d ∈
          (lambdaIdeal p K) ^ d :=
      samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) N hx n d
    have hden : n.factorization p * (p - 1) ≤ d :=
      samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd
    have heval_zero :
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
            (((samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x) ^ n).coeff d)
            hcoeff hden = 0 := by
      rw [samePrimeNatDivEvalAtDegree]
      let s : ℕ := d - n.factorization p * (p - 1)
      have hcoeff_s :
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x) ^ n).coeff d ∈
            (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
        simpa [s, Nat.add_sub_of_le hden] using hcoeff
      have hzero_s :
          (0 : ValuedIntegerRing p K) ∈
            (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) :=
        zero_mem _
      change samePrimeNatDivEval (p := p) (K := K) N n s hn
          (((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d)
          hcoeff_s = 0
      calc
        samePrimeNatDivEval (p := p) (K := K) N n s hn
            (((samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x) ^ n).coeff d)
            hcoeff_s
            = samePrimeNatDivEval (p := p) (K := K) N n s hn 0 hzero_s :=
                samePrimeNatDivEval_eq_of_eq (p := p) (K := K) hn
                  hcoeff_zero hcoeff_s hzero_s
        _ = 0 := samePrimeNatDivEval_zero (p := p) (K := K) hn hzero_s
    rw [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_signed_eval
      (p := p) (K := K) N n d hx hn hnd]
    rw [heval_zero]
    simp
  · simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore, hn, hnd]

end CyclotomicUnits

end KummerCriterion

end
