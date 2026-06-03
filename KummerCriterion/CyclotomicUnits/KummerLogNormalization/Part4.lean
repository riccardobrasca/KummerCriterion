module

public import KummerCriterion.CyclotomicUnits.KummerLogNormalization.Part3
import KummerCriterion.CyclotomicUnits.DworkParameter.Part17
import KummerCriterion.Reflection.ResidueSymbol.DworkFactorization.FiniteLogBounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_zero_of_cutoff_le_degree
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hcut : samePrimeFiniteLogCutoff (p := p) N ≤ d) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
      (p := p) (K := K) N n d x hx = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore]
  by_cases hnd : n ≤ d
  · have hcoeff :
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d ∈
          (lambdaIdeal p K) ^ d :=
      samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) N hx n d
    have hden : n.factorization p * (p - 1) ≤ d :=
      samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd
    rw [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_signed_eval
      (p := p) (K := K) N n d hx hn hnd]
    rw [samePrimeNatDivEvalAtDegree_eq_zero_of_cutoff_le
      (p := p) (K := K) (N := N) (n := n) (d := d) hn hnd hcut hcoeff hden]
    simp
  · simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore, hn, hnd]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_sum_Icc
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx =
      ∑ n ∈ Finset.Icc 1 d,
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
          (p := p) (K := K) N n d x hx := by
  classical
  simpa [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum] using
    (Finset.sum_attach (s := Finset.Icc 1 d)
      (f := fun n : ℕ =>
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
          (p := p) (K := K) N n d x hx))

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLogTermCore_normalizedArtinHasseCoord_eq_homogeneous_support_sum
    (N n : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) (hn : n ≠ 0) :
    samePrimeFiniteLogTermCore (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
          (p := p) (K := K) N hx) =
      ∑ d ∈ ((samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) N x) ^ n).support,
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore
          (p := p) (K := K) N n d x hx := by
  classical
  let P : Polynomial (ValuedIntegerRing p K) :=
    samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x
  let z : ValuedIntegerRing p K :=
    samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x
  let s : ℕ := samePrimeFiniteLogTermOrder (p := p) n
  have hz : z ∈ lambdaIdeal p K := by
    simpa [z] using samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
      (p := p) (K := K) N hx
  have hpow_order : z ^ n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    simpa [z, s, factorization_mul_pred_add_samePrimeFiniteLogTermOrder
        (p := p) hn] using
      Ideal.pow_mem_pow hz n
  have hcoeff_order_of_mem :
      ∀ d ∈ (P ^ n).support,
        (P ^ n).coeff d ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    intro d hd
    have hnd : n ≤ d := by
      simpa [P] using
        samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_le_of_mem_support
          (p := p) (K := K) N x hd
    have hcoeff : (P ^ n).coeff d ∈ (lambdaIdeal p K) ^ d := by
      simpa [P] using
        samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
          (p := p) (K := K) N hx n d
    have hle : (lambdaIdeal p K) ^ d ≤
        (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
      rw [factorization_mul_pred_add_samePrimeFiniteLogTermOrder (p := p) hn]
      exact Ideal.pow_le_pow_right hnd
    exact hle hcoeff
  have hcoeff_order :
      ∀ d, (P ^ n).coeff d ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    intro d
    by_cases hd : d ∈ (P ^ n).support
    · exact hcoeff_order_of_mem d hd
    · have hzero : (P ^ n).coeff d = 0 := by
        simpa [Polynomial.mem_support_iff] using hd
      rw [hzero]
      exact zero_mem _
  have heval :
      (P ^ n).eval 1 = ∑ d ∈ (P ^ n).support, (P ^ n).coeff d := by
    rw [Polynomial.eval_eq_sum]
    simp [Polynomial.sum]
  have hsum_eq : z ^ n = ∑ d ∈ (P ^ n).support, (P ^ n).coeff d := by
    calc
      z ^ n =
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x).eval 1) ^ n := by
        rw [samePrimeFiniteArtinHasseNormalizedCoordPoly_eval_one]
      _ = (P ^ n).eval 1 := by
        simp [P, Polynomial.eval_pow]
      _ = ∑ d ∈ (P ^ n).support, (P ^ n).coeff d := heval
  have hsum_order :
      (∑ d ∈ (P ^ n).support, (P ^ n).coeff d) ∈
        (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    rw [← hsum_eq]
    exact hpow_order
  calc
    samePrimeFiniteLogTermCore (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
          (p := p) (K := K) N hx)
        =
      samePrimeNatDivEval (p := p) (K := K) N n s hn (z ^ n) hpow_order := by
        rw [samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree
          (p := p) (K := K) hn hz]
        rw [samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
          (p := p) (K := K) hn (Ideal.pow_mem_pow hz n)
          (by
            have h := Nat.factorization_mul_pred_le_pred
              (ell := p) (n := n) (Fact.out : Nat.Prime p) hn
            omega)
          hpow_order]
    _ =
      samePrimeNatDivEval (p := p) (K := K) N n s hn
        (∑ d ∈ (P ^ n).support, (P ^ n).coeff d) hsum_order :=
        samePrimeNatDivEval_eq_of_eq (p := p) (K := K) hn
          hsum_eq hpow_order hsum_order
    _ =
      ∑ d ∈ (P ^ n).support,
        samePrimeNatDivEval (p := p) (K := K) N n s hn ((P ^ n).coeff d)
          (hcoeff_order d) := by
        rw [samePrimeNatDivEval_sum (p := p) (K := K) hn (P ^ n).support
          (fun d => (P ^ n).coeff d) hcoeff_order hsum_order]
    _ =
      ∑ d ∈ (P ^ n).support,
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore
          (p := p) (K := K) N n d x hx := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hnd : n ≤ d := by
          simpa [P] using
            samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_le_of_mem_support
              (p := p) (K := K) N x hd
        have hden : n.factorization p * (p - 1) ≤ d :=
          samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd
        have hcoeff : (P ^ n).coeff d ∈ (lambdaIdeal p K) ^ d := by
          simpa [P] using
            samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
              (p := p) (K := K) N hx n d
        rw [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore, dif_neg hn, dif_pos hnd]
        exact (samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
          (p := p) (K := K) hn hcoeff hden (hcoeff_order d)).symm

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLogTerm_normalizedArtinHasseCoord_eq_homogeneous_support_sum
    (N n : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) (hn : n ≠ 0) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
          (p := p) (K := K) N hx) =
      ∑ d ∈ ((samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) N x) ^ n).support,
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
          (p := p) (K := K) N n d x hx := by
  rw [samePrimeFiniteLogTerm,
    samePrimeFiniteLogTermCore_normalizedArtinHasseCoord_eq_homogeneous_support_sum
      (p := p) (K := K) N n hx hn,
    Finset.mul_sum]
  simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLogTerm_normalizedArtinHasseCoord_eq_homogeneous_cutoff_sum
    (N n : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
          (p := p) (K := K) N hx) =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
          (p := p) (K := K) N n d x hx := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore]
  let P : Polynomial (ValuedIntegerRing p K) :=
    samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x
  let C : ℕ := samePrimeFiniteLogCutoff (p := p) N
  let f : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := fun d =>
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
      (p := p) (K := K) N n d x hx
  have hsupport :
      samePrimeFiniteLogTerm (p := p) (K := K) N n
          (samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x)
          (samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
            (p := p) (K := K) N hx) =
        ∑ d ∈ (P ^ n).support, f d := by
    simpa [P, f] using
      samePrimeFiniteLogTerm_normalizedArtinHasseCoord_eq_homogeneous_support_sum
        (p := p) (K := K) N n hx hn
  have hsupport_union :
      ∑ d ∈ (P ^ n).support, f d =
        ∑ d ∈ (P ^ n).support ∪ Finset.range C, f d := by
    refine Finset.sum_subset (Finset.subset_union_left) ?_
    intro d _hdUnion hdSupport
    exact samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_zero_of_not_mem_support
      (p := p) (K := K) N n d hx (by simpa [P] using hdSupport)
  have hrange_union :
      ∑ d ∈ Finset.range C, f d =
        ∑ d ∈ (P ^ n).support ∪ Finset.range C, f d := by
    refine Finset.sum_subset (Finset.subset_union_right) ?_
    intro d hdUnion hdRange
    have hcut : C ≤ d :=
      Nat.le_of_not_gt (by
        intro hdlt
        exact hdRange (Finset.mem_range.mpr hdlt))
    exact samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_zero_of_cutoff_le_degree
      (p := p) (K := K) N n d hx (by simpa [C] using hcut)
  calc
    samePrimeFiniteLogTerm (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
          (p := p) (K := K) N hx)
        = ∑ d ∈ (P ^ n).support, f d := hsupport
    _ = ∑ d ∈ (P ^ n).support ∪ Finset.range C, f d := hsupport_union
    _ = ∑ d ∈ Finset.range C, f d := hrange_union.symm

omit [NumberField.IsCMField K] in
theorem artinHasseExp_scaledDworkParameter_sub_one_eq_mul_normalized
    (a : ZMod p) :
    artinHasseExp_eval_scaledDworkParameter p K a - 1 =
      scaledDworkParameter p K a *
        artinHasseNormalizedExpMinusOneEval p K
          (scaledDworkParameter p K a)
          (scaledDworkParameter_evalₐ_one (p := p) (K := K) a) :=
  artinHasseExp_eval_sub_one_eq_mul_normalized
    (p := p) (K := K)
    (scaledDworkParameter_evalₐ_one (p := p) (K := K) a)

omit [NumberField.IsCMField K] in
/-- The Dwork Artin-Hasse specialization of the normalized quotient
`X * (E_p(T) - 1) / (E_p(X*T) - 1) - 1`, with
`T = varpi` and `X = omega(a)`.

The nonunit quotient of the two Artin-Hasse differences is represented by the
unit from `kummerLogDworkArtinHasseQuotientDenUnit`. -/
noncomputable def kummerLogDworkArtinHasseNormalizedQuotientArg
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    DworkCompleteIntegerRing p K :=
  algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
      (rationalPadicTeichmuller p
        (kummerLogColumnIndex (p := p) hp_three a : ZMod p)) *
    ((kummerLogDworkArtinHasseQuotientDenUnit
      (p := p) (K := K) hp_three a)⁻¹ :
      (DworkCompleteIntegerRing p K)ˣ) - 1

omit [NumberField.IsCMField K] in
/-- Complete-ring normalized Artin-Hasse factor identity for the Dwork
quotient denominator.

This is where the common `varpi = dworkParameter` factor is cancelled, using
regularity in the complete Dwork ring. No cancellation in the finite quotient
is used. -/
theorem kummerLogDworkArtinHasseQuotientDenUnit_mul_normalized_eq_teich_mul_normalized
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogDworkArtinHasseQuotientDenUnit
        (p := p) (K := K) hp_three a : DworkCompleteIntegerRing p K) *
      artinHasseNormalizedExpMinusOneEval p K
        (dworkParameter p K)
        (dworkParameter_evalₐ_one (p := p) (K := K)) =
    algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
        (rationalPadicTeichmuller p
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)) *
      artinHasseNormalizedExpMinusOneEval p K
        (scaledDworkParameter p K
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p))
        (scaledDworkParameter_evalₐ_one (p := p) (K := K)
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)) := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let z : ZMod p := (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
  let c : S :=
    algebraMap (RationalPadicIntegerRing p) S
      (rationalPadicTeichmuller p z)
  let u : S :=
    (kummerLogDworkArtinHasseQuotientDenUnit
      (p := p) (K := K) hp_three a : S)
  let A1 : S :=
    artinHasseNormalizedExpMinusOneEval p K
      (dworkParameter p K)
      (dworkParameter_evalₐ_one (p := p) (K := K))
  let Az : S :=
    artinHasseNormalizedExpMinusOneEval p K
      (scaledDworkParameter p K z)
      (scaledDworkParameter_evalₐ_one (p := p) (K := K) z)
  have hden :
      u * (artinHasseExp_eval_scaledDworkParameter p K 1 - 1) =
        artinHasseExp_eval_scaledDworkParameter p K z - 1 := by
    simpa [u, z, S] using
      kummerLogDworkArtinHasseQuotientDenUnit_mul_exp_sub_one
        (p := p) (K := K) hp_three a
  have hone :
      artinHasseExp_eval_scaledDworkParameter p K 1 - 1 =
        dworkParameter p K * A1 := by
    simpa [A1, scaledDworkParameter_one (p := p) (K := K)] using
      artinHasseExp_scaledDworkParameter_sub_one_eq_mul_normalized
        (p := p) (K := K) (a := (1 : ZMod p))
  have hz :
      artinHasseExp_eval_scaledDworkParameter p K z - 1 =
        (c * dworkParameter p K) * Az := by
    simpa [Az, c, z, scaledDworkParameter, S] using
      artinHasseExp_scaledDworkParameter_sub_one_eq_mul_normalized
        (p := p) (K := K) (a := z)
  have hmul :
      dworkParameter p K * (u * A1 - c * Az) = 0 := by
    calc
      dworkParameter p K * (u * A1 - c * Az)
          = u * (dworkParameter p K * A1) -
              (c * dworkParameter p K) * Az := by ring
      _ = u * (artinHasseExp_eval_scaledDworkParameter p K 1 - 1) -
              (artinHasseExp_eval_scaledDworkParameter p K z - 1) := by
            rw [hone, hz]
      _ = 0 := by rw [hden, sub_self]
  have hcancel : u * A1 - c * Az = 0 :=
    dworkParameter_regular (p := p) (K := K) hmul
  simpa [u, A1, Az, c, z, S] using sub_eq_zero.mp hcancel

omit [NumberField.IsCMField K] in
/-- Complete-ring normalized quotient identity, in the product form
`(1 + Q_a(varpi)) * A_p(omega(a) varpi) = A_p(varpi)`.

The proof consumes the previous complete-ring cancellation theorem; this is
the identity to reduce modulo `varpi^(p - 1)` before applying finite logs. -/
theorem kummerLogDworkArtinHasseNormalizedQuotientArg_add_one_mul_normalized_eq_normalized
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogDworkArtinHasseNormalizedQuotientArg
        (p := p) (K := K) hp_three a + 1) *
      artinHasseNormalizedExpMinusOneEval p K
        (scaledDworkParameter p K
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p))
        (scaledDworkParameter_evalₐ_one (p := p) (K := K)
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)) =
    artinHasseNormalizedExpMinusOneEval p K
      (dworkParameter p K)
      (dworkParameter_evalₐ_one (p := p) (K := K)) := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let z : ZMod p := (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
  let c : S :=
    algebraMap (RationalPadicIntegerRing p) S
      (rationalPadicTeichmuller p z)
  let u : Sˣ :=
    kummerLogDworkArtinHasseQuotientDenUnit
      (p := p) (K := K) hp_three a
  let A1 : S :=
    artinHasseNormalizedExpMinusOneEval p K
      (dworkParameter p K)
      (dworkParameter_evalₐ_one (p := p) (K := K))
  let Az : S :=
    artinHasseNormalizedExpMinusOneEval p K
      (scaledDworkParameter p K z)
      (scaledDworkParameter_evalₐ_one (p := p) (K := K) z)
  have harg :
      kummerLogDworkArtinHasseNormalizedQuotientArg
          (p := p) (K := K) hp_three a + 1 =
        c * ((u⁻¹ : Sˣ) : S) := by
    simp [kummerLogDworkArtinHasseNormalizedQuotientArg, c, u, z, S]
  have hden :
      (u : S) * A1 = c * Az := by
    simpa [u, A1, Az, c, z, S] using
      kummerLogDworkArtinHasseQuotientDenUnit_mul_normalized_eq_teich_mul_normalized
        (p := p) (K := K) hp_three a
  calc
    (kummerLogDworkArtinHasseNormalizedQuotientArg
          (p := p) (K := K) hp_three a + 1) * Az
        = (c * ((u⁻¹ : Sˣ) : S)) * Az := by rw [harg]
    _ = ((u⁻¹ : Sˣ) : S) * (c * Az) := by ring
    _ = ((u⁻¹ : Sˣ) : S) * ((u : S) * A1) := by rw [← hden]
    _ = A1 := by simp

omit [NumberField.IsCMField K] in
/-- Finite quotient image of the complete-ring normalized quotient identity.
This is obtained by mapping the already-normalized complete-ring statement to
`R / (varpi^(p - 1))`, not by cancelling in the quotient. -/
theorem kummerLogDworkArtinHasseNormalizedQuotientArg_evalₐ_add_one_mul_normalized_eq_normalized
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
        (kummerLogDworkArtinHasseNormalizedQuotientArg
          (p := p) (K := K) hp_three a + 1) *
      AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
        (artinHasseNormalizedExpMinusOneEval p K
          (scaledDworkParameter p K
            (kummerLogColumnIndex (p := p) hp_three a : ZMod p))
          (scaledDworkParameter_evalₐ_one (p := p) (K := K)
            (kummerLogColumnIndex (p := p) hp_three a : ZMod p))) =
    AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
      (artinHasseNormalizedExpMinusOneEval p K
        (dworkParameter p K)
        (dworkParameter_evalₐ_one (p := p) (K := K))) := by
  have h :=
    congrArg (AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1))
      (kummerLogDworkArtinHasseNormalizedQuotientArg_add_one_mul_normalized_eq_normalized
        (p := p) (K := K) hp_three a)
  simpa [map_mul] using h

set_option maxHeartbeats 800000 in
-- The proof compares the Teichmuller scalar with the integral scalar through
-- the completed Dwork ramification identity; the larger heartbeat budget keeps
-- the coercion reductions deterministic.
omit [NumberField.IsCMField K] in
/-- The Dwork Artin-Hasse specialization represents the same normalized
quotient as modulo the Dwork `p`-level `(lambda)^(p-1)`. -/
theorem kummerLogDworkArtinHasseNormalizedQuotientArg_sub_algebraMap_mem_pow_pred
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseNormalizedQuotientArg
        (p := p) (K := K) hp_three a -
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
        (kummerLogNormalizedQuotientFiniteLogArg
          (p := p) (K := K) hp_three a) ∈
      (dworkCompleteLambdaIdeal p K) ^ (p - 1) := by
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  let z : ZMod p := (k : ZMod p)
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  let R₀ : Type := RationalPadicIntegerRing p
  let cU : Rˣ :=
    kummerLogValuedCyclotomicQuotientDenUnit
      (p := p) (K := K) hp_three a
  let dU : Sˣ :=
    kummerLogDworkArtinHasseQuotientDenUnit
      (p := p) (K := K) hp_three a
  let denInv : S := (dU⁻¹ : Sˣ)
  have hk_lt : k < p := by
    have hk_le := kummerLogColumnIndex_le_half (p := p) hp_three a
    omega
  have hk_val : z.val = k := by
    simpa [z] using ZMod.val_natCast_of_lt hk_lt
  have hprime :
      rationalPadicTeichmuller p z - (k : R₀) ∈ rationalPadicPrimeIdeal p := by
    simpa [z, hk_val] using
      rationalPadicTeichmuller_sub_natCast_val_mem_primeIdeal (p := p) z
  have hcoeffRaw :
      algebraMap R₀ S (rationalPadicTeichmuller p z - (k : R₀)) ∈
        (dworkParameterIdeal p K) ^ (1 * (p - 1)) :=
    algebraMap_mem_dworkParameterIdeal_pow_mul_pred_of_mem_rationalPadicPrimeIdeal_pow
      (p := p) (K := K) (q := 1)
      (c := rationalPadicTeichmuller p z - (k : R₀))
      (by simpa using hprime)
  have hcoeff :
      algebraMap R₀ S (rationalPadicTeichmuller p z) -
        algebraMap R S (k : R) ∈ (dworkCompleteLambdaIdeal p K) ^ (p - 1) := by
    have hraw :
        algebraMap R₀ S (rationalPadicTeichmuller p z - (k : R₀)) ∈
          (dworkCompleteLambdaIdeal p K) ^ (p - 1) := by
      simpa [one_mul, dworkParameterIdeal_eq_dworkCompleteLambdaIdeal
        (p := p) (K := K)] using hcoeffRaw
    convert hraw using 1
    rw [map_sub, algebraMap_rationalPadicInteger_natCast_dworkComplete
      (p := p) (K := K) k]
  have hsubeq :
      kummerLogDworkArtinHasseNormalizedQuotientArg
          (p := p) (K := K) hp_three a -
        algebraMap R S (kummerLogNormalizedQuotientFiniteLogArg
          (p := p) (K := K) hp_three a) =
        (algebraMap R₀ S (rationalPadicTeichmuller p z) -
          algebraMap R S (k : R)) * denInv := by
    have hdenInv :
        denInv = algebraMap R S (((cU⁻¹ : Rˣ) : R)) := by
      simp [denInv, dU, cU, kummerLogDworkArtinHasseQuotientDenUnit, R, S]
    change
      (algebraMap R₀ S (rationalPadicTeichmuller p z) * denInv - 1) -
        algebraMap R S ((k : R) * (((cU⁻¹ : Rˣ) : R)) - 1) =
        (algebraMap R₀ S (rationalPadicTeichmuller p z) -
          algebraMap R S (k : R)) * denInv
    rw [map_sub, map_mul, map_one, hdenInv]
    ring
  rw [hsubeq]
  exact ((dworkCompleteLambdaIdeal p K) ^ (p - 1)).mul_mem_right denInv hcoeff

omit [NumberField.IsCMField K] in
/-- In the finite quotient used for the mod-`p` Kummer-log coefficients, the
Dwork Artin-Hasse specialization reduces to the normalized argument. -/
theorem kummerLogDworkArtinHasseNormalizedQuotientArg_evalₐ_pow_pred
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
        (kummerLogDworkArtinHasseNormalizedQuotientArg
          (p := p) (K := K) hp_three a) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
        (kummerLogNormalizedQuotientFiniteLogArg
          (p := p) (K := K) hp_three a) := by
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  have hmem :=
    kummerLogDworkArtinHasseNormalizedQuotientArg_sub_algebraMap_mem_pow_pred
      (p := p) (K := K) hp_three a
  have hzero :
      AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
        (kummerLogDworkArtinHasseNormalizedQuotientArg
            (p := p) (K := K) hp_three a -
          algebraMap R S (kummerLogNormalizedQuotientFiniteLogArg
            (p := p) (K := K) hp_three a)) = 0 :=
    dworkComplete_evalₐ_eq_zero_of_mem_lambdaIdeal_pow
      (p := p) (K := K) hmem
  rw [map_sub] at hzero
  simpa [S, R, AdicCompletion.algebraMap_apply] using sub_eq_zero.mp hzero

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLog_eq_sub_of_productCoord_sub_mem {N : ℕ}
    {x y z : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) (hz : z ∈ lambdaIdeal p K)
    (hsub :
      samePrimeFiniteLogProductCoord (p := p) (K := K) x y - z ∈
        (lambdaIdeal p K) ^ (N + 1)) :
    samePrimeFiniteLog (p := p) (K := K) N x hx =
      samePrimeFiniteLog (p := p) (K := K) N z hz -
        samePrimeFiniteLog (p := p) (K := K) N y hy := by
  let xy : ValuedIntegerRing p K :=
    samePrimeFiniteLogProductCoord (p := p) (K := K) x y
  have hxy : xy ∈ lambdaIdeal p K :=
    samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hx hy
  have hlogxy :
      samePrimeFiniteLog (p := p) (K := K) N xy hxy =
        samePrimeFiniteLog (p := p) (K := K) N x hx +
          samePrimeFiniteLog (p := p) (K := K) N y hy := by
    simpa [xy] using samePrimeFiniteLog_add_add_mul
      (p := p) (K := K) N hx hy
  have hlogz :
      samePrimeFiniteLog (p := p) (K := K) N xy hxy =
        samePrimeFiniteLog (p := p) (K := K) N z hz :=
    samePrimeFiniteLog_eq_of_sub_mem (p := p) (K := K) hxy hz
      (by simpa [xy] using hsub)
  calc
    samePrimeFiniteLog (p := p) (K := K) N x hx =
        (samePrimeFiniteLog (p := p) (K := K) N x hx +
            samePrimeFiniteLog (p := p) (K := K) N y hy) -
          samePrimeFiniteLog (p := p) (K := K) N y hy := by
          rw [add_sub_cancel_right]
    _ =
        samePrimeFiniteLog (p := p) (K := K) N xy hxy -
          samePrimeFiniteLog (p := p) (K := K) N y hy := by
          rw [hlogxy]
    _ =
        samePrimeFiniteLog (p := p) (K := K) N z hz -
          samePrimeFiniteLog (p := p) (K := K) N y hy := by
          rw [hlogz]

/-- Finite logarithm of the Dwork Artin-Hasse specialization, represented by
the quotient-compatible finite-log argument. -/
noncomputable def kummerLogDworkArtinHasseSpecializedFiniteLog
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ ((p - 2) + 1) :=
  kummerLogNormalizedQuotientFiniteLog (p := p) (K := K) hp_three a (p - 2)

omit [NumberField.IsCMField K] in
/-- The finite logarithm is the difference of the two normalized
Artin-Hasse finite logarithms, after first proving the normalized quotient
identity in the complete Dwork ring and then reducing modulo
`varpi^(p - 1)`. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLog
        (p := p) (K := K) hp_three a =
      samePrimeFiniteLog (p := p) (K := K) (p - 2)
        (dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2))
        (dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
          (p := p) (K := K) (p - 2)) -
      samePrimeFiniteLog (p := p) (K := K) (p - 2)
        (scaledDworkParameterNormalizedCoordApprox
          (p := p) (K := K)
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p) (p - 2))
        (scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
          (p := p) (K := K)
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p) (p - 2)) := by
  classical
  let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
  let z : ZMod p := (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
  let q : ValuedIntegerRing p K :=
    kummerLogNormalizedQuotientFiniteLogArg (p := p) (K := K) hp_three a
  let X : ValuedIntegerRing p K :=
    dworkParameterNormalizedApprox (p := p) (K := K) (p - 2)
  let Y : ValuedIntegerRing p K :=
    scaledDworkParameterNormalizedApprox (p := p) (K := K) z (p - 2)
  let x : ValuedIntegerRing p K :=
    dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2)
  let y : ValuedIntegerRing p K :=
    scaledDworkParameterNormalizedCoordApprox (p := p) (K := K) z (p - 2)
  have hq : q ∈ lambdaIdeal p K :=
    kummerLogNormalizedQuotientFiniteLogArg_mem_lambdaIdeal
      (p := p) (K := K) hp_three a
  have hx : x ∈ lambdaIdeal p K := by
    simpa [x] using dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
      (p := p) (K := K) (p - 2)
  have hy : y ∈ lambdaIdeal p K := by
    simpa [y, z] using scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
      (p := p) (K := K) z (p - 2)
  have harg :
      AdicCompletion.evalₐ I (p - 1)
          (kummerLogDworkArtinHasseNormalizedQuotientArg
            (p := p) (K := K) hp_three a + 1) =
        Ideal.Quotient.mk (I ^ (p - 1)) (q + 1) := by
    have hqeval :=
      kummerLogDworkArtinHasseNormalizedQuotientArg_evalₐ_pow_pred
        (p := p) (K := K) hp_three a
    rw [map_add, hqeval]
    rfl
  have hY :
      AdicCompletion.evalₐ I (p - 1)
          (artinHasseNormalizedExpMinusOneEval p K
            (scaledDworkParameter p K z)
            (scaledDworkParameter_evalₐ_one (p := p) (K := K) z)) =
        Ideal.Quotient.mk (I ^ (p - 1)) Y := by
    have hpow : (p - 2) + 1 = p - 1 := by omega
    rw [← hpow]
    simpa [I, Y, z] using
      evalₐ_artinHasseNormalized_scaledDworkParameter_eq_mk_normalizedApprox
        (p := p) (K := K) z (p - 2)
  have hX :
      AdicCompletion.evalₐ I (p - 1)
          (artinHasseNormalizedExpMinusOneEval p K
            (dworkParameter p K)
            (dworkParameter_evalₐ_one (p := p) (K := K))) =
        Ideal.Quotient.mk (I ^ (p - 1)) X := by
    have hpow : (p - 2) + 1 = p - 1 := by omega
    rw [← hpow]
    simpa [I, X] using
      evalₐ_artinHasseNormalized_dworkParameter_eq_mk_normalizedApprox
        (p := p) (K := K) (p - 2)
  have hprod_mk :
      Ideal.Quotient.mk (I ^ (p - 1)) ((q + 1) * Y) =
        Ideal.Quotient.mk (I ^ (p - 1)) X := by
    have hnorm :=
      kummerLogDworkArtinHasseNormalizedQuotientArg_evalₐ_add_one_mul_normalized_eq_normalized
        (p := p) (K := K) hp_three a
    rw [harg, hY, hX] at hnorm
    simpa [I] using hnorm
  have hsub_pred :
      samePrimeFiniteLogProductCoord (p := p) (K := K) q y - x ∈
        (lambdaIdeal p K) ^ (p - 1) := by
    have hmem :
        (q + 1) * Y - X ∈ I ^ (p - 1) :=
      Ideal.Quotient.eq.mp hprod_mk
    have hsame :
        samePrimeFiniteLogProductCoord (p := p) (K := K) q y - x =
          (q + 1) * Y - X := by
      simp [samePrimeFiniteLogProductCoord, x, y, X, Y,
        dworkParameterNormalizedCoordApprox,
        scaledDworkParameterNormalizedCoordApprox]
      ring
    simpa [I, hsame] using hmem
  have hsub :
      samePrimeFiniteLogProductCoord (p := p) (K := K) q y - x ∈
        (lambdaIdeal p K) ^ ((p - 2) + 1) := by
    simpa [show (p - 2) + 1 = p - 1 by omega] using hsub_pred
  rw [kummerLogDworkArtinHasseSpecializedFiniteLog,
    kummerLogNormalizedQuotientFiniteLog]
  simpa [q, x, y, z] using
    samePrimeFiniteLog_eq_sub_of_productCoord_sub_mem
      (p := p) (K := K) (N := p - 2) hq hy hx hsub

omit [NumberField.IsCMField K] in
/-- The same normalized finite-log identity in the `p - 1` quotient used by
the Dwork-coordinate coefficient API. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLog_factorPow_eq_normalizedApprox_logs
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
        p - 1 ≤ (p - 2) + 1)
      (kummerLogDworkArtinHasseSpecializedFiniteLog
        (p := p) (K := K) hp_three a) =
      Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
          p - 1 ≤ (p - 2) + 1)
        (samePrimeFiniteLog (p := p) (K := K) (p - 2)
          (dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2))
          (dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
            (p := p) (K := K) (p - 2))) -
      Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
          p - 1 ≤ (p - 2) + 1)
        (samePrimeFiniteLog (p := p) (K := K) (p - 2)
          (scaledDworkParameterNormalizedCoordApprox
            (p := p) (K := K)
            (kummerLogColumnIndex (p := p) hp_three a : ZMod p) (p - 2))
          (scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
            (p := p) (K := K)
            (kummerLogColumnIndex (p := p) hp_three a : ZMod p) (p - 2))) := by
  rw [kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs
    (p := p) (K := K) hp_three a]
  rw [map_sub]

theorem concreteKummerLogVector_evalₐ_pow_pred_eq_two_nsmul_dworkArtinHasseSpecializedFiniteLog
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    AdicCompletion.evalₐ (lambdaIdeal p K) ((p - 2) + 1)
        (concreteKummerLogVector (p := p) (K := K) hp_three a :
          DworkCompleteIntegerRing p K) =
      2 • kummerLogDworkArtinHasseSpecializedFiniteLog
        (p := p) (K := K) hp_three a :=
  concreteKummerLogVector_evalₐ_pow_pred_eq_two_nsmul_normalizedQuotientFiniteLog
    (p := p) (K := K) hp_three a

end CyclotomicUnits
end KummerCriterion

end
