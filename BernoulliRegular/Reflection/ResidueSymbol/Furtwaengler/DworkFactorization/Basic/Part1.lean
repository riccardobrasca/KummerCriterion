module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse.Part1
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse.Part2
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Stickelberger.Part1
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DieudonneDwork.Part1
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DieudonneDwork.Part2
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.Fintype.Units
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Ring.Associated
public import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.TeichmullerSeries
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.Fintype.Fin
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Basic Dwork factorization algebra

Split from `DworkFactorization.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- Substitution of a nilpotent constant into a power series is the finite
polynomial evaluation at that constant. -/
theorem powerSeries_subst_C_eq_C_sum_range_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ) (ha : a ^ (N + 1) = 0)
    (F : PowerSeries A) :
    PowerSeries.subst (PowerSeries.C a) F =
      PowerSeries.C (∑ n ∈ Finset.range (N + 1), PowerSeries.coeff n F * a ^ n) := by
  have hnil : IsNilpotent a := ⟨N + 1, ha⟩
  have hsubst : PowerSeries.HasSubst (PowerSeries.C a : PowerSeries A) := by
    change IsNilpotent (PowerSeries.constantCoeff (PowerSeries.C a : PowerSeries A))
    simpa using hnil
  ext m
  by_cases hm : m = 0
  · subst m
    rw [PowerSeries.coeff_subst' hsubst]
    rw [finsum_eq_sum_of_support_subset
      (fun d : ℕ => PowerSeries.coeff d F •
        PowerSeries.coeff 0 ((PowerSeries.C a : PowerSeries A) ^ d))
      (s := Finset.range (N + 1))]
    · simp [smul_eq_mul]
    · intro d hd
      by_contra hdmem
      have hle : N + 1 ≤ d := Nat.le_of_not_gt (by simpa using hdmem)
      have hpow : a ^ d = 0 := pow_eq_zero_of_le hle ha
      exact hd (by simp [hpow])
  · rw [PowerSeries.coeff_subst' hsubst]
    rw [finsum_eq_zero_of_forall_eq_zero]
    · exact (PowerSeries.coeff_ne_zero_C hm).symm
    · intro d
      have hcoeff :
          PowerSeries.coeff m ((PowerSeries.C a : PowerSeries A) ^ d) = 0 := by
        rw [← map_pow (PowerSeries.C : A →+* PowerSeries A) a d]
        exact PowerSeries.coeff_ne_zero_C hm
      simp [hcoeff]

/-- Substitution of a nilpotent constant into a power series is the constant
power series attached to the finite truncation evaluation. -/
theorem powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ) (ha : a ^ (N + 1) = 0)
    (F : PowerSeries A) :
    PowerSeries.subst (PowerSeries.C a) F =
      PowerSeries.C
        ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) := by
  rw [powerSeries_subst_C_eq_C_sum_range_of_pow_succ_eq_zero a N ha F]
  congr 1
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp

/-- Finite truncation evaluation at a nilpotent element is multiplicative. -/
theorem powerSeries_trunc_eval₂_mul_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ) (ha : a ^ (N + 1) = 0)
    (F G : PowerSeries A) :
    (PowerSeries.trunc (N + 1) (F * G)).eval₂ (RingHom.id A) a =
      (PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a *
        (PowerSeries.trunc (N + 1) G).eval₂ (RingHom.id A) a := by
  have hCa : PowerSeries.HasSubst (PowerSeries.C a : PowerSeries A) := by
    change IsNilpotent (PowerSeries.constantCoeff (PowerSeries.C a : PowerSeries A))
    exact ⟨N + 1, by simpa using ha⟩
  apply PowerSeries.C_injective
  calc
    PowerSeries.C ((PowerSeries.trunc (N + 1) (F * G)).eval₂ (RingHom.id A) a)
        = PowerSeries.subst (PowerSeries.C a) (F * G) := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha]
    _ = PowerSeries.subst (PowerSeries.C a) F *
          PowerSeries.subst (PowerSeries.C a) G := by
          rw [PowerSeries.subst_mul hCa]
    _ = PowerSeries.C ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) *
          PowerSeries.C ((PowerSeries.trunc (N + 1) G).eval₂ (RingHom.id A) a) := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha F,
            powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha G]
    _ = PowerSeries.C
          ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a *
            (PowerSeries.trunc (N + 1) G).eval₂ (RingHom.id A) a) := by
          simp

end Furtwaengler

end BernoulliRegular

end
