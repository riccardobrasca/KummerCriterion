module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkAssembly
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkWitt
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingCongruence
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceCoefficientExpansion
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
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
