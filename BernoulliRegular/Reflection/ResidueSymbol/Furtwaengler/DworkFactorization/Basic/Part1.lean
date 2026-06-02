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

/-- The finite truncation `∑_{n ≤ N} λ_n T^n` of a Dwork theta series. -/
def dworkThetaTrunc {A : Type*} [CommSemiring A]
    (dworkCoeff : ℕ → A) (N : ℕ) (u : A) : A :=
  ∑ n ∈ Finset.range (N + 1), dworkCoeff n * u ^ n






















/-- An element of `I` becomes nilpotent modulo `I^(N+1)`. -/
theorem quotient_mk_mem_pow_succ_eq_zero
    {A : Type*} [CommRing A] (I : Ideal A) {x : A} (hx : x ∈ I) (N : ℕ) :
    (Ideal.Quotient.mk (I ^ (N + 1)) x) ^ (N + 1) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hx (N + 1)

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

/-- Finite truncation evaluation at a nilpotent element commutes with powers. -/
theorem powerSeries_trunc_eval₂_pow_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ) (ha : a ^ (N + 1) = 0)
    (F : PowerSeries A) (m : ℕ) :
    (PowerSeries.trunc (N + 1) (F ^ m)).eval₂ (RingHom.id A) a =
      ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) ^ m := by
  have hCa : PowerSeries.HasSubst (PowerSeries.C a : PowerSeries A) := by
    change IsNilpotent (PowerSeries.constantCoeff (PowerSeries.C a : PowerSeries A))
    exact ⟨N + 1, by simpa using ha⟩
  apply PowerSeries.C_injective
  calc
    PowerSeries.C ((PowerSeries.trunc (N + 1) (F ^ m)).eval₂ (RingHom.id A) a)
        = PowerSeries.subst (PowerSeries.C a) (F ^ m) := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha]
    _ = PowerSeries.subst (PowerSeries.C a) F ^ m := by
          rw [PowerSeries.subst_pow hCa]
    _ = PowerSeries.C ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) ^ m := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha F]
    _ = PowerSeries.C
          (((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) ^ m) := by
          simp





/-- Evaluating `F(T^r)` at a nilpotent element is the same as evaluating `F`
at the corresponding power. -/
theorem powerSeries_trunc_eval₂_subst_X_pow_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N r : ℕ) (hr : r ≠ 0)
    (ha : a ^ (N + 1) = 0) (ha_pow : (a ^ r) ^ (N + 1) = 0)
    (F : PowerSeries A) :
    (PowerSeries.trunc (N + 1)
        (PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ r) F)).eval₂
        (RingHom.id A) a =
      (PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) (a ^ r) := by
  have hCa : PowerSeries.HasSubst (PowerSeries.C a : PowerSeries A) := by
    change IsNilpotent (PowerSeries.constantCoeff (PowerSeries.C a : PowerSeries A))
    exact ⟨N + 1, by simpa using ha⟩
  have hXr : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries A) ^ r) :=
    PowerSeries.HasSubst.X_pow hr
  apply PowerSeries.C_injective
  calc
    PowerSeries.C
        ((PowerSeries.trunc (N + 1)
          (PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ r) F)).eval₂
          (RingHom.id A) a)
        = PowerSeries.subst (PowerSeries.C a)
            (PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ r) F) := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha]
    _ = PowerSeries.subst
          (PowerSeries.subst (PowerSeries.C a) ((PowerSeries.X : PowerSeries A) ^ r)) F := by
          rw [PowerSeries.subst_comp_subst_apply hXr hCa]
    _ = PowerSeries.subst (PowerSeries.C (a ^ r)) F := by
          congr 1
          rw [PowerSeries.subst_pow hCa, PowerSeries.subst_X hCa]
          simp
    _ = PowerSeries.C
          ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) (a ^ r)) := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero (a ^ r) N ha_pow F]

/-- Evaluating a rescaled finite truncation at `a` is the same as evaluating
the original finite truncation at `a * u`. -/
theorem powerSeries_trunc_rescale_eval₂_eq_trunc_eval₂_mul
    {A : Type*} [CommSemiring A] (F : PowerSeries A) (N : ℕ) (a u : A) :
    (PowerSeries.trunc (N + 1) (PowerSeries.rescale u F)).eval₂ (RingHom.id A) a =
      (PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) (a * u) := by
  rw [PowerSeries.eval₂_trunc_eq_sum_range, PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [PowerSeries.coeff_rescale, mul_pow, mul_assoc, mul_comm]

/-- Two truncated ordinary-exponential correction factors multiply by adding
their target arguments, after extracting the common nilpotent parameter. -/
theorem rescale_exp_trunc_eval₂_mul
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) (N : ℕ)
    (δ x y : A) (hδ : δ ^ (N + 1) = 0) :
    let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * x) *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * y) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (x + y)) := by
  dsimp only
  let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
  have hmul :=
    powerSeries_trunc_eval₂_mul_of_pow_succ_eq_zero
      (A := A) δ N hδ (PowerSeries.rescale x Rps) (PowerSeries.rescale y Rps)
  have hformal : PowerSeries.rescale x Rps * PowerSeries.rescale y Rps =
      PowerSeries.rescale (x + y) Rps := by
    simpa [Rps] using rescale_exp_mapTo_mul r φ x y
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * x) *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * y)
        =
          (PowerSeries.trunc (N + 1) (PowerSeries.rescale x Rps)).eval₂
              (RingHom.id A) δ *
            (PowerSeries.trunc (N + 1) (PowerSeries.rescale y Rps)).eval₂
              (RingHom.id A) δ := by
          rw [powerSeries_trunc_rescale_eval₂_eq_trunc_eval₂_mul,
            powerSeries_trunc_rescale_eval₂_eq_trunc_eval₂_mul]
    _ = (PowerSeries.trunc (N + 1)
            (PowerSeries.rescale x Rps * PowerSeries.rescale y Rps)).eval₂
            (RingHom.id A) δ := by
          rw [hmul]
    _ = (PowerSeries.trunc (N + 1) (PowerSeries.rescale (x + y) Rps)).eval₂
            (RingHom.id A) δ := by
          rw [hformal]
    _ = (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (x + y)) := by
          rw [powerSeries_trunc_rescale_eval₂_eq_trunc_eval₂_mul]



end Furtwaengler

end BernoulliRegular

end
