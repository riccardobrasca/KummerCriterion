module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import BernoulliRegular.Reflection.Local.Graded
public import BernoulliRegular.Reflection.Local.Completion.Part1

/-!
# Completed local principal units

This file starts the REF-10d3b completed endpoint layer.  The localized ring
`Localization.AtPrime` is not complete, so the reverse `p`-power endpoint is
recorded in the adic completion at the cyclotomic maximal ideal.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The completed cyclotomic root, viewed as an element of completed `U_1`. -/
noncomputable def completedLocalCyclotomicZetaPrincipalUnit :
    completedPrincipalUnitSubgroup p K 1 :=
  ⟨completedLocalCyclotomicZetaUnit p K,
    completedLocalCyclotomicZetaUnit_mem_completedPrincipalUnitSubgroup_one (p := p) (K := K)⟩


theorem exists_completedPrincipalUnit_pow_prime_sub_one_add_mem_next
    {n : ℕ} (hn : 2 ≤ n) {x : completedLocalCyclotomicRing p K}
    (hx : x ∈ completedLocalCyclotomicMaximalIdeal p K ^ (n + (p - 1))) :
    ∃ w : completedLocalCyclotomicUnitGroup p K,
      w ∈ completedPrincipalUnitSubgroup p K n ∧
        ((w ^ p : completedLocalCyclotomicUnitGroup p K) :
            completedLocalCyclotomicRing p K) - (1 + x) ∈
          completedLocalCyclotomicMaximalIdeal p K ^ (n + (p - 1) + 1) := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let π : S := completedLocalCyclotomicUniformizer p K
  obtain ⟨y, hyM, hpy⟩ :=
    exists_natCast_prime_mul_eq_of_mem_completedLocalCyclotomicMaximalIdeal_pow_add_pred
      (p := p) (K := K) (n := n) hx
  obtain ⟨z, hz⟩ :=
    exists_uniformizer_pow_mul_eq_of_mem_completedLocalCyclotomicMaximalIdeal_pow
      (p := p) (K := K) (n := n) hyM
  have hn_ne : n ≠ 0 := by omega
  let w : completedLocalCyclotomicUnitGroup p K :=
    completedOneAddUnitOfMemMaximalIdealPow (p := p) (K := K) (n := n) hn_ne hyM
  have hw_coe : (w : S) = 1 + y := by
    simp [w]
  have hvu : π ∣ π ^ n := by
    refine ⟨π ^ (n - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hquv : (p : S) * π ^ n * π ∣ (π ^ n) ^ p :=
    natCast_prime_mul_uniformizer_pow_mul_uniformizer_dvd_uniformizer_pow_prime
      (p := p) (K := K) hn
  obtain ⟨b, hb⟩ := exists_one_add_mul_pow_prime_eq_of_dvd
    (R := S) (q := p) (u := π ^ n) (v := π)
    (Fact.out : Nat.Prime p) hvu hquv z
  have hpM : (p : S) ∈ M ^ (p - 1) := by
    simpa [S, M] using
      natCast_prime_mem_completedLocalCyclotomicMaximalIdeal_pow_pred (p := p) (K := K)
  have hπn : π ^ n ∈ M ^ n := by
    rw [completedLocalCyclotomicMaximalIdeal_pow_eq_span_uniformizer_pow (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self (π ^ n)
  have hπ : π ∈ M := by
    change completedLocalCyclotomicUniformizer p K ∈ completedLocalCyclotomicMaximalIdeal p K
    rw [completedLocalCyclotomicMaximalIdeal_eq_span_uniformizer (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self π
  have hprod : (p : S) * π ^ n * π ∈ M ^ (n + (p - 1) + 1) := by
    have hmul₁ : π ^ n * π ∈ M ^ n * M :=
      Ideal.mul_mem_mul hπn hπ
    have hmul₂ : (p : S) * (π ^ n * π) ∈ M ^ (p - 1) * (M ^ n * M) :=
      Ideal.mul_mem_mul hpM hmul₁
    have hIcomm : M ^ (p - 1) * (M ^ n * M) = (M ^ n * M) * M ^ (p - 1) := by
      rw [mul_comm]
    have hmul₃ : (p : S) * (π ^ n * π) ∈ (M ^ n * M) * M ^ (p - 1) := by
      rwa [hIcomm] at hmul₂
    have hIassoc : (M ^ n * M) * M ^ (p - 1) = M ^ n * (M * M ^ (p - 1)) := by
      rw [mul_assoc]
    have hmul₄ : (p : S) * (π ^ n * π) ∈ M ^ n * (M * M ^ (p - 1)) := by
      rwa [hIassoc] at hmul₃
    simpa [pow_add, mul_assoc, add_assoc, add_comm, add_left_comm] using hmul₄
  have hpxz : (p : S) * π ^ n * z = x := by
    rw [← hz] at hpy
    simpa [mul_assoc, S, π] using hpy
  refine ⟨w, ?_, ?_⟩
  · rw [mem_completedPrincipalUnitSubgroup_iff]
    simpa [hw_coe] using hyM
  · have hpow :
        ((w ^ p : completedLocalCyclotomicUnitGroup p K) : S) =
          1 + x + ((p : S) * π ^ n * π * b) := by
      rw [Units.val_pow_eq_pow_val, hw_coe, ← hz, hb, mul_add, hpxz]
      ring
    rw [hpow]
    have htail : (p : S) * π ^ n * π * b ∈ M ^ (n + (p - 1) + 1) :=
      Ideal.mul_mem_right b (M ^ (n + (p - 1) + 1)) hprod
    simpa using htail

private theorem mem_ideal_smul_top_iff_self {R : Type*} [CommRing R]
    (I : Ideal R) {x : R} :
    x ∈ I • (⊤ : Submodule R R) ↔ x ∈ I := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) ?_
    · simpa [smul_eq_mul] using I.mul_mem_right y hr
    · intro x y hx hy
      exact I.add_mem hx hy
  · intro hx
    have h : x • (1 : R) ∈ I • (⊤ : Submodule R R) :=
      Submodule.smul_mem_smul hx Submodule.mem_top
    simpa [smul_eq_mul] using h

private structure CompletedPthRootApprox
    (u : completedLocalCyclotomicUnitGroup p K) (n : ℕ) where
  val : completedLocalCyclotomicUnitGroup p K
  mem_two : val ∈ completedPrincipalUnitSubgroup p K 2
  err : ((val ^ p : completedLocalCyclotomicUnitGroup p K) :
      completedLocalCyclotomicRing p K) - (u : completedLocalCyclotomicRing p K) ∈
    completedLocalCyclotomicMaximalIdeal p K ^ (n + 2 + (p - 1))

private noncomputable def completedPthRootApproxZero
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) :
    CompletedPthRootApprox p K u 0 where
  val := 1
  mem_two := one_mem_completedPrincipalUnitSubgroup (p := p) (K := K) 2
  err := by
    let S := completedLocalCyclotomicRing p K
    let M := completedLocalCyclotomicMaximalIdeal p K
    rw [mem_completedPrincipalUnitSubgroup_iff] at hu
    have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
    have hidx : 0 + 2 + (p - 1) = p + 1 := by omega
    rw [hidx]
    have hneg : -((u : S) - 1) ∈ M ^ (p + 1) := (M ^ (p + 1)).neg_mem hu
    simpa [S, sub_eq_add_neg, add_comm] using hneg

private noncomputable def completedPthRootApproxResidual
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    completedLocalCyclotomicRing p K :=
  (u : completedLocalCyclotomicRing p K) *
      (((A.val ^ p : completedLocalCyclotomicUnitGroup p K)⁻¹ :
        completedLocalCyclotomicUnitGroup p K) : completedLocalCyclotomicRing p K) - 1

private theorem completedPthRootApproxResidual_mem
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    completedPthRootApproxResidual (p := p) (K := K) A ∈
      completedLocalCyclotomicMaximalIdeal p K ^ (n + 2 + (p - 1)) := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let a : completedLocalCyclotomicUnitGroup p K := A.val ^ p
  have ha_inv : ((a : completedLocalCyclotomicUnitGroup p K) : S) *
      (((a : completedLocalCyclotomicUnitGroup p K)⁻¹ :
        completedLocalCyclotomicUnitGroup p K) : S) = 1 :=
    Units.mul_inv a
  have ha_inv_pow : ((A.val : S) ^ p) * (((A.val : completedLocalCyclotomicUnitGroup p K)⁻¹ :
      completedLocalCyclotomicUnitGroup p K) : S) ^ p = 1 := by
    simpa [S, a, Units.val_pow_eq_pow_val, Units.inv_pow_eq_pow_inv] using ha_inv
  have hmul : (((A.val ^ p : completedLocalCyclotomicUnitGroup p K) : S) -
        (u : S)) *
        ((((A.val ^ p : completedLocalCyclotomicUnitGroup p K)⁻¹ :
          completedLocalCyclotomicUnitGroup p K) : S)) ∈
      M ^ (n + 2 + (p - 1)) :=
    Ideal.mul_mem_right _ _ A.err
  have hneg := (M ^ (n + 2 + (p - 1))).neg_mem hmul
  have hres :
      completedPthRootApproxResidual (p := p) (K := K) A =
        -((((A.val ^ p : completedLocalCyclotomicUnitGroup p K) : S) - (u : S)) *
          ((((A.val ^ p : completedLocalCyclotomicUnitGroup p K)⁻¹ :
            completedLocalCyclotomicUnitGroup p K) : S))) := by
    simp only [completedPthRootApproxResidual, Units.val_pow_eq_pow_val,
      Units.inv_pow_eq_pow_inv] at ha_inv ⊢
    rw [sub_mul, ha_inv_pow]
    ring
  rw [hres]
  exact hneg

private noncomputable def completedPthRootCorrection
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    completedLocalCyclotomicUnitGroup p K :=
  Classical.choose
    (exists_completedPrincipalUnit_pow_prime_sub_one_add_mem_next (p := p) (K := K)
      (n := n + 2) (by omega : 2 ≤ n + 2)
      (completedPthRootApproxResidual_mem (p := p) (K := K) A))

private theorem completedPthRootCorrection_mem
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    completedPthRootCorrection (p := p) (K := K) A ∈
      completedPrincipalUnitSubgroup p K (n + 2) :=
  (Classical.choose_spec
    (exists_completedPrincipalUnit_pow_prime_sub_one_add_mem_next (p := p) (K := K)
      (n := n + 2) (by omega : 2 ≤ n + 2)
      (completedPthRootApproxResidual_mem (p := p) (K := K) A))).1

private theorem completedPthRootCorrection_err
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    (((completedPthRootCorrection (p := p) (K := K) A) ^ p :
        completedLocalCyclotomicUnitGroup p K) :
        completedLocalCyclotomicRing p K) -
      (1 + completedPthRootApproxResidual (p := p) (K := K) A) ∈
        completedLocalCyclotomicMaximalIdeal p K ^ ((n + 2) + (p - 1) + 1) :=
  (Classical.choose_spec
    (exists_completedPrincipalUnit_pow_prime_sub_one_add_mem_next (p := p) (K := K)
      (n := n + 2) (by omega : 2 ≤ n + 2)
      (completedPthRootApproxResidual_mem (p := p) (K := K) A))).2

private noncomputable def completedPthRootApproxStep
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    CompletedPthRootApprox p K u (n + 1) where
  val := A.val * completedPthRootCorrection (p := p) (K := K) A
  mem_two := by
    refine (completedPrincipalUnitSubgroup p K 2).mul_mem A.mem_two ?_
    exact completedPrincipalUnitSubgroup_mono (p := p) (K := K)
      (m := n + 2) (n := 2) (by omega)
      (completedPthRootCorrection_mem (p := p) (K := K) A)
  err := by
    let S := completedLocalCyclotomicRing p K
    let M := completedLocalCyclotomicMaximalIdeal p K
    let c := completedPthRootCorrection (p := p) (K := K) A
    let r := completedPthRootApproxResidual (p := p) (K := K) A
    let a : completedLocalCyclotomicUnitGroup p K := A.val ^ p
    have ha_inv : ((a : completedLocalCyclotomicUnitGroup p K) : S) *
        (((a : completedLocalCyclotomicUnitGroup p K)⁻¹ :
          completedLocalCyclotomicUnitGroup p K) : S) = 1 :=
      Units.mul_inv a
    have hr_eq : 1 + r = (u : S) *
        (((a : completedLocalCyclotomicUnitGroup p K)⁻¹ :
          completedLocalCyclotomicUnitGroup p K) : S) := by
      simp [r, completedPthRootApproxResidual, a]
    have ha_res : ((a : completedLocalCyclotomicUnitGroup p K) : S) * (1 + r) =
        (u : S) := by
      rw [hr_eq]
      calc
        ((a : completedLocalCyclotomicUnitGroup p K) : S) *
            ((u : S) * (((a : completedLocalCyclotomicUnitGroup p K)⁻¹ :
              completedLocalCyclotomicUnitGroup p K) : S)) =
          (u : S) * (((a : completedLocalCyclotomicUnitGroup p K) : S) *
            (((a : completedLocalCyclotomicUnitGroup p K)⁻¹ :
              completedLocalCyclotomicUnitGroup p K) : S)) := by ring
        _ = (u : S) := by rw [ha_inv, mul_one]
    have hcerr := completedPthRootCorrection_err (p := p) (K := K) A
    have hmul : ((a : completedLocalCyclotomicUnitGroup p K) : S) *
        (((c ^ p : completedLocalCyclotomicUnitGroup p K) : S) - (1 + r)) ∈
        M ^ ((n + 2) + (p - 1) + 1) :=
      Ideal.mul_mem_left _ _ hcerr
    have htarget :
        (((A.val * c) ^ p : completedLocalCyclotomicUnitGroup p K) : S) -
            (u : S) =
          ((a : completedLocalCyclotomicUnitGroup p K) : S) *
            (((c ^ p : completedLocalCyclotomicUnitGroup p K) : S) - (1 + r)) := by
      rw [mul_sub, ha_res]
      simp [a, c, mul_pow]
    have hidx : (n + 1) + 2 + (p - 1) = (n + 2) + (p - 1) + 1 := by omega
    rw [hidx, htarget]
    exact hmul

private noncomputable def completedPthRootApproxSeq
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) :
    (n : ℕ) → CompletedPthRootApprox p K u n
  | 0 => completedPthRootApproxZero (p := p) (K := K) hu
  | n + 1 => completedPthRootApproxStep (p := p) (K := K)
      (completedPthRootApproxSeq hu n)

private theorem completedPthRootApproxSeq_succ_sub_mem
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) (n : ℕ) :
    ((completedPthRootApproxSeq (p := p) (K := K) hu (n + 1)).val :
        completedLocalCyclotomicRing p K) -
      ((completedPthRootApproxSeq (p := p) (K := K) hu n).val :
        completedLocalCyclotomicRing p K) ∈
        completedLocalCyclotomicMaximalIdeal p K ^ (n + 2) := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let A := completedPthRootApproxSeq (p := p) (K := K) hu n
  let c := completedPthRootCorrection (p := p) (K := K) A
  have hc : (c : S) - 1 ∈ M ^ (n + 2) := by
    simpa [c, M] using completedPthRootCorrection_mem (p := p) (K := K) A
  have hmul : (A.val : S) * ((c : S) - 1) ∈ M ^ (n + 2) :=
    Ideal.mul_mem_left _ _ hc
  change ((completedPthRootApproxStep (p := p) (K := K) A).val : S) - (A.val : S) ∈
    M ^ (n + 2)
  convert hmul using 1
  simp [completedPthRootApproxStep, A, c]
  ring

private theorem completedPthRootApproxSeq_smodEq
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) :
    ∀ {m n : ℕ}, m ≤ n →
      ((completedPthRootApproxSeq (p := p) (K := K) hu m).val :
          completedLocalCyclotomicRing p K) ≡
        ((completedPthRootApproxSeq (p := p) (K := K) hu n).val :
          completedLocalCyclotomicRing p K)
        [SMOD (completedLocalCyclotomicMaximalIdeal p K ^ m •
          (⊤ : Submodule (completedLocalCyclotomicRing p K)
            (completedLocalCyclotomicRing p K)))] := by
  intro m n hmn
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst hm
      exact SModEq.rfl
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · refine (ih hmn').trans ?_
        rw [SModEq.sub_mem]
        have hadj := completedPthRootApproxSeq_succ_sub_mem (p := p) (K := K) hu n
        have hmem : ((completedPthRootApproxSeq (p := p) (K := K) hu n).val :
              completedLocalCyclotomicRing p K) -
            ((completedPthRootApproxSeq (p := p) (K := K) hu (n + 1)).val :
              completedLocalCyclotomicRing p K) ∈
            completedLocalCyclotomicMaximalIdeal p K ^ m := by
          have hneg : -(((completedPthRootApproxSeq (p := p) (K := K) hu (n + 1)).val :
              completedLocalCyclotomicRing p K) -
            ((completedPthRootApproxSeq (p := p) (K := K) hu n).val :
              completedLocalCyclotomicRing p K)) ∈
            completedLocalCyclotomicMaximalIdeal p K ^ m :=
            Ideal.pow_le_pow_right (by omega : m ≤ n + 2)
              ((completedLocalCyclotomicMaximalIdeal p K ^ (n + 2)).neg_mem hadj)
          convert hneg using 1
          ring
        exact (mem_ideal_smul_top_iff_self
          (I := completedLocalCyclotomicMaximalIdeal p K ^ m)).mpr hmem
      · have hm : m = n + 1 := by omega
        subst hm
        exact SModEq.rfl

end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular
