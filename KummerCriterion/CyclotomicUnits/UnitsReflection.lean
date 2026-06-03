module

public import KummerCriterion.CyclotomicUnits.Saturation
public import KummerCriterion.TotallyRealSubfield.ClassGroup
public import Mathlib.NumberTheory.Bernoulli
import KummerCriterion.CyclotomicUnits.KummerLogDeterminant
import KummerCriterion.CyclotomicUnits.LogDomain
import KummerCriterion.CyclotomicUnits.NormalizedIndex
import KummerCriterion.CyclotomicUnits.SaturationIndex
import KummerCriterion.HMinus.HMinusCriterion
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-!
# Class-number algebra for the cyclotomic-unit route

This file isolates the class-number step needed to plug a cyclotomic-unit proof
of `p ∣ h⁺ → p ∣ h⁻` into Kummer's criterion.
-/

@[expose] public section

noncomputable section

open NumberField

namespace KummerCriterion

/-- A cyclotomic-unit implication `p ∣ hPlus K → p ∣ hMinus K` identifies
total and relative class-number divisibility. -/
theorem dvd_h_iff_dvd_hMinus_of_dvd_hPlus_imp
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K]
    (hplus_to_hminus : (p : ℕ) ∣ hPlus K → (p : ℕ) ∣ hMinus K) :
    (p : ℕ) ∣ h K ↔ (p : ℕ) ∣ hMinus K := by
  constructor
  · intro hpH
    rw [h_eq_hPlus_mul_hMinus p hp_odd K] at hpH
    rcases hp.out.dvd_mul.mp hpH with hplus | hminus
    · exact hplus_to_hminus hplus
    · exact hminus
  · intro hminus
    rw [h_eq_hPlus_mul_hMinus p hp_odd K]
    exact dvd_mul_of_dvd_right hminus (hPlus K)

end KummerCriterion

end

/-!
# Minus class-number criterion for the cyclotomic-unit route

This file records the `h⁻`/Bernoulli-numerator API in the direction used by the
cyclotomic-unit proof of weak reflection.
-/

@[expose] public section

noncomputable section

open NumberField

namespace KummerCriterion

/-- Contrapositive form of `p_dvd_hMinus_iff_p_dvd_some_bernoulli`. -/
theorem bernoulli_nonzero_of_not_dvd_hMinus
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K] (hp_odd : p ≠ 2)
    (hminus : ¬ (p : ℕ) ∣ hMinus K) :
    ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
      ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num := fun k hk hk_range hnum =>
  hminus <|
    (p_dvd_hMinus_iff_p_dvd_some_bernoulli (p := p) (K := K) hp_odd).2
      ⟨k, hk, hk_range, hnum⟩

end KummerCriterion

end

/-!
# Cyclotomic-unit route to weak reflection

This file assembles the cyclotomic-unit route from Bernoulli nonvanishing to
weak reflection.
-/

@[expose] public section

noncomputable section

open NumberField

namespace KummerCriterion

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Bernoulli numerator nonvanishing in the classical range implies
that `p` does not divide the real cyclotomic-unit index. -/
theorem not_dvd_cyclotomicUnitIndex_of_bernoulli_nonzero
    (hp_odd : p ≠ 2)
    (hB : ∀ j : ℕ, 1 ≤ j → 2 * j ≤ p - 3 →
      ¬ (p : ℤ) ∣ (_root_.bernoulli (2 * j)).num) :
    ¬ p ∣ (CPlus (p := p) (K := K)
      (by have hp_two := (Fact.out : Nat.Prime p).two_le; omega)).index := by
  classical
  have hp_three : 3 ≤ p := by
    have hp_two := (Fact.out : Nat.Prime p).two_le
    omega
  by_cases hp_eq_three : p = 3
  · have hindex :
        (CPlus (p := p) (K := K) hp_three).index = 1 := by
      rw [CPlus_eq_top_of_eq_three (p := p) (K := K) hp_three hp_eq_three]
      exact Subgroup.index_top
    rw [show
      (CPlus (p := p) (K := K)
        (by have hp_two := (Fact.out : Nat.Prime p).two_le; omega)).index =
          (CPlus (p := p) (K := K) hp_three).index by rfl]
    rw [hindex]
    intro hdiv
    exact (Fact.out : Nat.Prime p).ne_one (Nat.dvd_one.mp hdiv)
  · have hp_five : 5 ≤ p := by
      obtain ⟨k, hk⟩ := (Fact.out : Nat.Prime p).odd_of_ne_two hp_odd
      have hp_two := (Fact.out : Nat.Prime p).two_le
      omega
    have hdet :
        (CyclotomicUnits.concreteKummerLogMatrix
          (p := p) (K := K) hp_three hp_five).det ≠ 0 :=
      (CyclotomicUnits.kummerLogMatrix_det_ne_zero_iff_bernoulli_nonzero
        (p := p) (K := K) hp_three hp_five).mpr hB
    have hsat :
        pSaturated (CPlus (p := p) (K := K) hp_three) (EPlus (K := K)) p :=
      CyclotomicUnits.cyclotomicUnits_pSaturated_of_kummerLog_det_ne_zero
        (p := p) (K := K) hp_three hp_five hdet
    have hnot := not_dvd_index_of_pSaturated (p := p) (K := K) hp_three hsat
    rwa [show
      (CPlus (p := p) (K := K)
        (by have hp_two := (Fact.out : Nat.Prime p).two_le; omega)).index =
          (CPlus (p := p) (K := K) hp_three).index by rfl]

/-- Contrapositive weak reflection from the cyclotomic-unit route. -/
theorem not_dvd_hPlus_of_not_dvd_hMinus_units
    (hp_odd : p ≠ 2) (hminus : ¬ (p : ℕ) ∣ hMinus K) :
    ¬ (p : ℕ) ∣ hPlus K := by
  classical
  have hp_three : 3 ≤ p := by
    have hp_two := (Fact.out : Nat.Prime p).two_le
    omega
  have hB :
      ∀ j : ℕ, 1 ≤ j → 2 * j ≤ p - 3 →
        ¬ (p : ℤ) ∣ (_root_.bernoulli (2 * j)).num :=
    bernoulli_nonzero_of_not_dvd_hMinus
      (p := p) (K := K) hp_odd hminus
  have hindex :
      ¬ p ∣ (CPlus (p := p) (K := K) hp_three).index := by
    simpa using
      not_dvd_cyclotomicUnitIndex_of_bernoulli_nonzero
        (p := p) (K := K) hp_odd hB
  intro hplus
  have hnormalized :
      p ∣ (normalizedCPlus (p := p) (K := K) hp_odd hp_three).index :=
    (cyclotomicUnitIndex_primeConductor_pPrimary
      (p := p) (K := K) hp_odd).mpr hplus
  have hCPlus :
      p ∣ (CPlus (p := p) (K := K) hp_three).index :=
    (CPlus_index_prime_dvd_iff_normalizedCPlus_index_prime_dvd
      (p := p) (K := K) hp_odd hp_three).mpr hnormalized
  exact hindex hCPlus

/-- Weak reflection by contrapositive from the cyclotomic-unit route. -/
theorem weakReflection_dvd_hMinus_of_dvd_hPlus_units
    (hp_odd : p ≠ 2) (hplus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ hMinus K := by
  classical
  by_contra hminus
  exact not_dvd_hPlus_of_not_dvd_hMinus_units
    (p := p) (K := K) hp_odd hminus hplus

/-- The total class-number divisibility criterion obtained from the
cyclotomic-unit weak-reflection route. -/
theorem dvd_h_iff_exists_dvd_bernoulli_units
    (hp_odd : p ≠ 2) :
    (p : ℕ) ∣ h K ↔
      ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  rw [dvd_h_iff_dvd_hMinus_of_dvd_hPlus_imp hp_odd
      (weakReflection_dvd_hMinus_of_dvd_hPlus_units (p := p) (K := K) hp_odd),
    p_dvd_hMinus_iff_p_dvd_some_bernoulli (p := p) (K := K) hp_odd]

end KummerCriterion

end
