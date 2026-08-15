module

public import FltRegular.NumberTheory.RegularPrimes
import KummerCriterion.BernoulliFast.ValuesUpTo100
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.Bernoulli
import KummerCriterion.CyclotomicUnits.UnitsReflection

/-!
# Kummer's criterion

This file exposes the final public theorem of the project.
-/

@[expose] public section

open NumberField

namespace KummerCriterion

/-- **Kummer's criterion.**

An odd prime `p` is regular iff `p` does not divide the numerator of any
Bernoulli number `B_2, B_4,..., B_{p-3}`. -/
theorem _root_.KummerCriterion
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2) :
    IsRegularPrime p ↔
      ∀ k, 1 ≤ k → 2 * k ≤ p - 3 → ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  have : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have : IsCMField (CyclotomicField p ℚ) :=
    isCMField_of_cyclotomic (p := p) (hp_odd := hp_odd) (K := CyclotomicField p ℚ)
  have hiff : (p : ℕ) ∣ h (CyclotomicField p ℚ) ↔
      ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num :=
    dvd_h_iff_exists_dvd_bernoulli_units
      (p := p) (K := CyclotomicField p ℚ) hp_odd
  rw [IsRegularPrime, IsRegularNumber, hp.out.coprime_iff_not_dvd]
  change ¬ (p : ℕ) ∣ h (CyclotomicField p ℚ) ↔ _
  rw [hiff]
  push Not
  rfl

end KummerCriterion

/-!
# Regularity of primes below 100

This file records the regularity status of each prime below `100`.

Regular primes below `100`:
`2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 43, 47, 53, 61, 71, 73, 79,
83, 89, 97`.

Irregular primes below `100`:
`37, 59, 67`.

The computational Bernoulli steps are discharged by `norm_num` using the
`@[simp]` values from `KummerCriterion.BernoulliFast.ValuesUpTo100`.
-/

@[expose] public section

namespace KummerCriterion

private theorem regular_of_bernoulli_values
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hB : ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
      ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num) :
    IsRegularPrime p :=
  (KummerCriterion (p := p) hp_odd).mpr hB

theorem isRegularPrime_three_lt100 :
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    IsRegularPrime 3 :=
  isRegularPrime_three

theorem isRegularPrime_five_lt100 :
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    IsRegularPrime 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 5) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 1 := by omega
    (interval_cases k; norm_num))

theorem isRegularPrime_seven_lt100 :
    letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    IsRegularPrime 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 7) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 2 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_eleven_lt100 :
    letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    IsRegularPrime 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 11) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 4 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_thirteen_lt100 :
    letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    IsRegularPrime 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 13) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 5 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_seventeen_lt100 :
    letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    IsRegularPrime 17 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 17) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 7 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_nineteen_lt100 :
    letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    IsRegularPrime 19 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 19) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 8 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_twentythree_lt100 :
    letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    IsRegularPrime 23 := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 23) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 10 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_twentynine_lt100 :
    letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
    IsRegularPrime 29 := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 29) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 13 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_thirtyone_lt100 :
    letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    IsRegularPrime 31 := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 31) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 14 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_fortyone_lt100 :
    letI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    IsRegularPrime 41 := by
  have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 41) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 19 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_fortythree_lt100 :
    letI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    IsRegularPrime 43 := by
  have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 43) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 20 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_fortyseven_lt100 :
    letI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
    IsRegularPrime 47 := by
  have : Fact (Nat.Prime 47) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 47) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 22 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_fiftythree_lt100 :
    letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    IsRegularPrime 53 := by
  have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 53) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 25 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_sixtyone_lt100 :
    letI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
    IsRegularPrime 61 := by
  have : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 61) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 29 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_seventyone_lt100 :
    letI : Fact (Nat.Prime 71) := ⟨by norm_num⟩
    IsRegularPrime 71 := by
  have : Fact (Nat.Prime 71) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 71) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 34 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_seventythree_lt100 :
    letI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
    IsRegularPrime 73 := by
  have : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 73) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 35 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_seventynine_lt100 :
    letI : Fact (Nat.Prime 79) := ⟨by norm_num⟩
    IsRegularPrime 79 := by
  have : Fact (Nat.Prime 79) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 79) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 38 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_eightythree_lt100 :
    letI : Fact (Nat.Prime 83) := ⟨by norm_num⟩
    IsRegularPrime 83 := by
  have : Fact (Nat.Prime 83) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 83) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 40 := by   omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_eightynine_lt100 :
    let : Fact (Nat.Prime 89) := ⟨by norm_num⟩
    IsRegularPrime 89 := by
  have : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 89) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 43 := by omega
    interval_cases k <;> norm_num)

theorem isRegularPrime_ninetyseven_lt100 :
    letI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
    IsRegularPrime 97 := by
  have : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact regular_of_bernoulli_values (p := 97) (by norm_num) (by
    intro k hk hk_range
    have hk_upper : k ≤ 47 := by omega
    interval_cases k <;> norm_num)

end KummerCriterion
