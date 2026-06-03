module

public import KummerCriterion.LehmerVandiver.PrimaryUnits.Part3
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Real cyclotomic units

This file gives the standard real cyclotomic units in `K⁺` a route-level name.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace KummerCriterion

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Indices `2 ≤ a ≤ (p - 1) / 2` are automatically coprime to the prime
conductor `p`. -/
theorem realCyclotomicUnit_index_coprime {a : ℕ}
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) : a.Coprime p := by
  have hp_prime : Nat.Prime p := Fact.out
  have ha_pos : 0 < a := by omega
  have ha_lt : a < p := by
    have hhalf : (p - 1) / 2 < p := by omega
    omega
  have hnot : ¬ p ∣ a := fun hpa => by
    exact (not_le_of_gt ha_lt) (Nat.le_of_dvd ha_pos hpa)
  exact (hp_prime.coprime_iff_not_dvd.mpr hnot).symm

/-- The real cyclotomic unit in `𝓞 K⁺` attached to `2 ≤ a ≤ (p - 1) / 2`. -/
noncomputable def realCyclotomicUnit (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) : (𝓞 K⁺)ˣ :=
  LehmerVandiver.realCyclotomicUnitPlusUnit p K a
    (realCyclotomicUnit_index_coprime (p := p) ha_two ha_le)
    (Fact.out : Nat.Prime p).two_le

@[simp]
theorem realCyclotomicUnit_val (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    (realCyclotomicUnit (p := p) (K := K) a ha_two ha_le : 𝓞 K⁺) =
      LehmerVandiver.realCyclotomicUnitPlus p K a := by
  unfold realCyclotomicUnit
  rw [LehmerVandiver.realCyclotomicUnitPlusUnit_val]

/-- The image of the real cyclotomic unit in `𝓞 K` is the σ-fixed product
`cyclotomicUnit a * σ(cyclotomicUnit a)`. -/
theorem algebraMap_realCyclotomicUnit (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    algebraMap (𝓞 K⁺) (𝓞 K)
        (realCyclotomicUnit (p := p) (K := K) a ha_two ha_le : 𝓞 K⁺) =
      LehmerVandiver.realCyclotomicUnit p K a := by
  rw [realCyclotomicUnit_val, LehmerVandiver.algebraMap_realCyclotomicUnitPlus]

end KummerCriterion

end
