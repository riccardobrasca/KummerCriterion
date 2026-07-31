module

public import KummerCriterion.BernoulliFast.PrimesUpTo100
public import Mathlib.Data.Set.Finite.Basic
import KummerCriterion.BernoulliFast.ValuesUpTo100
import Mathlib.Tactic

/-!
# Basic infrastructure for non-regular primes

This file contains the elementary bridge from Bernoulli numerator witnesses to
the existing `IsRegularPrime` predicate, plus finite-set scaffolding for the
infinitude argument.
-/

@[expose] public section

namespace KummerCriterion

/-- A Bernoulli numerator witness in Kummer's range proves that `p` is not
regular. -/
theorem not_isRegularPrime_of_bernoulli_num_dvd
    {p : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2)
    (h : ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧
      (p : ℤ) ∣ (bernoulli (2 * k)).num) :
    letI : Fact p.Prime := ⟨hp⟩
    ¬ IsRegularPrime p := by
  have : Fact p.Prime := ⟨hp⟩
  intro hreg
  rcases h with ⟨k, hk_pos, hk_range, hdiv⟩
  exact ((KummerCriterion (p := p) hp_odd).mp hreg k hk_pos hk_range) hdiv

/-- Conversely, non-regularity gives a Bernoulli numerator witness in Kummer's
range. -/
theorem exists_bernoulli_num_dvd_of_not_isRegularPrime
    {p : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2)
    (hirr : letI : Fact p.Prime := ⟨hp⟩; ¬ IsRegularPrime p) :
    ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧
      (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra h
  exact hirr <| (KummerCriterion (p := p) hp_odd).mpr <| by
    intro k hk_pos hk_range hdiv
    exact h ⟨k, hk_pos, hk_range, hdiv⟩

/-- To prove a predicate infinite, it is enough to show that no finite set
covers it. -/
theorem infinite_of_forall_finite_set_not_cover
    {P : ℕ → Prop}
    (h : ∀ S : Finset ℕ, (∀ p, P p → p ∈ S) → False) :
    Set.Infinite {p : ℕ | P p} := by
  intro hfinite
  exact h hfinite.toFinset fun p hp => hfinite.mem_toFinset.mpr hp

end KummerCriterion
