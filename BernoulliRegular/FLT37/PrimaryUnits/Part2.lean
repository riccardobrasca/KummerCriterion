module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.TotallyRealSubfield.ZetaPrime
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import FltRegular.NumberTheory.Cyclotomic.MoreLemmas
public import BernoulliRegular.FLT37.PrimaryUnits.Part1

/-!
# Primary units of `𝓞 K⁺` (ticket FLT37c, scaffold)

For Vandiver Lemma 2 (primary unit decomposition), an element
`γ ∈ 𝓞 K⁺` is **primary** when it is congruent to a rational integer
modulo `𝔭⁺^p`, where `𝔭⁺` is the unique prime of `𝓞 K⁺` above `(p)`.
Equivalently (since `𝔭⁺·𝓞 K = 𝔭² = (ζ-1)^2`), this is
`γ ≡ a (mod (ζ-1)^{2p})` viewed in `𝓞 K`.

This file isolates the K⁺-side primary definition with basic API.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.4.
* Vandiver 1929, *Fermat's Last Theorem and the Second Factor in the
  Cyclotomic Class Number*.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

section PrimaryPlus

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

section CyclotomicUnits

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]














/-- The K-level multiplicative identity `(ζ - 1) · cyclotomicUnit = ζ^k - 1`
in K, lifted from the 𝓞 K version. -/
theorem zeta_sub_one_mul_cyclotomicUnit_in_K (k : ℕ) :
    (IsCyclotomicExtension.zeta p ℚ K - 1) *
        algebraMap (𝓞 K) K (cyclotomicUnit p K k) =
      IsCyclotomicExtension.zeta p ℚ K ^ k - 1 := by
  have h := zeta_sub_one_mul_cyclotomicUnit p K k
  have := congrArg (algebraMap (𝓞 K) K) h
  rw [map_mul, map_sub, map_sub, map_pow, map_one] at this
  convert this using 2

/-- **Norm of the cyclotomic unit.** For `k` coprime to `p` (odd prime),
`Algebra.norm ℚ (cyclotomicUnit p K k) = 1`. -/
theorem cyclotomicUnit_norm_rat (k : ℕ) (hk : k.Coprime p) (hp_odd : p ≠ 2) :
    Algebra.norm ℚ (algebraMap (𝓞 K) K (cyclotomicUnit p K k)) = (1 : ℚ) := by
  have h_K := zeta_sub_one_mul_cyclotomicUnit_in_K p K k
  have hp_pos : 0 < (p : ℚ) := by exact_mod_cast hp.1.pos
  have h_norm := congrArg (Algebra.norm ℚ : K → ℚ) h_K
  rw [map_mul, FLT37.zeta_pow_sub_one_norm_rat p K hp_odd k hk] at h_norm
  -- LHS: norm(ζ - 1) · norm(cyclotomicUnit) = p · norm(cyclotomicUnit)
  have h_zeta := FLT37.zetaSubOne_norm_rat p K hp_odd
  rw [FLT37.algebraMap_zetaSubOne] at h_zeta
  rw [h_zeta] at h_norm
  -- h_norm : p * norm(...) = p
  exact mul_left_cancel₀ hp_pos.ne' (h_norm.trans (mul_one _).symm)

/-- **Integer norm of the cyclotomic unit.** For `k` coprime to `p` (odd
prime), `Algebra.norm ℤ (cyclotomicUnit p K k) = 1`. -/
theorem cyclotomicUnit_norm_int (k : ℕ) (hk : k.Coprime p) (hp_odd : p ≠ 2) :
    Algebra.norm ℤ (cyclotomicUnit p K k) = (1 : ℤ) := by
  have h_rat := cyclotomicUnit_norm_rat p K k hk hp_odd
  have h_coe : ((Algebra.norm ℤ (cyclotomicUnit p K k) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap (𝓞 K) K (cyclotomicUnit p K k)) :=
    Algebra.coe_norm_int _
  rw [h_rat] at h_coe
  exact_mod_cast h_coe

/-- `cyclotomicUnit p K p = 0`, since `∑_{j=0}^{p-1} ζ^j = 0`
(cyclotomic identity). -/
theorem cyclotomicUnit_p_eq_zero : cyclotomicUnit p K p = 0 :=
  (zeta_spec p ℚ K).unit'_coe.geom_sum_eq_zero
    (Nat.lt_of_lt_of_le one_lt_two hp.1.two_le)















/-- `cyclotomicUnit p K (p - 1) = -ζ^{p-1}`. From the cyclotomic
identity `∑_{j=0}^{p-1} ζ^j = 0`, we have
`∑_{j=0}^{p-2} ζ^j = -ζ^{p-1}`. -/
theorem cyclotomicUnit_p_sub_one :
    cyclotomicUnit p K (p - 1) = -((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - 1) := by
  have hp_pos : 1 ≤ p := hp.1.pos
  have hp_eq : (p - 1) + 1 = p := Nat.sub_add_cancel hp_pos
  have key : cyclotomicUnit p K (p - 1) +
      ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - 1) = 0 := by
    have hrec := cyclotomicUnit_succ p K (p - 1)
    rw [hp_eq] at hrec
    rw [← hrec, cyclotomicUnit_p_eq_zero]
  linear_combination key


end CyclotomicUnits

/-! ## Real cyclotomic units `(1 - ζ^k)(1 - ζ^{-k})/((1 - ζ)(1 - ζ^{-1}))`

These are `σ`-fixed in `𝓞 K` and hence descend to elements of `𝓞 K⁺`.
They are the building blocks for Pollaczek's primary unit decomposition. -/

section RealCyclotomicUnits

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The real cyclotomic combination
`(cyclotomicUnit k) · σ(cyclotomicUnit k)` in `𝓞 K`. This is
automatically `σ`-fixed and corresponds to the K⁺-side cyclotomic
unit `(1 - ζ^k)(1 - ζ^{-k})/((1 - ζ)(1 - ζ^{-1}))`. -/
noncomputable def realCyclotomicUnit [IsCMField K] (k : ℕ) : 𝓞 K :=
  cyclotomicUnit p K k * ringOfIntegersComplexConj K (cyclotomicUnit p K k)













/-- The real cyclotomic combination is fixed by complex conjugation. -/
theorem realCyclotomicUnit_complexConj [IsCMField K] (k : ℕ) :
    ringOfIntegersComplexConj K (realCyclotomicUnit p K k) =
      realCyclotomicUnit p K k := by
  unfold realCyclotomicUnit
  rw [map_mul]
  rw [show ringOfIntegersComplexConj K
        (ringOfIntegersComplexConj K (cyclotomicUnit p K k)) =
      cyclotomicUnit p K k from by
    apply RingOfIntegers.ext
    simp]
  ring



/-- **Integer norm of the real cyclotomic combination.** For `k` coprime
to `p` (odd prime), `Algebra.norm ℤ (realCyclotomicUnit p K k) = 1`. -/
theorem realCyclotomicUnit_norm_int [IsCMField K] (k : ℕ) (hk : k.Coprime p)
    (hp_odd : p ≠ 2) :
    Algebra.norm ℤ (realCyclotomicUnit p K k) = (1 : ℤ) := by
  -- realCyclotomicUnit = cyclotomicUnit · σ(cyclotomicUnit)
  -- norm(σ x) = norm(x), so norm(realCyclotomicUnit) = norm(cyclotomicUnit)^2 = 1
  unfold realCyclotomicUnit
  rw [map_mul]
  have h_conj : Algebra.norm ℤ (ringOfIntegersComplexConj K (cyclotomicUnit p K k)) =
      Algebra.norm ℤ (cyclotomicUnit p K k) := by
    apply (algebraMap ℤ ℚ).injective_int
    have h1 := Algebra.coe_norm_int (ringOfIntegersComplexConj K (cyclotomicUnit p K k))
    have h2 := Algebra.coe_norm_int (cyclotomicUnit p K k)
    -- transit through ℚ-norm
    have h_q : Algebra.norm ℚ (algebraMap (𝓞 K) K
        (ringOfIntegersComplexConj K (cyclotomicUnit p K k))) =
        Algebra.norm ℚ (algebraMap (𝓞 K) K (cyclotomicUnit p K k)) := by
      have h_eq : algebraMap (𝓞 K) K
          (ringOfIntegersComplexConj K (cyclotomicUnit p K k)) =
          BernoulliRegular.complexConjRat (p := p) (K := K) hp_odd
            (algebraMap (𝓞 K) K (cyclotomicUnit p K k)) := by
        change ((ringOfIntegersComplexConj K (cyclotomicUnit p K k) : 𝓞 K) : K) =
          BernoulliRegular.complexConjRat (p := p) (K := K) hp_odd
            ((cyclotomicUnit p K k : 𝓞 K) : K)
        rw [coe_ringOfIntegersComplexConj]
        rfl
      rw [h_eq]
      exact Algebra.norm_eq_of_algEquiv
        (BernoulliRegular.complexConjRat (p := p) (K := K) hp_odd) _
    change ((algebraMap ℤ ℚ) (Algebra.norm ℤ _) : ℚ) =
      ((algebraMap ℤ ℚ) (Algebra.norm ℤ _))
    rw [show (algebraMap ℤ ℚ) (Algebra.norm ℤ
      (ringOfIntegersComplexConj K (cyclotomicUnit p K k))) =
      ((Algebra.norm ℤ (ringOfIntegersComplexConj K (cyclotomicUnit p K k)) : ℤ) : ℚ) from rfl,
      show (algebraMap ℤ ℚ) (Algebra.norm ℤ (cyclotomicUnit p K k)) =
        ((Algebra.norm ℤ (cyclotomicUnit p K k) : ℤ) : ℚ) from rfl, h1, h2]
    exact h_q
  rw [h_conj, ← sq]
  rw [cyclotomicUnit_norm_int p K k hk hp_odd]
  ring




/-- `realCyclotomicUnit k ≡ k² (mod ζ - 1)` in `𝓞 K`. -/
theorem zetaSubOne_dvd_realCyclotomicUnit_sub_sq [IsCMField K] (k : ℕ) :
    ((zeta_spec p ℚ K).unit' : 𝓞 K) - 1 ∣
      realCyclotomicUnit p K k - (k : 𝓞 K) ^ 2 := by
  -- Combine cyclotomicUnit ≡ k and σ(cyclotomicUnit) ≡ k modulo ζ - 1
  have h_diff : realCyclotomicUnit p K k - (k : 𝓞 K) ^ 2 =
      cyclotomicUnit p K k *
        (ringOfIntegersComplexConj K (cyclotomicUnit p K k) - (k : 𝓞 K)) +
      (k : 𝓞 K) * (cyclotomicUnit p K k - (k : 𝓞 K)) := by
    change cyclotomicUnit p K k * ringOfIntegersComplexConj K (cyclotomicUnit p K k)
        - (k : 𝓞 K) ^ 2 = _
    ring
  rw [h_diff]
  exact dvd_add
    ((zetaSubOne_dvd_complexConj_cyclotomicUnit_sub_natCast p K k).mul_left _)
    ((zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k).mul_left _)





/-- The real cyclotomic combination is a unit when `k` is coprime to `p`. -/
theorem isUnit_realCyclotomicUnit [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnit p K k) := by
  unfold realCyclotomicUnit
  exact (isUnit_cyclotomicUnit p K k hk hp_two).mul
    ((isUnit_cyclotomicUnit p K k hk hp_two).map
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)



end RealCyclotomicUnits
end PrimaryPlus
end FLT37

end BernoulliRegular

end
