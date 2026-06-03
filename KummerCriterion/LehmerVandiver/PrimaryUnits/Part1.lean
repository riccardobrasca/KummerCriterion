module

public import KummerCriterion.LehmerVandiver.PrimaryConj
public import KummerCriterion.TotallyRealSubfield.ZetaPrime
public import KummerCriterion.HMinus.KplusPrimeArithmetic
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import FltRegular.NumberTheory.Cyclotomic.MoreLemmas

/-!
# Primary units of `𝓞 K⁺`

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

namespace KummerCriterion

namespace LehmerVandiver

section PrimaryPlus

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-! ## Cyclotomic units `(1 - ζ^k)/(1 - ζ)` in `𝓞 K`

For `k` coprime to `p` (so `1 ≤ k ≤ p-1`), the element
`(1 - ζ^k)/(1 - ζ)` is a unit in `𝓞 K`. These are the building blocks
for Pollaczek's primary units in K⁺. -/

section CyclotomicUnits

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The cyclotomic unit `(1 - ζ^k)/(1 - ζ) ∈ 𝓞 K` for `k` coprime to
`p`. Equivalently `1 + ζ + ζ^2 + ... + ζ^{k-1}`. -/
noncomputable def cyclotomicUnit (k : ℕ) : 𝓞 K :=
  ∑ j ∈ Finset.range k, (zeta_spec p ℚ K).unit' ^ j

/-- Recursive identity: `cyclotomicUnit (k+1) = cyclotomicUnit k + ζ^k`. -/
theorem cyclotomicUnit_succ (k : ℕ) :
    cyclotomicUnit p K (k + 1) =
      cyclotomicUnit p K k + ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k := by
  unfold cyclotomicUnit
  rw [Finset.sum_range_succ]

/-- The cyclotomic-unit telescoping identity:
`(1 - ζ) · cyclotomicUnit k = 1 - ζ^k` in `𝓞 K`. -/
theorem one_sub_zeta_mul_cyclotomicUnit (k : ℕ) :
    (1 - (zeta_spec p ℚ K).unit') * cyclotomicUnit p K k =
      1 - ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k := by
  unfold cyclotomicUnit
  rw [Finset.mul_sum]
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Reversed sign form: `(ζ - 1) · cyclotomicUnit k = ζ^k - 1`. -/
theorem zeta_sub_one_mul_cyclotomicUnit (k : ℕ) :
    (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) * cyclotomicUnit p K k =
      ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k - 1 := by
  have h := one_sub_zeta_mul_cyclotomicUnit p K k
  linear_combination -h

/-- **Conjugation unit value: `u = -ζ^{p-1}` in `𝓞 K`.** -/
private theorem zetaSubOneConjUnit_val_eq [IsCMField K] :
    ((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) =
      -((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - 1) := by
  unfold zetaSubOneConjUnit
  push_cast
  ring

/-- `cyclotomicUnit k ≡ k (mod ζ - 1)` in `𝓞 K`: the difference
`cyclotomicUnit k - k` is divisible by `ζ - 1`. -/
theorem zetaSubOne_dvd_cyclotomicUnit_sub_natCast (k : ℕ) :
    ((zeta_spec p ℚ K).unit' : 𝓞 K) - 1 ∣
      cyclotomicUnit p K k - (k : 𝓞 K) := by
  unfold cyclotomicUnit
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hcast : ((n + 1 : ℕ) : 𝓞 K) = (n : 𝓞 K) + 1 := by push_cast; rfl
    rw [hcast]
    have hsplit : ∑ j ∈ Finset.range n, ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ j +
        ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ n - ((n : 𝓞 K) + 1) =
        (∑ j ∈ Finset.range n, ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ j - (n : 𝓞 K)) +
        (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ n - 1) := by ring
    rw [hsplit]
    refine dvd_add ih ?_
    -- ζ - 1 ∣ ζ^n - 1
    have htel : (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) *
        cyclotomicUnit p K n =
        ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ n - 1 := by
      have h := one_sub_zeta_mul_cyclotomicUnit p K n
      linear_combination -h
    exact ⟨cyclotomicUnit p K n, htel.symm⟩

/-- The complex conjugate of `cyclotomicUnit k` is also congruent to `k`
modulo `ζ - 1`. -/
theorem zetaSubOne_dvd_complexConj_cyclotomicUnit_sub_natCast [IsCMField K]
    (k : ℕ) :
    ((zeta_spec p ℚ K).unit' : 𝓞 K) - 1 ∣
      ringOfIntegersComplexConj K (cyclotomicUnit p K k) - (k : 𝓞 K) := by
  have h := zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k
  have h_apply :
      ringOfIntegersComplexConj K (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) ∣
      ringOfIntegersComplexConj K (cyclotomicUnit p K k - (k : 𝓞 K)) :=
    map_dvd (ringOfIntegersComplexConj K).toRingEquiv.toRingHom h
  rw [map_sub, map_sub (a := cyclotomicUnit p K k), map_one,
    map_natCast] at h_apply
  -- σ(ζ - 1) is associated to ζ - 1
  have hassoc :
      Associated (ringOfIntegersComplexConj K (((zeta_spec p ℚ K).unit' : 𝓞 K)) - 1)
        (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) := by
    have h_orig := associated_complexConj_zetaSubOne p K
    change Associated (ringOfIntegersComplexConj K (((zeta_spec p ℚ K).unit' : 𝓞 K)) - 1)
        (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1)
    have h_eq : ringOfIntegersComplexConj K (((zeta_spec p ℚ K).unit' : 𝓞 K)) - 1 =
        ringOfIntegersComplexConj K (zetaSubOne p K) := by
      rw [show (zetaSubOne p K : 𝓞 K) = ((zeta_spec p ℚ K).unit' : 𝓞 K) - 1 from rfl,
        map_sub, map_one]
    rw [h_eq]
    exact h_orig.symm
  exact hassoc.symm.dvd.trans h_apply

/-- The cyclotomic unit `(1 - ζ^k)/(1 - ζ)` is a unit in `𝓞 K` when
`k` is coprime to `p`. Proven via mathlib's `geom_sum_isUnit`. -/
theorem isUnit_cyclotomicUnit (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (cyclotomicUnit p K k) := by
  unfold cyclotomicUnit
  exact (zeta_spec p ℚ K).unit'_coe.geom_sum_isUnit hp_two hk

/-- The cyclotomic unit packaged as `(𝓞 K)ˣ` when `k` is coprime to `p`. -/
noncomputable def cyclotomicUnitUnit (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (𝓞 K)ˣ :=
  (isUnit_cyclotomicUnit p K k hk hp_two).unit

@[simp]
theorem cyclotomicUnitUnit_val (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (cyclotomicUnitUnit p K k hk hp_two : 𝓞 K) = cyclotomicUnit p K k :=
  IsUnit.unit_spec _

/-- `(ζ - 1) ∣ (ζ^k - 1)` in `𝓞 K` for any natural `k`. -/
theorem zetaSubOne_dvd_zeta_pow_sub_one (k : ℕ) :
    (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) ∣
      (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k - 1) :=
  ⟨cyclotomicUnit p K k, (zeta_sub_one_mul_cyclotomicUnit p K k).symm⟩

end CyclotomicUnits
end PrimaryPlus
end LehmerVandiver

end KummerCriterion

end
