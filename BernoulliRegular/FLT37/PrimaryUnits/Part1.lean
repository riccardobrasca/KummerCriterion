module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.TotallyRealSubfield.ZetaPrime
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import FltRegular.NumberTheory.Cyclotomic.MoreLemmas

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

/-- An element `γ ∈ 𝓞 K⁺` is **primary** when it is congruent to a
rational integer modulo `𝔭⁺^p`. -/
def IsPrimaryPlus [IsCMField K] (γ : 𝓞 (K⁺)) : Prop :=
  ∃ a : ℤ, γ - (a : 𝓞 (K⁺)) ∈ zetaPrimePlus p K ^ p

namespace IsPrimaryPlus

variable {p K}





/-- The negation of a K⁺-primary element is K⁺-primary. -/
theorem neg [IsCMField K] {γ : 𝓞 (K⁺)} (hγ : IsPrimaryPlus p K γ) :
    IsPrimaryPlus p K (-γ) := by
  obtain ⟨a, ha⟩ := hγ
  refine ⟨-a, ?_⟩
  have : -γ - ((-a : ℤ) : 𝓞 (K⁺)) = -(γ - (a : 𝓞 (K⁺))) := by push_cast; ring
  rw [this]
  exact (zetaPrimePlus p K ^ p).neg_mem ha

/-- `IsPrimaryPlus` is preserved by `Neg.neg` in both directions. -/
@[simp]
theorem neg_iff [IsCMField K] {γ : 𝓞 (K⁺)} :
    IsPrimaryPlus p K (-γ) ↔ IsPrimaryPlus p K γ :=
  ⟨fun h => by simpa using h.neg, fun h => h.neg⟩







end IsPrimaryPlus



namespace IsPrimaryUnit

variable {p K}







end IsPrimaryUnit





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

/-- For `k` coprime to `p`, `(ζ - 1)` is associated to `(ζ^k - 1)` in `𝓞 K`,
with witness `cyclotomicUnitUnit k` (since `(ζ - 1) · cyclotomicUnit k = ζ^k - 1`). -/
theorem associated_zeta_sub_one_zeta_pow_sub_one (k : ℕ) (hk : k.Coprime p)
    (hp_two : 2 ≤ p) :
    Associated (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1)
      (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k - 1) :=
  ⟨cyclotomicUnitUnit p K k hk hp_two, by
    rw [cyclotomicUnitUnit_val]
    exact zeta_sub_one_mul_cyclotomicUnit p K k⟩



/-- `(ζ - 1) ∣ (ζ^k - 1)` in `𝓞 K` for any natural `k`. -/
theorem zetaSubOne_dvd_zeta_pow_sub_one (k : ℕ) :
    (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) ∣
      (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k - 1) :=
  ⟨cyclotomicUnit p K k, (zeta_sub_one_mul_cyclotomicUnit p K k).symm⟩

/-- For integers `a, b` and any natural `k`, `(ζ - 1) ∣ (a + ζ^k · b - (a + b))`
in `𝓞 K`. The key residue-modulo-(ζ-1) computation for FLT case I. -/
theorem zetaSubOne_dvd_factor_sub_sum (a b : ℤ) (k : ℕ) :
    (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((a + b : ℤ) : 𝓞 K)) := by
  have h := zetaSubOne_dvd_zeta_pow_sub_one p K k
  have heq :
      ((a : 𝓞 K) + ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((a + b : ℤ) : 𝓞 K) =
      (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k - 1) * (b : 𝓞 K) := by
    push_cast
    ring
  rw [heq]
  exact h.mul_right _


/-- **`(ζ - 1)^{p-1} ∣ p` in `𝓞 K`.** Cyclotomic ramification: `(p)·𝓞 K`
factors with `zetaPrime` to multiplicity `p - 1`. We use the project's
`primesOver_ramificationIdx_eq_prime_sub_one_at_p` and mathlib's
`Ideal.le_pow_ramificationIdx`. -/
theorem zetaSubOne_pow_p_sub_one_dvd_p :
    (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) ^ (p - 1) ∣ ((p : ℕ) : 𝓞 K) := by
  -- ramificationIdx (rationalPrimeIdeal p) (zetaPrime p K) = p - 1.
  have hram : (rationalPrimeIdeal p).ramificationIdx (zetaPrime p K) = p - 1 :=
    primesOver_ramificationIdx_eq_prime_sub_one_at_p (p := p) (K := K) (zetaPrime p K)
      (zetaPrime_mem_primesOver_at_p (p := p) (K := K))
  -- map (algebraMap ℤ (𝓞 K)) (rationalPrimeIdeal p) ≤ (zetaPrime p K) ^ (p - 1).
  have h_le := Ideal.le_pow_ramificationIdx
    (R := ℤ) (S := 𝓞 K)
    (p := rationalPrimeIdeal p) (P := zetaPrime p K)
  rw [hram] at h_le
  -- Cast (p : 𝓞 K) ∈ map ... rationalPrimeIdeal p:
  have hp_mem : ((p : ℕ) : 𝓞 K) ∈
      (rationalPrimeIdeal p).map (algebraMap ℤ (𝓞 K)) := by
    have h_int : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by
      push_cast; rfl
    rw [h_int]
    refine Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 K)) ?_
    rw [rationalPrimeIdeal]
    exact Ideal.subset_span (Set.mem_singleton _)
  -- so (p : 𝓞 K) ∈ (zetaPrime)^{p-1}, which is the span of (ζ-1)^{p-1}.
  have hp_in_pow : ((p : ℕ) : 𝓞 K) ∈ (zetaPrime p K) ^ (p - 1) := h_le hp_mem
  rw [show zetaPrime p K =
    Ideal.span {((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)} from rfl,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hp_in_pow
  exact hp_in_pow

/-- **`(ζ-1)^2 ∣ p` for `p ≥ 3`** in `𝓞 K`. Direct corollary of
`zetaSubOne_pow_p_sub_one_dvd_p`: `(ζ-1)^2 ∣ (ζ-1)^{p-1} ∣ p` when
`p - 1 ≥ 2`, i.e., `p ≥ 3`. -/
theorem zetaSubOne_sq_dvd_p (hp_three : 3 ≤ p) :
    (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) ^ 2 ∣ ((p : ℕ) : 𝓞 K) :=
  (pow_dvd_pow _ (by omega : 2 ≤ p - 1)).trans
    (zetaSubOne_pow_p_sub_one_dvd_p (p := p) (K := K))



end CyclotomicUnits
end PrimaryPlus
end FLT37

end BernoulliRegular

end
