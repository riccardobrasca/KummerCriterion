module

public import BernoulliRegular.Reflection.ResidueSymbol.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Non-canonical p-th power residue symbols

This file contains the older choice-dependent residue-symbol API used by some
algebraic Stickelberger support lemmas.  It is only the finite-field
definition and its elementary multiplicativity/vanishing facts.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]

/-- Global noncomputable Fintype instance for `𝓞 K ⧸ q` when `q ≠ ⊥`. -/
noncomputable instance instFintype_OK_quotient {K : Type*}
    [Field K] [NumberField K] (q : Ideal (𝓞 K)) [NeZero q] :
    Fintype (𝓞 K ⧸ q) :=
  have : Finite (𝓞 K ⧸ q) := by
    rw [← Ideal.absNorm_ne_zero_iff]
    exact Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne q)⟩
  Fintype.ofFinite _

/-- The choice-dependent prime-level `p`-th power residue symbol. -/
noncomputable def pthSymbolAtPrime {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) (q : Ideal (𝓞 K)) : ZMod p := by
  classical
  by_cases hbot : q = ⊥
  · exact 0
  haveI : NeZero q := ⟨hbot⟩
  by_cases hmax : q.IsMaximal
  · by_cases hα : α ∈ q
    · exact 0
    by_cases hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1
    · by_cases hroot : ∃ ζ : (𝓞 K ⧸ q)ˣ, IsPrimitiveRoot ζ p
      · haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        haveI : q.IsMaximal := hmax
        exact Reflection.ResidueSymbol.PowerResidue.primeExponent q
          hroot.choose hroot.choose_spec hdiv α hα
      · exact 0
    · exact 0
  · exact 0



/-- Symbol vanishes when `α ∈ q`. -/
theorem pthSymbolAtPrime_eq_zero_of_mem {K : Type*}
    [Field K] [NumberField K] {α : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∈ q) :
    pthSymbolAtPrime (p := p) α q = 0 := by
  unfold pthSymbolAtPrime
  rw [dif_neg hbot, dif_pos hmax, dif_pos hα]


/-- The `p`-th power residue symbol `(α/I)_p` extended to integral ideals. -/
noncomputable def pthSymbolAtIdeal {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) (I : Ideal (𝓞 K)) : ZMod p :=
  ((UniqueFactorizationMonoid.normalizedFactors I).map
    (fun P => pthSymbolAtPrime (p := p) α P)).sum







/-- Each element of `normalizedFactors I` is a prime, nonzero, maximal ideal. -/
theorem isPrime_of_mem_normalizedFactors {K : Type*} [Field K] [NumberField K]
    {I : Ideal (𝓞 K)} {P : Ideal (𝓞 K)}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    P.IsPrime ∧ P ≠ ⊥ ∧ P.IsMaximal := by
  have hPrime : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hP_ne : P ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot]
    exact hPrime.ne_zero
  have hP_isPrime : P.IsPrime := Ideal.isPrime_of_prime hPrime
  refine ⟨hP_isPrime, hP_ne, ?_⟩
  exact Ideal.IsPrime.isMaximal hP_isPrime hP_ne


/-- If `α` lies in every prime factor of `I`, then `(α/I)_p` is zero. -/
theorem pthSymbolAtIdeal_eq_zero_of_mem_all_factors {K : Type*} [Field K] [NumberField K]
    {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∈ P) :
    pthSymbolAtIdeal (p := p) α I = 0 := by
  unfold pthSymbolAtIdeal
  have hmap :
      (UniqueFactorizationMonoid.normalizedFactors I).map
          (fun P => pthSymbolAtPrime (p := p) α P) =
        (UniqueFactorizationMonoid.normalizedFactors I).map
          (fun _P => (0 : ZMod p)) := by
    refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_eq_zero_of_mem hP_ne_bot hP_max (hα P hP)
  rw [hmap]
  simp










end Furtwaengler

end BernoulliRegular

end
