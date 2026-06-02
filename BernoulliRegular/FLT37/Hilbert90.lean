module

public import BernoulliRegular.FLT37.PrimaryDescent
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import FltRegular.CaseII.AuxLemmas

/-!
# Hilbert 90 setup for `K/K⁺` (ticket FLT37b2b2-b)

For a CM cyclotomic field `K = ℚ(ζ_p)`, `Gal(K/K⁺) = {1, σ}` where `σ` is
complex conjugation. This file packages:

* `algebraMap_norm_eq_self_mul_complexConj`: for `x : K`,
  `algebraMap K⁺ K (Algebra.norm K⁺ x) = x * complexConj K x`. The
  degree-2 specialisation of `Algebra.norm_eq_prod_automorphisms`.
* `norm_complexConj_div_self_eq_one`: for non-zero `α : K`,
  `Algebra.norm K⁺ (σα/α) = 1` — the input to Hilbert 90.

Future companions in this file (b-hilbert90, b-coprime, b-kummer) will
build the chain leading to `σα/α = u·v^p` (FLT37b2b2-b).

## References

* Washington, *Introduction to Cyclotomic Fields*, Theorem 6.16.
* `groupCohomology.exists_div_of_norm_eq_one` (Hilbert 90 cyclic).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

section NormComplexConj

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The Galois group `Gal(K/K⁺)` viewed as a `Finset` is `{1, complexConj K}`. -/
private theorem finset_univ_galois_eq [IsCMField K] :
    haveI : DecidableEq (K ≃ₐ[K⁺] K) := Classical.decEq _
    (Insert.insert (1 : K ≃ₐ[K⁺] K) {complexConj K}) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  rw [Finset.card_insert_of_notMem (by simp [(complexConj_ne_one K).symm]),
    Finset.card_singleton]
  have : Fintype.card (K ≃ₐ[K⁺] K) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact (IsGalois.card_aut_eq_finrank K⁺ K).trans (finrank_K_over_Kplus (K := K))
  omega



end NormComplexConj

/-! ## Hilbert 90: `σα/α = γ/σγ` (FLT37b2b2-b-hilbert90)

The cyclic Hilbert 90 in mathlib (`groupCohomology.exists_div_of_norm_eq_one`)
is stated for `K, L : Type` at universe 0. We therefore restrict our K to
universe 0 in this section. (This is no loss for concrete cyclotomic fields
like `CyclotomicField 37 ℚ`.) -/

section Hilbert90

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Every element of `Gal(K/K⁺)` is a power of `complexConj K`, since the
group has order 2. -/
private theorem mem_zpowers_complexConj [IsCMField K] (σ : K ≃ₐ[K⁺] K) :
    σ ∈ Subgroup.zpowers (complexConj K) := by
  rcases algEquiv_eq_one_or_complexConj σ with rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩



end Hilbert90

/-! ## Coprime descent: `α · γ ∈ K⁺` (FLT37b2b2-b-coprime) -/

section CoprimeDescent

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K



end CoprimeDescent

/-! ## Norm formula for principal ideals (FLT37b2b2-d-norm-singleton)

For `K/K⁺` Galois of degree 2, the relative norm of a principal ideal
satisfies `(relNorm (a)).map = (a) · (σa)`. This is the singleton case
of the general formula `(relNorm 𝔞).map = 𝔞 · σ𝔞`, which underlies the
class-group descent of `[𝔞·σ𝔞]`. -/

section NormSingleton

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K





end NormSingleton

/-! ## Class descent of `[𝔞·σ𝔞]` for primary `(α) = 𝔞^p` (FLT37b2b2-d-class)

Combining the singleton norm formula with `pow_dvd_pow_iff_dvd` (Dedekind
domain UFM) yields the descent for the specific 𝔞 used in Vandiver Lemma 1:
when `(α) = 𝔞^p`, the class `[𝔞·σ𝔞] = [𝔞]²` lifts to `Cl(𝓞 K⁺)` via
`relNorm 𝔞`. -/

section ClassDescentFromSingleton

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K



end ClassDescentFromSingleton

/-! ## b-kummer-local-prime: σα/α has high `(ζ-1)`-valuation (FLT37b2b2-b-kummer-1)

For primary α, the difference `σα - α` is divisible by `(ζ-1)^{2p}` in
`𝓞 K`. We package this as the existence of an explicit witness `η`. -/

section KummerLocalPrime

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K








end KummerLocalPrime

end FLT37

end BernoulliRegular

end
