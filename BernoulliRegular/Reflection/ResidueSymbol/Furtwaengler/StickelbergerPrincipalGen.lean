module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolIdealGaloisAction


/-!
# `α^Θ`: the Stickelberger principal generator

This file defines the **element-level** Stickelberger generator `α^Θ`
for `α : 𝓞 K`, where `Θ = ∑_a a · σ_{a^{-1}}` is the Stickelberger
element of `ℤ[(ZMod p)ˣ]`. Concretely:

```
α^Θ := ∏_{a ∈ (ZMod p)ˣ} (σ_{a^{-1}} α) ^ a.val.
```

This is the principal-ideal specialisation of the Stickelberger
factorisation: at the ideal level, the existing
`stickelbergerIdeal q_K = ∏_a (σ_{a^{-1}} q_K)^{a.val}` for primes
extends multiplicatively, and for `A = Ideal.span {α}` the factorisation
generator is exactly `α^Θ`.

This is the right intermediate object for the strategy pivot
(see `.mathlib-quality/ref18_pivot.md`):

* Φ(A) = g(A)^p has ideal `(Φ(A)) = A^Θ`.
* For principal A = (α), `Φ((α)) = u(α) · α^Θ` (principal unit factor).
* Primary α ⟹ u(α) = ±1 ⟹ the unit factor's residue symbol is trivial.
* Norm-form Kelly theorem `(Φ(A)/B)_p = (NB/A)_p` then gives Eisenstein
  reciprocity directly.

## Main definitions

* `stickelbergerPrincipalGen α` — the element `α^Θ ∈ 𝓞 K`.
* `stickelbergerPrincipalGen_zero` — `0^Θ = 0`.
* `stickelbergerPrincipalGen_one` — `1^Θ = 1`.
* `stickelbergerPrincipalGen_mul` — multiplicativity.
* `stickelbergerPrincipalGen_ne_zero` — `α ≠ 0 ⟹ α^Θ ≠ 0`.
* `span_stickelbergerPrincipalGen` — `(α^Θ) = stickelbergerIdeal_principal α`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **The Stickelberger principal generator** `α^Θ ∈ 𝓞 K`, where
`Θ = ∑_a a · σ_{a^{-1}}` is the Stickelberger element. Defined as
`∏_a (σ_{a^{-1}} α)^a.val`. -/
noncomputable def stickelbergerPrincipalGen (α : 𝓞 K) : 𝓞 K :=
  ∏ a : CyclotomicUnitDelta p,
    (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ ((a : ZMod p).val)






/-! ### Connection to `stickelbergerIdeal` for principal ideals

Specialise the existing `stickelbergerIdeal` (defined for ideals of `𝓞 K`)
to a principal ideal `Ideal.span {α}`. The result equals
`Ideal.span {α^Θ}` where `α^Θ = stickelbergerPrincipalGen α`.
-/












/-! ### Symbol of `α` against `(β^Θ)` as a Galois sum

The canonical residue symbol `(α / (β^Θ))_p` decomposes as a sum over
Galois indices of the principal symbols `(α / (σ_{a^{-1}} β))_p`.

This is the principal-ideal analogue of
`pthSymbolAtPrincipal_canonical_eq_stickelberger_sum` for general
principal `(β)` (not just primes with a Stickelberger ideal equality). -/


/-! ### Helper: prod-induction pattern for `pthSymbolAtIdeal_canonical_mul_α`

A `Finset.prod` of integral elements, each coprime to every prime factor
of an ideal, can be expanded under `pthSymbolAtIdeal_canonical` slot 1
into a sum of individual symbols.
-/

/-- **Finset-product version of `pthSymbolAtIdeal_canonical_mul_α`**.
For a finset `s : Finset ι` indexing elements `f i : 𝓞 K`, with each
`f i` coprime to every prime factor of `I`, the canonical residue symbol
in the numerator slot satisfies
`(∏_i f i / I)_p = ∑_i (f i / I)_p`. -/
theorem pthSymbolAtIdeal_canonical_finset_prod_α {ι : Type*}
    (s : Finset ι) (f : ι → 𝓞 K) {I : Ideal (𝓞 K)}
    (hf : ∀ i ∈ s, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, f i ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (∏ i ∈ s, f i) I =
      ∑ i ∈ s, pthSymbolAtIdeal_canonical (p := p) (K := K) (f i) I := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, pthSymbolAtIdeal_canonical_one_alpha,
      Finset.sum_empty]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [pthSymbolAtIdeal_canonical_mul_α (p := p)
      (hf i (Finset.mem_insert_self i s))]
    · rw [ih (fun j hj P hP => hf j (Finset.mem_insert_of_mem hj) P hP)]
    · -- ∀ P ∈ normalizedFactors I, ∏_{j ∈ s} f j ∉ P (P prime).
      intro P hP h_in_prod
      obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
      haveI : P.IsPrime := hP_max.isPrime
      -- ∏ f ∈ P (prime) ⟹ some f j ∈ P.
      obtain ⟨j, hj_mem, hj_in⟩ :=
        Ideal.IsPrime.prod_mem_iff.mp h_in_prod
      exact (hf j (Finset.mem_insert_of_mem hj_mem) P hP) hj_in

/-! ### Left-slot Galois sum for `(α^Θ / γ)_p`

The principal symbol with `α^Θ` in the numerator and `γ` in the denominator
expands as a Galois-weighted sum:
```
(α^Θ / γ)_p = ∑_a a.val · (σ_{a^{-1}} α / γ)_p
```
This uses the multiplicativity and power form of the canonical symbol in
its first (numerator) slot, applied to the explicit Finset-product
expression for `α^Θ`. -/



end Furtwaengler

end BernoulliRegular

end
