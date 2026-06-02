module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiIdeal

/-!
# Kelly's prime-level identity (REF-18 Phase 2, sub-piece K)

This file builds the Kelly-form prime identity for `α^Θ / P'`:

```
(α^Θ / P')_p = (NP' / α)_p
```

via three steps (K1–K3 in `.mathlib-quality/ref18_phase2_plan.md`):

* **K1**: `(α^Θ / P')_p = ∑_a a.val · (σ_{a^{-1}} α / P')_p` (left-slot
  Galois sum at a single prime).
* **K2**: integer-against-prime symbol formula for `(n / P')_p`.
* **K3**: the substantive Stickelberger-Eisenstein combination
  `∑_a a.val · (σ_{a^{-1}} α / P')_p = (NP' / α)_p`.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Kelly identities -/






/-! ### K1 — α^Θ symbol left-Galois sum at a single ideal -/

/-- **K1: Left-slot Galois sum for `(α^Θ / B)_p`** at any ideal `B`.

Generalises `pthSymbolAtPrincipal_canonical_principalGen_left_eq_galois_sum`
from principal `(γ)` to arbitrary ideals `B`. The hypothesis is that
each `σ_{a^{-1}} α` is coprime to every prime factor of `B`. -/
theorem pthSymbolAtIdeal_canonical_principalGen_eq_galois_sum
    (α : 𝓞 K) (B : Ideal (𝓞 K))
    (h_coprime : ∀ (a : CyclotomicUnitDelta p)
      (P : Ideal (𝓞 K)), P ∈ normalizedFactors B →
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) B := by
  classical
  unfold stickelbergerPrincipalGen
  -- Distribute pthSymbolAtIdeal_canonical over Finset-prod numerator.
  rw [pthSymbolAtIdeal_canonical_finset_prod_α (p := p) Finset.univ
    (fun a : CyclotomicUnitDelta p =>
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ ((a : ZMod p).val))
    (I := B)
    (fun a _ P hP h_in_pow => ?_)]
  · -- Each (σ_{a^{-1}} α)^a.val term unfolds via _pow_α.
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pthSymbolAtIdeal_canonical_pow_α (p := p)
      (fun P hP => h_coprime a P hP) ((a : ZMod p).val)]
  · -- side condition for finset_prod: (σ_{a^{-1}} α)^a.val ∉ P.
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    haveI hP_prime : P.IsPrime := hP_max.isPrime
    have h_in : cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∈ P :=
      hP_prime.mem_of_pow_mem ((a : ZMod p).val) h_in_pow
    exact (h_coprime a P hP) h_in

/-- **K1 specialised to a single non-bot prime `P'`**: the Galois sum
collapses to a single prime-level term per Galois index. -/
theorem pthSymbolAtIdeal_canonical_principalGen_at_prime_eq_galois_sum
    (α : 𝓞 K) {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P' := by
  classical
  -- Apply the general form, then translate ideal-symbol → prime-symbol at P'.
  rw [pthSymbolAtIdeal_canonical_principalGen_eq_galois_sum α P' ?_]
  · refine Finset.sum_congr rfl fun a _ => ?_
    -- pthSymbolAtIdeal_canonical _ P' = pthSymbolAtPrime_canonical _ P' (P' prime).
    rw [pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) hP'_ne]
  · -- coprimality at every prime factor of P'.
    intro a P hP
    -- normalizedFactors P' = {P'} for prime P'.
    have hP_eq : P = P' := by
      have h_factors :
          UniqueFactorizationMonoid.normalizedFactors P' = ({P'} : Multiset _) := by
        have h_prime_in_R : Prime P' := (Ideal.prime_iff_isPrime hP'_ne).mpr inferInstance
        have h_irreducible : Irreducible P' := h_prime_in_R.irreducible
        have h_assoc :=
          UniqueFactorizationMonoid.normalizedFactors_irreducible h_irreducible
        rw [show normalize P' = P' from normalize_eq P'] at h_assoc
        exact h_assoc
      rw [h_factors] at hP
      exact Multiset.mem_singleton.mp hP
    rw [hP_eq]
    exact h_coprime a

/-! ### K2 — integer-against-prime symbol formula (structural hypothesis)

The substantive content connecting `Σ_a a.val · (σ_{a^{-1}} α / P')_p`
to `(NP' / α)_p` is the **Stickelberger / Gauss-sum norm relation**:
the Galois-weighted sum on the LHS reconstitutes a single integer-norm
symbol on the RHS via the identity `g(χ_{P'}) · g(χ_{P'}^{-1}) = ±NP'`
in the appropriate cyclotomic ring.

We package this as a structural hypothesis `StickelbergerNormRelation α P'`
to be discharged by the substantive Gauss-sum chain.

Note: For `α` Galois-invariant (`α ∈ ℤ ⊆ 𝓞 K`), the LHS sum equals
`(Σ a.val) · (α / P')_p = 0` (since `Σ_{a ∈ (ZMod p)ˣ} a.val ≡ 0
(mod p)` for odd p — `SumUnitsValEqZeroHypothesis`). And the RHS
`(NP' / α)_p` for α ∈ ℤ requires a separate computation; it is NOT
generally zero. So `StickelbergerNormRelation` is a substantive identity
when α is non-trivial in the Galois orbit. -/



/-! ### K3 — concrete Kelly prime equality from K1 + K2 -/



/-! ### Trivial discharge cases for `StickelbergerNormRelation`

The trivial cases `α = 0` and `α = 1` of `StickelbergerNormRelation` hold
unconditionally; we prove them here. -/



/-! ### `StickelbergerNormRelation` for integer α (trivially primary)

For `α = (n : 𝓞 K)` coming from `n ∈ ℤ`, the relation holds with both
sides vanishing in `ZMod p` (for odd `p`):

* **LHS**: `Σ_a a.val · (σ_{a^{-1}} α / P')_p = (Σ a.val) · (α / P')_p`
  since σ_a fixes integer α. By `Σ a.val ≡ 0 (mod p)` (for odd p),
  this is 0.

* **RHS**: `pthSymbolAtIdeal_canonical (NP' : 𝓞 K) (Ideal.span {α})` for
  α ∈ ℤ — vanishes by the Galois-orbit summation argument
  (the prime factors of `(α)` split into Galois orbits, and within each
  orbit the integer-against-prime symbols sum to 0).

The remaining open content for general primary α (NOT just integers) is
the substantive Stickelberger / Gauss-sum norm relation. -/




/-! ### Re-indexing identity for `Σ a.val = Σ a⁻¹.val` -/



/-! ### Galois-invariant β + arithmetic identity ⟹ symbol vanishes -/


/-! ### Trivial discharges of the concrete Kelly equality -/








/-! ### Discharge of `SumUnitsValEqZeroHypothesis` for odd p -/



/-! ### K2 for perfect p-th powers `α = β^p`

Both sides of `StickelbergerNormRelation` vanish unconditionally for `α = β^p`:

* **LHS**: `σ_{a⁻¹}(β^p) = (σ_{a⁻¹} β)^p`, and
  `pthSymbolAtPrime_canonical ((σ β)^p) P' = 0` by
  `pthSymbolAtPrime_canonical_pow_p_eq_zero_uncond`.

* **RHS**: `Ideal.span {β^p} = (Ideal.span {β})^p`, and
  `pthSymbolAtIdeal_canonical _ (I^p) = 0` by
  `pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero`.

This is the cleanest non-trivial substantive discharge of K2 — it relies
only on the unconditional p-th-power kill at the leaf level, not on
Stickelberger / Gauss-sum content. -/





/-! ### K2 multiplicativity: reducing `α · β^p` to `α`

When `β` is coprime to `P'` at every Galois index, multiplying by `β^p`
contributes 0 to both sides of `StickelbergerNormRelation`:

* **LHS**: `pthSymbolAtPrime_canonical (σ_{a⁻¹}(α · β^p)) P' =
  pthSymbolAtPrime_canonical (σ_{a⁻¹} α) P' +
  pthSymbolAtPrime_canonical ((σ_{a⁻¹} β)^p) P' =
  pthSymbolAtPrime_canonical (σ_{a⁻¹} α) P' + 0` (multiplicativity at q + p-th-power kill).

* **RHS**: `pthSymbolAtIdeal_canonical NP' ((α) · (β)^p) =
  pthSymbolAtIdeal_canonical NP' (α) + 0` (ideal multiplicativity + ideal pow-p kill).

So `K2(α · β^p) ⟺ K2(α)` under the coprimality hypothesis. -/



/-! ### General K2 multiplicativity

Both sides of `StickelbergerNormRelation` are additive in α (under
appropriate coprimality at every Galois conjugate of α and β with P',
and the per-α coprimality on the RHS factor decomposition). So
`K2(α · β) ⟺ K2(α)` AND `K2(β)` are equivalent under those conditions. -/



/-! ### Unconditional consumers via _pow_p multiplicativity

Combining the `α = β^p` discharge with multiplicativity by `β^p` gives
unconditional discharges for `α₀ · β^p` whenever `α₀` has a known
the concrete Kelly equality, under coprimality of β.

The most general consumer: for η of the form `α₀ · β^p` where α₀
has a discharged Kelly identity, the full chain produces
the concrete Kelly equality for `α₀ · β^p` at every nonzero prime. -/



/-! ### Unconditional `_of_odd` consumers (no arithmetic hypothesis needed) -/




/-! ### Concrete Kelly equality for unit α — special cases -/

end Furtwaengler

end BernoulliRegular

end
