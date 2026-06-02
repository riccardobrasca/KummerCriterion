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
