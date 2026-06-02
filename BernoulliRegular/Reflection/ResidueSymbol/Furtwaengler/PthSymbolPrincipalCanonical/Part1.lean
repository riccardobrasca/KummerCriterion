module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolCanonical

/-!
# Canonical `pthSymbolAtIdeal` / `pthSymbolAtPrincipal` and the unconditional c.3 closed form

This file mirrors the `pthSymbolAtIdeal` / `pthSymbolAtPrincipal` API on top
of `pthSymbolAtPrime_canonical`, and uses the explicit Galois-action
transformation from `PthSymbolCanonical.lean` to derive the
**unconditional c.3 closed form**:

```
pthSymbolAtPrincipal_canonical α h_stick.gen =
  ∑ a : CyclotomicUnitDelta p,
    pthSymbolAtPrime_canonical (σ_a α) q_K
```

Compared to the conditional theorem
`pthSymbolAtPrincipal_eq_galois_sum_of_hypothesis` (in
`KummerFurtwaengler.lean`), the canonical version is *unconditional*:
the explicit `(a : ZMod p)` factor in the Galois-action transformation
cancels the digit-sum `a.val` factor, so the closed form eliminates
both the `a.val` weights and the `StickelbergerGaloisHypothesis` input.

## Main definitions and theorems

* `pthSymbolAtIdeal_canonical α I` — the canonical residue symbol at an
  integral ideal, defined as the multiset sum of
  `pthSymbolAtPrime_canonical α P` over the prime factors `P` of `I`.
* `pthSymbolAtPrincipal_canonical α β` — the canonical principal symbol,
  defined as `pthSymbolAtIdeal_canonical α (Ideal.span {β})`.
* `pthSymbolAtPrincipal_canonical_eq_galois_sum` — the **c.3 unconditional
  closed form** taking only `StickelbergerIdealEquality q_K`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Canonical `pthSymbolAtIdeal`

Mirrors `pthSymbolAtIdeal` but uses `pthSymbolAtPrime_canonical` as the
prime-level building block. -/











/-! ### Canonical `pthSymbolAtPrincipal` -/



/-! ### c.3 unconditional half (consequence of c.1 only)

Mirror of `pthSymbolAtPrincipal_eq_stickelberger_sum`: from the
`StickelbergerIdealEquality` (c.1) we expand the canonical principal
symbol into the digit sum
`∑ a, ↑a.val * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K)`. -/


/-! ### c.3 unconditional Galois transformation per term

The key lemma: for a non-bot prime `q_K` and any `a, α`, the term
`↑a.val * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K)`
equals the Galois-translated term
`pthSymbolAtPrime_canonical (σ_a α) q_K`.

Proof: the canonical Galois-action lemma
`pthSymbolAtPrime_canonical_galoisAction` gives, for the inverse direction,
```
pthSymbolAtPrime_canonical (σ_a α) (σ_a • σ_{a⁻¹} q_K) =
  (a : ZMod p) * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K).
```
Since `σ_a (σ_{a⁻¹} q_K) = q_K`, this reads
```
pthSymbolAtPrime_canonical (σ_a α) q_K =
  (a : ZMod p) * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K).
```
Now `↑a.val = (a : ZMod p)` in `ZMod p`. The hypotheses on `α` and `p`
in `pthSymbolAtPrime_canonical_galoisAction` rule out the bad cases;
we case-split to handle them via the `_eq_zero` lemmas. -/


/-! ### c.3 unconditional closed form

The main theorem: combining the digit-sum expansion with the per-term
Galois transformation yields the unconditional closed form
```
pthSymbolAtPrincipal_canonical α γ = ∑_a pthSymbolAtPrime_canonical (σ_a α) q_K.
```
No `StickelbergerGaloisHypothesis` is needed: the explicit `(a : ZMod p)`
factor in the canonical Galois-action lemma cancels the `a.val` weight in
the digit sum. -/


/-! ### REF-19 canonical: principal symbol vanishing for hyperprimary singular

Combining the canonical KFR with `(η) = b^p` (singular η) gives that the
canonical residue symbol of η on any principal ideal `(γ)` (with γ
coprime to (η, p)) vanishes. This is the consumer-facing form for REF-19. -/


/-! ### Ideal-level canonical symbol API for `α`

These mirror the corresponding `pthSymbolAtIdeal` API lemmas
(`pthSymbolAtIdeal_one_alpha`, `_zero_alpha`, `_pow`, `_mul`) but for the
canonical symbol. Each one reduces, term-by-term over the prime factorization
of `I`, to the corresponding `pthSymbolAtPrime_canonical` lemma. -/

















/-! ### Principal-level canonical symbol API

Mirror of the principal-level API in `KummerFurtwaengler.lean`. These lemmas
directly reduce to the ideal-level versions, since
`pthSymbolAtPrincipal_canonical α β = pthSymbolAtIdeal_canonical α (Ideal.span {β})`. -/

end Furtwaengler

end BernoulliRegular
