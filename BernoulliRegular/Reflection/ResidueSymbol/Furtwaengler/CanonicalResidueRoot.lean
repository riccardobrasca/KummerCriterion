module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Int

/-!
# Canonical primitive `p`-th root of unity in `(𝓞 K ⧸ q)ˣ`

For `K = ℚ(ζ_p)` cyclotomic and a maximal ideal `q ⊂ 𝓞 K` with
`(p : 𝓞 K) ∉ q`, the canonical primitive `p`-th root of unity in
`(𝓞 K ⧸ q)ˣ` is the residue of the canonical primitive `p`-th root
`cyclotomicZetaInteger K ∈ 𝓞 K`.

This avoids the `Classical.choose` obstacle in
`pthSymbolAtPrime`: the canonical choice is fixed by the cyclotomic
Galois action, hence the c.2 transformation
`pthSymbolAtPrime (σ_a α) (σ_a • q) = ? · pthSymbolAtPrime α q`
has unit factor `c = 1` unconditionally.

## Main definitions and theorems

* `canonicalResidueZetaP q hp_in_q` — the canonical primitive `p`-th
  root in `(𝓞 K ⧸ q)ˣ`, defined when `(p : 𝓞 K) ∉ q` (and `q` maximal).
* `canonicalResidueZetaP_isPrimitiveRoot` — primitivity: it is a
  primitive `p`-th root of unity.
* `cyclotomicRingOfIntegersEquiv_apply_zetaInteger` — Galois compatibility:
  `σ_a` acts on `cyclotomicZetaInteger` by raising to the `a.val` power.
* `canonicalResidueZetaP_galois_compat` — the canonical residue zeta at
  `σ_a • q` is the image of the canonical residue zeta at `q` under the
  quotient ring iso induced by `σ_a`, raised to the `a.val` power.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Step 1 — coprimality of `absNorm q` with `p`

If `q` is a maximal ideal of `𝓞 K` with `(p : 𝓞 K) ∉ q`, then
`(absNorm q).Coprime p`. The proof uses the Dedekind structure: the
prime `q.under ℤ` is `⟨ℓ⟩` for some rational prime `ℓ`, and
`absNorm q` is a power of `ℓ`. Since `p ∉ q` and `q` is prime, the
underlying prime is not `p`, so the coprimality follows.
-/

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [Fact p.Prime] in

omit [IsCyclotomicExtension {p} ℚ K] in

/-! ### Step 2 — canonical residue ζ_p definition and primitivity

We define the canonical primitive `p`-th root of unity in `(𝓞 K ⧸ q)ˣ`
as the residue of the canonical primitive `p`-th root of unity
`cyclotomicZetaInteger K ∈ 𝓞 K`. Primitivity follows from
`IsPrimitiveRoot.idealQuotient_mk` once coprimality is established.
-/







/-! ### Step 2b — basic API around primitivity

Convenience lemmas immediately derived from `IsPrimitiveRoot`:
`pow_eq_one`, `ne_one`, `orderOf_eq`, plus a `zpow` form and the
inverse-as-power identity `ζ⁻¹ = ζ ^ (p - 1)`.
-/











/-! ### Step 3 — Galois compatibility of canonical zeta

The cyclotomic Galois action `σ_a` on `𝓞 K` acts on
`cyclotomicZetaInteger` by raising to the `a.val` power.
Concretely, `σ_a • ζ = ζ^a.val` (Mathlib's `cyclotomicSigmaOfUnit_smul_zetaInteger`).
This translates to the residue level via the quotient ring iso.
-/





end Furtwaengler

end BernoulliRegular
