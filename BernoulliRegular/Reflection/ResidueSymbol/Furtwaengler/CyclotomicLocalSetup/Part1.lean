module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IntegralBridge
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CanonicalResidueRoot
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Ideal.GoingUp


/-!
# Concrete cyclotomic local setup at a prime above ℓ ≠ p

This file is the home for **REF-18c2c5-b** — constructing a
`ConcreteStickelbergerSetup ℓ p k K R'` instance where
`K = ℚ(ζ_p)`, `R' ⊃ K` is a cyclotomic extension containing `ζ_ℓ`,
and the user supplies a prime `Q ⊂ 𝓞 R'` above ℓ.

## Strategy

We provide a CONSTRUCTOR `mkConcreteStickelbergerSetup` taking the
prime `Q` (above ℓ in `𝓞 R'`) as input and assembling all the required
witnesses from mathlib's cyclotomic API:

* `zeta_p` and `zeta_ell` come from
  `IsCyclotomicExtension.exists_isPrimitiveRoot` applied to `R'`.
* `zeta_p_int`, `zeta_ell_int` come from `IsPrimitiveRoot.toInteger`.
* The residue field `k = 𝓞 R' / Q` is the canonical choice; the
  residue map is `Ideal.Quotient.mk Q`.
* `card_k = ℓ ^ f` requires the inertia degree of Q over ℓ.
* The primitive p-th root in k is the image of `zetaPInt` under the
  residue map; primitivity requires `p ∣ #k - 1`.

## Status

Stage 1 (primitive roots in R') — DONE.
Stage 2 (integral lifts in 𝓞 R') — DONE.
Stage 3 (residue field and map) — DONE.
Stage 4 (assembly into the bundle) — REMAINING (still needs `card_k`,
   `hzeta_k`, `hdiv` and the bundle-building tactic).
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace CyclotomicLocalSetup

variable (p ℓ : ℕ) [hp : Fact p.Prime] [hℓ : Fact ℓ.Prime]
variable (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (R' : Type w) [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']

/-! ### Step 1 — choose primitive roots in `R'` -/





/-! ### Step 2 — integral lifts in `𝓞 R'` -/




/-! ### Step 3 — residue field and map (given prime Q above ℓ)

Given a prime `Q ⊂ 𝓞 R'` containing ℓ, the residue field is
`k = 𝓞 R' / Q` and the residue map is the canonical quotient map.
The Q is supplied by the user; existence is via going-up
(`Ideal.nonempty_primesOver`).
-/

variable (Q : Ideal (𝓞 R')) [Q.IsPrime]







/-! ### Step 5 — primitive p-th root in residue field

Apply mathlib's `IsPrimitiveRoot.idealQuotient_mk` to lift `zetaPInt` to
a primitive p-th root in the residue field, given coprimality of
`absNorm Q` with `p`.
-/

/-! ### Step 6 — bundle assembly

We assemble all the pieces into a `ConcreteStickelbergerSetup`. The
key trick: take the `Field` and `Fintype` instances on `residueField R' Q`
as **explicit parameters** so the structure's `[Field k] [Fintype k]`
binder can match. The user constructs them (or uses our defs) before
calling.
-/

/-! Step 1 status: the SCALAR fields (zeta_p, zeta_ell, zeta_p_int,
zeta_ell_int, π, Q, residueMap, hπ, etc.) are constructed above.
The 5 ADDITIONAL fields the structure requires (`zeta_p_int_residue`,
`psi`, `hpsi`, `psiExponent`, `psi_eq_zeta_ell_pow`) require building
the additive character `ψ : k →+ R'` from a trace map. This is
itself ~100 LOC of trace-form infrastructure, deferred. -/

/-! ### Stage 4 — residue field cardinality witness for `k = 𝓞 K ⧸ P`

For the source-side bundle `S : FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'`,
the `card_k` field requires `Fintype.card (𝓞 K ⧸ P) = ℓ ^ f` for some
`f : ℕ`. We derive this from `Ideal.absNorm_eq_pow_inertiaDeg'`, with
`f` the inertia degree of `P` over `(ℓ : ℤ)`. -/

variable {p₀ ℓ₀ : ℕ} [Fact p₀.Prime] [Fact ℓ₀.Prime]
variable {K₀ : Type v} [Field K₀] [NumberField K₀]
  [IsCyclotomicExtension {p₀} ℚ K₀]

omit [NumberField K₀] in



/-! ### Stage 4 — `ringChar` of `𝓞 K ⧸ P` -/


/-! ### Stage 4 — `Algebra (ZMod ℓ) (𝓞 K ⧸ P)` instance -/


/-! ### Stage 4 — residueMap construction at a split prime

Building the bundle for `k = 𝓞 K ⧸ P` requires a ring hom
`residueMap : 𝓞 R' →+* (𝓞 K ⧸ P)` with explicit kernel a prime `Q` of
`𝓞 R'` over `P`. This requires `f(Q/P) = 1` (residue degree one), since
otherwise `𝓞 R' ⧸ Q` is a strict extension of `𝓞 K ⧸ P`. We package
the splitting witness as an iso `𝓞 R' ⧸ Q ≃+* 𝓞 K ⧸ P` plus the
under-equality. -/


/-! ### Stage 4 — K-algebra compatibility of the splitting iso

For the split-prime construction to identify `S.descentPrime` (= `Q.under (𝓞 K)`)
with `P`, we need the iso `𝓞 R' ⧸ Q ≃+* 𝓞 K ⧸ P` to be K-algebra
compatible — i.e., the iso composed with `Quotient.mk Q ∘ algebraMap`
on the `𝓞 R'` side equals `Quotient.mk P` on the `𝓞 K` side. -/



/-! ### Stage 4 — Canonical K-alg-compat splitting iso under residue degree 1

When `Q.under (𝓞 K) = P` and the canonical induced ring hom
`(𝓞 K ⧸ P) →+* (𝓞 R' ⧸ Q)` is surjective (the `f(Q/P) = 1` condition),
we can construct the canonical iso `(𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)`. This
iso satisfies `IsKAlgebraCompatibleSplittingIso` automatically. -/







end CyclotomicLocalSetup
end Furtwaengler

end BernoulliRegular
