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
/-- A maximal ideal of `𝓞 K` containing the rational prime `ℓ` lies over
the principal ideal `(ℓ)` of `ℤ`. -/
theorem under_eq_span_of_natCast_mem
    (P : Ideal (𝓞 K₀)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ₀ : 𝓞 K₀) ∈ P) :
    Ideal.under ℤ P = Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ) := by
  have hℓ_in_comap : (ℓ₀ : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K₀)) P := by
    rw [Ideal.mem_comap]
    simpa using hℓ_in_P
  have h_span_le : Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ) ≤ Ideal.under ℤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hℓ_in_comap
  have hℓ_prime_int : Prime ((ℓ₀ : ℤ)) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using (Fact.out : ℓ₀.Prime)
  have h_span_max : (Ideal.span ({(ℓ₀ : ℤ)} : Set ℤ)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hℓ_prime_int.irreducible
  have h_under_ne_top : Ideal.under ℤ P ≠ ⊤ := by
    intro h
    have h_one_mem_under : (1 : ℤ) ∈ Ideal.under ℤ P := h ▸ Submodule.mem_top
    have h_one_mem_comap :
        (1 : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K₀)) P := by
      simpa [Ideal.under] using h_one_mem_under
    have h_one_mem : (1 : 𝓞 K₀) ∈ P := by
      simpa using h_one_mem_comap
    exact hP_max.ne_top (Ideal.eq_top_of_isUnit_mem _ h_one_mem isUnit_one)
  exact (h_span_max.eq_of_le h_under_ne_top h_span_le).symm



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

/-! ## Step 2: applying the abstract Stickelberger theorems

Given a `ConcreteStickelbergerSetup S`, the bundle's `gaussSumInt_mem_Q`
gives `g(χ_q)^p ∈ Q^p` directly. Here we package it for the c.1 chain. -/

section Step2

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')


end Step2

/-! ## Step 3: Galois descent to 𝓞 K

Given the bundle's `S.gaussSumInt a ^ p ∈ S.Q ^ p` for `Q ⊂ 𝓞 R'`,
we use Galois descent of valuations to express the corresponding
ideal-membership in `𝓞 K` at the prime `q = Q.under (𝓞 K)`.

The descent: ramification of `Q` over `q = Q ∩ 𝓞 K` for the cyclotomic
extension `K → R' = K(ζ_ℓ)` is `ℓ - 1` (totally ramified above the
prime ℓ via `ζ_ℓ - 1`). For `x ∈ 𝓞 K`, `v_q(x) = v_Q(x) / (ℓ - 1)`. -/

section Step3

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

omit [NumberField K] in
/-- **Step 3: pull the prime back to 𝓞 K.**
For `Q ⊂ 𝓞 R'` and the algebra map `𝓞 K →+* 𝓞 R'`, the prime ideal
`Q.under (𝓞 K)` is a prime of `𝓞 K` lying above `(ℓ : ℤ)`. -/
theorem Q_under_isPrime {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
    (Q : Ideal (𝓞 R')) [Q.IsPrime] :
    (Q.under (𝓞 K)).IsPrime :=
  Ideal.IsPrime.under (𝓞 K) (P := Q)

omit [Fact (Nat.Prime ℓ)] [NumberField K] in
/-- The pulled-back prime contains ℓ. -/
theorem Q_under_contains_ell {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (Q : Ideal (𝓞 R')) [Q.IsPrime] (hQ : (ℓ : 𝓞 R') ∈ Q) :
    (ℓ : 𝓞 K) ∈ Q.under (𝓞 K) := by
  rw [show (Q.under (𝓞 K)) = Ideal.comap (algebraMap (𝓞 K) (𝓞 R')) Q from rfl]
  rw [Ideal.mem_comap]
  rw [show (algebraMap (𝓞 K) (𝓞 R') (ℓ : 𝓞 K)) = (ℓ : 𝓞 R') from by push_cast; rfl]
  exact hQ

/-- The pulled-back prime is non-bot. -/
theorem Q_under_ne_bot
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (Q : Ideal (𝓞 R')) [Q.IsPrime] (hQ : (ℓ : 𝓞 R') ∈ Q) :
    Q.under (𝓞 K) ≠ ⊥ := by
  intro hbot
  have h_in_under : (ℓ : 𝓞 K) ∈ Q.under (𝓞 K) :=
    Q_under_contains_ell Q hQ
  rw [hbot, Ideal.mem_bot] at h_in_under
  have : (ℓ : 𝓞 K) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact this h_in_under

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- The pulled-back prime is in the cyclotomic-conjugates orbit of any
prime above ℓ in `𝓞 K`. (Galois transitivity above a fixed rational
prime.) -/
theorem Q_under_mem_cyclotomicConjugates [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (_hq_ne : q ≠ ⊥)
    (hq_above : q.under ℤ = Ideal.span ({(ℓ : ℤ)} : Set ℤ))
    (Q : Ideal (𝓞 R')) [Q.IsPrime] (hQ : (ℓ : 𝓞 R') ∈ Q) :
    haveI : (Q.under (𝓞 K)).IsPrime := Q_under_isPrime Q
    Q.under (𝓞 K) ∈ cyclotomicConjugates (p := p) (K := K) q := by
  haveI : (Q.under (𝓞 K)).IsPrime := Q_under_isPrime Q
  refine mem_cyclotomicConjugates_iff_under_eq.mpr ?_
  -- Goal: (Q.under (𝓞 K)).under ℤ = q.under ℤ.
  -- Both equal `(ℓ)` (Q.under (𝓞 K) lies above ℓ since (ℓ : 𝓞 K) ∈ it; q similarly).
  have h1 : (ℓ : ℤ) ∈ ((Q.under (𝓞 K)).under ℤ) := by
    rw [show (Q.under (𝓞 K)).under ℤ =
        Ideal.comap (algebraMap ℤ (𝓞 K)) (Q.under (𝓞 K)) from rfl]
    rw [Ideal.mem_comap]
    rw [show (algebraMap ℤ (𝓞 K) (ℓ : ℤ)) = (ℓ : 𝓞 K) from by push_cast; rfl]
    exact Q_under_contains_ell Q hQ
  -- Both Q.under (𝓞 K).under ℤ and q.under ℤ are non-zero primes of ℤ
  -- containing (ℓ); both must equal (ℓ).
  haveI : (Q.under (𝓞 K)).LiesOver ((Q.under (𝓞 K)).under ℤ) := ⟨rfl⟩
  have h_under_ne : (Q.under (𝓞 K)).under ℤ ≠ ⊥ := by
    -- (ℓ : ℤ) ≠ 0 and ∈ this ideal.
    intro hbot
    rw [hbot, Ideal.mem_bot] at h1
    have : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    exact this h1
  haveI : ((Q.under (𝓞 K)).under ℤ).IsPrime := Ideal.IsPrime.under ℤ (P := Q.under (𝓞 K))
  haveI : ((Q.under (𝓞 K)).under ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance h_under_ne
  haveI : (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp (Fact.out : ℓ.Prime)
  haveI : (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  -- Both are maximal primes of ℤ containing (ℓ). They equal (ℓ).
  -- (ℓ) ⊆ Q.under (𝓞 K).under ℤ since (ℓ : ℤ) ∈ that ideal.
  have h2 : Ideal.span ({(ℓ : ℤ)} : Set ℤ) ≤ (Q.under (𝓞 K)).under ℤ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact h1
  -- Now both are maximal, so equal.
  have h3 : Ideal.span ({(ℓ : ℤ)} : Set ℤ) = (Q.under (𝓞 K)).under ℤ :=
    Ideal.IsMaximal.eq_of_le inferInstance
      (Ideal.IsMaximal.ne_top inferInstance)
      h2
  rw [← h3, hq_above]

end Step3

/-! ## Bundle-level wrappers

When a `ConcreteStickelbergerSetup S` is supplied, the prime `S.Q ⊂ 𝓞 R'`
above ℓ pulls back to a prime `q_K := S.Q.under (𝓞 K) ⊂ 𝓞 K` above ℓ.
We package the previous step-3 theorems as bundle accessors. -/

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- The descent prime in `𝓞 K`: `q_K := S.Q.under (𝓞 K)`. -/
noncomputable def descentPrime : Ideal (𝓞 K) := S.Q.under (𝓞 K)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
theorem descentPrime_isPrime : (S.descentPrime).IsPrime := haveI := S.hQ_prime
  Q_under_isPrime (K := K) S.Q


theorem descentPrime_ne_bot : S.descentPrime ≠ ⊥ :=
  haveI := S.hQ_prime
  Q_under_ne_bot (K := K) (ℓ := ℓ) S.Q S.hQ


end ConcreteStickelbergerSetup
end Furtwaengler

end BernoulliRegular
