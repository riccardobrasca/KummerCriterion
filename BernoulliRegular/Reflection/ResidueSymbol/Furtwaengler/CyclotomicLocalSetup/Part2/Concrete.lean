module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CanonicalResidueRoot
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup.Part1


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

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-! ### Membership descent

For `x ∈ 𝓞 K`, membership of `x` in `S.descentPrime^n` implies
membership of its image in `S.Q^n`. This is the "easy" direction —
the reverse needs ramification index. -/


/-! ### Ramification index of `descentPrime` in `S.Q`

For the cyclotomic extension `K → R' = K(ζ_ℓ)`, the prime `Q ⊂ 𝓞 R'`
above `descentPrime` has ramification index given by `Ideal.ramificationIdx`.
This packages the abstract ramification index for downstream descent
arguments. -/

/-- The ramification index of `Q ⊂ 𝓞 R'` over `descentPrime ⊂ 𝓞 K`. -/
noncomputable def descentRamificationIdx : ℕ :=
  Ideal.ramificationIdx S.descentPrime S.Q



omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The bundle's prime `S.Q` is not the zero ideal. -/
theorem Q_ne_bot' : S.Q ≠ ⊥ := by
  intro h
  have h_in : (ℓ : 𝓞 R') ∈ (⊥ : Ideal (𝓞 R')) := h ▸ S.hQ
  rw [Ideal.mem_bot] at h_in
  have : (ℓ : 𝓞 R') ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact this h_in

/-- `S.Q.LiesOver S.descentPrime` (definitional). -/
instance Q_liesOver_descentPrime : S.Q.LiesOver S.descentPrime :=
  ⟨rfl⟩

/-! ### Multiplicity descent (full Galois descent of valuations)

The substantive Dedekind-domain content connecting `S.Q`-adic and
`S.descentPrime`-adic valuations: for any `x ∈ 𝓞 K \ {0}`,
`v_Q(algebraMap x) = e · v_q(x)`. Standard application of
`Ideal.emultiplicity_map_eq_ramificationIdx_mul`. -/

/-- Multiplicity descent: `v_Q(algebraMap x) = e · v_q(x)` for any nonzero
`x ∈ 𝓞 K`. -/
theorem emultiplicity_Q_eq_ramificationIdx_mul_emultiplicity_descentPrime
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    {x : 𝓞 K} (hx : x ≠ 0) :
    emultiplicity S.Q (Ideal.span ({algebraMap (𝓞 K) (𝓞 R') x} : Set (𝓞 R'))) =
      S.descentRamificationIdx *
        emultiplicity S.descentPrime (Ideal.span ({x} : Set (𝓞 K))) := by
  haveI := S.descentPrime_isPrime
  have h_descent_ne_bot : S.descentPrime ≠ ⊥ := S.descentPrime_ne_bot
  haveI := S.hQ_prime
  have hQ_ne : S.Q ≠ ⊥ := S.Q_ne_bot'
  haveI := S.Q_liesOver_descentPrime
  have h_map : Ideal.map (algebraMap (𝓞 K) (𝓞 R'))
        (Ideal.span ({x} : Set (𝓞 K))) =
      Ideal.span ({algebraMap (𝓞 K) (𝓞 R') x} : Set (𝓞 R')) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [← h_map]
  have hspan_ne : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hQ_irred : Irreducible S.Q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.prime_of_isPrime hQ_ne S.hQ_prime)
  have hq_irred : Irreducible S.descentPrime :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.prime_of_isPrime h_descent_ne_bot S.descentPrime_isPrime)
  exact Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    hspan_ne hq_irred hQ_irred hQ_ne

/-- The descent ramification index is non-zero. -/
theorem descentRamificationIdx_ne_zero
    [IsDomain (𝓞 K)] [Module.IsTorsionFree (𝓞 K) (𝓞 R')] :
    S.descentRamificationIdx ≠ 0 := by
  haveI := S.descentPrime_isPrime
  haveI := S.hQ_prime
  haveI := S.Q_liesOver_descentPrime
  exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
    S.Q S.descentPrime_ne_bot


/-! ### Iff form of valuation descent

Combining the multiplicity-equality + ramification-index-positivity:
for `x ∈ 𝓞 K \ {0}`, the algebra map sends `x` into `Q^(e*n)` iff
`x ∈ descentPrime^n`. -/

/-- Iff form of valuation descent. -/
theorem mem_descentPrime_pow_iff_algebraMap_mem_Q_pow_mul
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {x : 𝓞 K} (hx : x ≠ 0) (n : ℕ) :
    x ∈ S.descentPrime ^ n ↔
      algebraMap (𝓞 K) (𝓞 R') x ∈ S.Q ^ (S.descentRamificationIdx * n) := by
  haveI := S.descentPrime_isPrime
  have h_descent_ne_bot : S.descentPrime ≠ ⊥ := S.descentPrime_ne_bot
  haveI := S.hQ_prime
  have hQ_ne : S.Q ≠ ⊥ := S.Q_ne_bot'
  haveI := S.Q_liesOver_descentPrime
  -- Translate everything to multiplicities.
  have hspan_x_ne : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hQ_irred : Irreducible S.Q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.prime_of_isPrime hQ_ne S.hQ_prime)
  have hq_irred : Irreducible S.descentPrime :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.prime_of_isPrime h_descent_ne_bot S.descentPrime_isPrime)
  have h_emult :=
    S.emultiplicity_Q_eq_ramificationIdx_mul_emultiplicity_descentPrime hx
  -- LHS membership ↔ pow_dvd of the span by descentPrime.
  have h_lhs : x ∈ S.descentPrime ^ n ↔
      S.descentPrime ^ n ∣ Ideal.span ({x} : Set (𝓞 K)) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  -- RHS membership ↔ pow_dvd of the image span by Q.
  have h_rhs : algebraMap (𝓞 K) (𝓞 R') x ∈ S.Q ^ (S.descentRamificationIdx * n) ↔
      S.Q ^ (S.descentRamificationIdx * n) ∣
        Ideal.span ({algebraMap (𝓞 K) (𝓞 R') x} : Set (𝓞 R')) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [h_lhs, h_rhs]
  rw [pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity]
  rw [h_emult]
  -- Goal: (n : ℕ∞) ≤ emult ↔ (e * n : ℕ∞) ≤ e * emult, where e ≥ 1.
  have he_ne : (S.descentRamificationIdx : ℕ∞) ≠ 0 := by
    exact_mod_cast S.descentRamificationIdx_ne_zero
  have he_top : (S.descentRamificationIdx : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
  rw [show ((S.descentRamificationIdx * n : ℕ) : ℕ∞) =
      (S.descentRamificationIdx : ℕ∞) * (n : ℕ∞) by push_cast; ring]
  exact (ENat.mul_le_mul_left_iff he_ne he_top).symm


/-! ### Translation of step 2 to `descentPrime`

If we are supplied with a Galois-invariance witness `γ ∈ 𝓞 K` with
`algebraMap γ = S.gaussSumInt a ^ p`, the iff form transports the
step-2 Q-adic data into 𝓞 K.

The Galois-invariance witness itself is an open piece (see ticket
REF-18c2c5-b's c.1.4): one shows `S.gaussSumInt a ^ p` is fixed by
`Gal(R'/K)` (using `gaussSumInt_pow_p_invariant` from
`Stickelberger.lean` plus the cyclotomic Galois action), and combined
with `IsCyclotomicExtension.isGalois` and Galois-fixed-implies-in-K
plus `isIntegral_algebraMap_iff`-style descent, this packages a
γ ∈ 𝓞 K. -/

/-! ### Non-vanishing helper

In a domain `𝓞 R'`, `x ^ p ≠ 0 ↔ x ≠ 0` (since p ≥ 1). The bundle's
step-2 always gives `gaussSumInt a ∈ S.Q`, but we need a direct
non-vanishing witness for the descent assembly. This is provided as
a helper. -/

end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
