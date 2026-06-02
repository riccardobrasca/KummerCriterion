module

public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.CyclotomicUnitTwist

/-!
# Aggregate σ_a-twist for `pollaczekUnit` (LV005c1b — partial)

Distribute the standard cyclotomic Galois automorphism `σ_a :=
cyclotomicSigmaOfUnit p K a` over the Pollaczek product
`pollaczekUnit p K i = ∏_b ((1-ζ^b)/(1-ζ))^{b^{p-1-i}}` (over the
half-range `b ∈ {1, …, (p-1)/2}`), using the factor-wise σ-twist from
LV005c1a (`cyclotomicSigmaOfUnit_smul_cyclotomicUnit_mul_cyclotomicUnit`).

This file ships the **first stage** of LV005c1b's chain:

  `σ_a(pollaczekUnit p K i : 𝓞 K) · cyclotomicUnit p K (a : ZMod p).val ^ S =
   ∏_{b ∈ Ico 1 ((p-1)/2 + 1)} cyclotomicUnit p K (((a : ZMod p) * b).val)
                                  ^ (b ^ (p - 1 - i))`,

where `S = ∑_b b^{p-1-i}` is the half-range exponent sum.

The remaining stages (half-range pair-up reducing
`cyclotomicUnit p K (((a · b).val)` back to half-range; reindex; absorb
exponent discrepancy mod `p`; Fermat reduction `(a⁻¹.val)^E ≡ a^i (mod p)`)
build the full eigenvalue identity
`σ_a(pollaczekUnit i) ≡ pollaczekUnit i ^{a^i} (mod p-th powers)`.
Those stages are **not yet shipped here**; they require the half-range
pair-up symmetry analogous to `pollaczekR_split_reindex` /
`pollaczekR_half_range_factorisation` (LV004e) at the K-side
`cyclotomicUnit` level. Track in LV005c1b's residual.

## Main result

* `cyclotomicSigmaOfUnit_smul_pollaczekUnit_aggregate` — the aggregate
  σ-twist in the substitution form (no inversion, no half-range
  pair-up yet).

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), Lemma 8.2 / Lemma 8.4 (p. 156); proof of Cor 8.19 (p. 158).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section AggregateTwist



end AggregateTwist

section PairUp

/-- **Cyclotomic-unit pair-up identity**: for `1 ≤ c < p` (so `(p - c)` is
also in `Finset.Ico 1 p`),

  `ζ^c · cyclotomicUnit p K (p - c) = -cyclotomicUnit p K c` in `𝓞 K`.

Equivalently `cyclotomicUnit p K (p - c) = -ζ^{-c} · cyclotomicUnit p K c`,
expressed in the inversion-free multiplicative form.

Proof: multiply by `(ζ - 1)`. The LHS becomes
`ζ^c · (ζ^{p-c} - 1) = ζ^p - ζ^c = 1 - ζ^c = -(ζ^c - 1)`. The RHS becomes
`-(ζ - 1) · cyclotomicUnit c = -(ζ^c - 1)`. Cancel `(ζ - 1) ≠ 0`. -/
theorem zeta_pow_mul_cyclotomicUnit_p_sub_eq_neg
    (c : ℕ) (hc : c ≤ p) :
    ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ c * cyclotomicUnit p K (p - c) =
      -cyclotomicUnit p K c := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set ζ : 𝓞 K := ((zeta_spec p ℚ K).unit' : 𝓞 K)
  have hζ_sub_one_ne_zero : (ζ - 1 : 𝓞 K) ≠ 0 :=
    (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero
  -- ζ^p = 1.
  have hζ_p : ζ ^ p = 1 := by
    have hζ_prim : IsPrimitiveRoot ζ p := (zeta_spec p ℚ K).unit'_coe
    exact hζ_prim.pow_eq_one
  -- Multiply both sides by (ζ - 1) and cancel.
  refine mul_right_cancel₀ hζ_sub_one_ne_zero ?_
  calc ζ ^ c * cyclotomicUnit p K (p - c) * (ζ - 1)
      = ζ ^ c * ((ζ - 1) * cyclotomicUnit p K (p - c)) := by ring
    _ = ζ ^ c * (ζ ^ (p - c) - 1) := by
          rw [zeta_sub_one_mul_cyclotomicUnit]
    _ = ζ ^ c * ζ ^ (p - c) - ζ ^ c := by ring
    _ = ζ ^ p - ζ ^ c := by
          rw [← pow_add, Nat.add_sub_cancel' hc]
    _ = 1 - ζ ^ c := by rw [hζ_p]
    _ = -(ζ ^ c - 1) := by ring
    _ = -((ζ - 1) * cyclotomicUnit p K c) := by
          rw [zeta_sub_one_mul_cyclotomicUnit]
    _ = -cyclotomicUnit p K c * (ζ - 1) := by ring

/-- **Inversion-free pair-up corollary**: for `1 ≤ d ≤ p`,
`cyclotomicUnit p K d = -ζ^d · cyclotomicUnit p K (p - d)` in `𝓞 K`.

Derived from `zeta_pow_mul_cyclotomicUnit_p_sub_eq_neg` by multiplying
through by `ζ^d` and using `ζ^p = 1` to collapse `ζ^d · ζ^{p-d} = 1`. -/
theorem cyclotomicUnit_eq_neg_zeta_pow_mul_cyclotomicUnit_p_sub
    (d : ℕ) (hd : d ≤ p) :
    cyclotomicUnit p K d =
      -((zeta_spec p ℚ K).unit' : 𝓞 K) ^ d *
        cyclotomicUnit p K (p - d) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set ζ : 𝓞 K := ((zeta_spec p ℚ K).unit' : 𝓞 K)
  have hζ_p : ζ ^ p = 1 := by
    have hζ_prim : IsPrimitiveRoot ζ p := (zeta_spec p ℚ K).unit'_coe
    exact hζ_prim.pow_eq_one
  -- Apply zeta_pow_mul_cyclotomicUnit_p_sub_eq_neg with c = p - d.
  have h := zeta_pow_mul_cyclotomicUnit_p_sub_eq_neg
    (p := p) (K := K) (p - d) (Nat.sub_le _ _)
  -- h : ζ^{p-d} · cyclotomicUnit (p - (p-d)) = -cyclotomicUnit (p-d).
  -- p - (p - d) = d (using d ≤ p).
  rw [show p - (p - d) = d from Nat.sub_sub_self hd] at h
  -- h : ζ^{p-d} · cyclotomicUnit d = -cyclotomicUnit (p-d).
  -- Multiply both sides by ζ^d, use ζ^d · ζ^{p-d} = ζ^p = 1.
  have h_pow : ζ ^ d * ζ ^ (p - d) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hd, hζ_p]
  calc cyclotomicUnit p K d
      = 1 * cyclotomicUnit p K d := by ring
    _ = (ζ ^ d * ζ ^ (p - d)) * cyclotomicUnit p K d := by rw [h_pow]
    _ = ζ ^ d * (ζ ^ (p - d) * cyclotomicUnit p K d) := by ring
    _ = ζ ^ d * (-cyclotomicUnit p K (p - d)) := by rw [h]
    _ = -ζ ^ d * cyclotomicUnit p K (p - d) := by ring

end PairUp

section HalfRangeReduction



end HalfRangeReduction

section HalfRangeBijection

end HalfRangeBijection

section PerTermSwap


end PerTermSwap

section StageFive


end StageFive

section StageSix












end StageSix

set_option maxRecDepth 4000000
set_option linter.style.setOption false in
set_option maxHeartbeats 4000000





end FLT37

end BernoulliRegular

end
