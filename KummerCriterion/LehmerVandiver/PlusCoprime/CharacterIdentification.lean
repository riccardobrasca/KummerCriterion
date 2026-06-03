module

public import KummerCriterion.LehmerVandiver.PrimaryUnits.Part1
public import KummerCriterion.LehmerVandiver.PrimaryUnits.Part2
public import KummerCriterion.LehmerVandiver.PrimaryUnits.Part3
public import KummerCriterion.UnitQuotient.DeltaAction

/-!
# Cyclotomic-unit pair-up

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
 GTM 83), Lemma 8.2 / Lemma 8.4 (p. 156); proof of Cor 8.19 (p. 158).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset
open scoped NumberField

namespace KummerCriterion

namespace LehmerVandiver

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

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
  -- h: ζ^{p-d} · cyclotomicUnit (p - (p-d)) = -cyclotomicUnit (p-d).
  -- p - (p - d) = d (using d ≤ p).
  rw [show p - (p - d) = d from Nat.sub_sub_self hd] at h
  -- h: ζ^{p-d} · cyclotomicUnit d = -cyclotomicUnit (p-d).
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

end LehmerVandiver

end KummerCriterion

end
