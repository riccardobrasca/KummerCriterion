module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitSum
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Minimal-weight uniqueness for base-`ℓ` decompositions (Layer 1, REF-18c2c4)

For any non-negative integer decomposition `a = Σ_{i<f} k_i · ℓ^i` (with
`k_i ≥ 0`, possibly `k_i ≥ ℓ`), the weight `Σ k_i` is bounded below by
the base-`ℓ` digit sum `s_ℓ(a)`. Equality holds iff `(k_0,…,k_{f-1})`
is the standard base-`ℓ` digit vector of `a` (extended with leading
zeros to length `f`).

This is the **minimal-weight uniqueness theorem** that combines with
`TraceMultinomial.lean`'s expansion to give the digit-sum Stickelberger
congruence: among multinomial-expansion terms of `(traceSum x)^n`
contributing to the `x^a` coefficient, the smallest `n` for which a
non-zero contribution can occur is exactly `s_ℓ(a)`, with a unique
contributing tuple.

## Proof strategy

The clean proof decomposes into three steps:

1. **`digitSum_add_mul`**: for `x < ℓ`,
   `digitSum ℓ (x + ℓ · y) = x + digitSum ℓ y` (via mathlib's
   `Nat.digits_add`).

2. **`digitSum_add_le`**: digit sum is sub-additive,
   `digitSum ℓ (a + b) ≤ digitSum ℓ a + digitSum ℓ b`. Proved via the
   identity `digitSum ℓ n = n − (ℓ−1) · Σ⌊n/ℓ^{i+1}⌋` (Mathlib's
   `Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits`) plus floor
   sup-additivity `⌊(a+b)/c⌋ ≥ ⌊a/c⌋ + ⌊b/c⌋`.

3. **`digitSum_mul_left`**: `digitSum ℓ (ℓ · n) = digitSum ℓ n`,
   since multiplying by `ℓ` prepends a zero digit.

Then the main theorem follows by induction on `f`: write
`S = k 0 + ℓ · T` (where `T = Σ k(j+1) ℓ^j`), then

  `digitSum ℓ S ≤ digitSum ℓ (k 0) + digitSum ℓ (ℓ T)` (sub-additivity)
              `≤ k 0 + digitSum ℓ T` (digitSum_le_self + digitSum_mul_left)
              `≤ k 0 + Σ k(j+1)` (induction hypothesis)
              `= Σ k_i`.

Uniqueness follows from a strict-inequality version of step 1
(when `k 0 ≥ ℓ`, there's a carry that strictly decreases the weight).

These three auxiliary lemmas are stated below as separate `sorry`s
for clarity; the main theorem is then a one-line induction.
-/

@[expose] public section

namespace BernoulliRegular

namespace Furtwaengler








end Furtwaengler

end BernoulliRegular
