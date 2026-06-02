module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceBinomial
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.MinimalWeight
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.MultinomialMod
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceMultinomial
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitVectors
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.FullTeichSetup
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Stickelberger leading-term identification (REF-18c2c4-L2c3)

Combines the trace-form binomial truncation (L2c2) with the multinomial
expansion of `(traceSum y)^n` and the Layer-1 minimal-weight / digit-
factorial machinery to prove the **digit-sum Stickelberger congruence**
for the reciprocal-convention integral Gauss sum: for `1 ≤ a ≤ p - 1`,

  `g(χ_q^{-a}, ψ) ∈ Q^{s_ℓ(a · d)} ∧ g(χ_q^{-a}, ψ) ∉ Q^{s_ℓ(a · d) + 1}`,

where `d = (#k - 1) / p` and `s_ℓ` is the base-`ℓ` digit sum.
The setup stores the ordinary character `χ_q(x) ≡ x^d (mod Q)`, so the
reciprocal convention is represented by the wrapper
`gaussSumIntRec a = gaussSumInt (p - a)` in the Stickelberger range.

## Strategy

The proof routes through L2c2's `gaussSumInt_qadic_ord_at_prime_of_traceLead`,
which reduces the goal to providing a candidate leading term `lead` with:
1. `lead ∈ Q^s` (containment).
2. `lead ∉ Q^{s+1}` (non-degeneracy).
3. `traceBinomialApprox a s - lead ∈ Q^{s+1}` (the Gauss sum is congruent
   to `lead` modulo `Q^{s+1}`).

We construct `lead = stickelbergerLead a := unit_a · π^s` where `unit_a`
is a unit in `𝓞 R'/Q` lifted from the digit-factorial reciprocal
`(s_ℓ(a · d))! / ∏ aᵢ!` (with `(a₀, …, a_{f-1})` the standard digits).

The third clause is the heaviest: it requires expanding the residual
character sums

  `T_n(a) := ∑_x (S.residueCharInt ^ a) x · C((Tr(c·x)).val, n)`

via the multinomial expansion of `(traceSum (c·x))^n` (Layer 1) plus
character orthogonality (`FiniteField.sum_pow_units`), and identifying
the unique surviving multi-index at minimum weight `s_ℓ(a · d)` via
`digitSum_decomp_unique_at_minimum`.

## Status

This file contains the main theorem statement and a structured
decomposition into sub-lemmas. The containment and non-degeneracy halves
are still the substantive L2c3 gaps.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

end Furtwaengler

end BernoulliRegular
