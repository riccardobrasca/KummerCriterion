# Kummer's Criterion

A [Lean 4](https://leanprover.github.io/) formalisation of **Kummer's criterion**,
the Bernoulli-number characterisation of *regular* primes.

A [blueprint](https://riccardobrasca.github.io/KummerCriterion/blueprint/) describing
the mathematical structure of the proof is available.

## What this project proves

An odd prime `p` is **regular** when it does not divide the class number of the
`p`-th cyclotomic field `ℚ(ζ_p)`. This number-theoretic condition is notoriously
hard to check directly. Kummer's criterion replaces it with a finite, purely
arithmetic test on Bernoulli numbers.

The main theorem lives in
[`KummerCriterion/Main.lean`](KummerCriterion/Main.lean):

```lean
/-- **Kummer's criterion.**

An odd prime `p` is regular iff `p` does not divide the numerator of any
Bernoulli number `B_2, B_4, ..., B_{p-3}`. -/
theorem _root_.KummerCriterion
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2) :
    IsRegularPrime p ↔
      ∀ k, 1 ≤ k → 2 * k ≤ p - 3 → ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num
```

In words: regularity of `p` is equivalent to `p` not dividing the numerator of
any of the Bernoulli numbers `B₂, B₄, …, B_{p-3}` — a condition one can verify by
a finite computation.

## Why it matters: Fermat's Last Theorem for exponents below 100

Kummer's celebrated result is that **Fermat's Last Theorem holds for every
regular prime exponent**. That direction is formalised separately in the
[`flt-regular`](https://github.com/leanprover-community/flt-regular) project, on
which this development is built.

Kummer's criterion is the missing computational ingredient: it turns "is `p`
regular?" into an explicit Bernoulli-number check. Running that check on the
small primes shows that the only irregular primes below 100 are

```
37, 59, 67,
```

so every other odd prime under 100 is regular. Combined with `flt-regular`, this
yields Fermat's Last Theorem for all those exponents — i.e. for the overwhelming
majority of exponents below 100 directly from regularity (the three irregular
exponents 37, 59, 67 being handled by other means).

This is packaged as a self-contained theorem in
[`KummerCriterion/BernoulliFast/FermatLastTheoremUpTo100.lean`](KummerCriterion/BernoulliFast/FermatLastTheoremUpTo100.lean):

```lean
/-- Fermat's Last Theorem for every exponent up to `100` except `2`, the
three irregular primes below `100`, and `74 = 2 * 37`. -/
theorem fermatLastTheoremFor_le100_of_ne_irregular
    (n : ℕ) (hn_two : 2 < n) (hn_le100 : n ≤ 100)
    (hn37 : n ≠ 37) (hn59 : n ≠ 59) (hn67 : n ≠ 67) (hn74 : n ≠ 74) :
    FermatLastTheoremFor n
```

The composite exponent `74 = 2 · 37` is excluded because reducing it by divisor
monotonicity would route through the irregular exponent `37`.

## Infinitely many irregular primes

Irregular primes are not a finite accident: following Carlitz's classical
argument, the project also proves that there are infinitely many of them.
The Bernoulli-number side of Kummer's criterion is combined with the
unrestricted Kummer congruence for divided Bernoulli numbers
`B_m / m ≡ B_n / n (mod p)`, proved here by the elementary Voronoi route.

The endpoint lives in
[`KummerCriterion/IrregularPrimes/Infinitude.lean`](KummerCriterion/IrregularPrimes/Infinitude.lean):

```lean
/-- Infinitely many primes are not regular, by the Carlitz route. -/
theorem infinite_not_isRegularPrime :
    Set.Infinite
      {p : ℕ | ∃ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        ¬ IsRegularPrime p}
```
