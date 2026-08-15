module

public import Mathlib.NumberTheory.FLT.Basic

/-!
Challenge statement for Comparator: Fermat's Last Theorem for exponents
`2 < n ≤ 100`, excluding the three irregular primes below `100`
(`37`, `59`, `67`) and the composite `74 = 2 * 37`.

The transitive closure of imports here is the trusted side. Only the bare
mathlib statement of `FermatLastTheoremFor` is required.
-/

public theorem fermatLastTheoremFor_le100_of_ne_irregular
    (n : ℕ) (hn_two : 2 < n) (hn_le100 : n ≤ 100)
    (hn37 : n ≠ 37) (hn59 : n ≠ 59) (hn67 : n ≠ 67) (hn74 : n ≠ 74) :
    FermatLastTheoremFor n := sorry
