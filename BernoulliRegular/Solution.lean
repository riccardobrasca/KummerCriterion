import BernoulliRegular.BernoulliFast.FermatLastTheoremUpTo100

/-!
Solution side for Comparator: forwards to the project's proof.
-/

theorem fermatLastTheoremFor_le100_of_ne_irregular
    (n : ℕ) (hn_two : 2 < n) (hn_le100 : n ≤ 100)
    (hn37 : n ≠ 37) (hn59 : n ≠ 59) (hn67 : n ≠ 67) (hn74 : n ≠ 74) :
    FermatLastTheoremFor n :=
  BernoulliRegular.fermatLastTheoremFor_le100_of_ne_irregular
    n hn_two hn_le100 hn37 hn59 hn67 hn74
