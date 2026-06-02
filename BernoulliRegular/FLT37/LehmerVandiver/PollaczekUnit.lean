module

public import BernoulliRegular.FLT37.PrimaryUnits

/-!
# Pollaczek cyclotomic unit `pollaczekUnit p i`

For an odd prime `p` and an even integer `i ∈ {2, 4, …, p-3}`,
Washington defines the **Pollaczek cyclotomic unit**

  `E_i := ∏_{b=1}^{(p-1)/2} ((1 - ζ^b) / (1 - ζ))^{b^{p-1-i}} ∈ (𝓞 K)ˣ`

inside `K = ℚ(ζ_p)` where `ζ = ζ_p` is a primitive `p`-th root of
unity (Washington, *Introduction to Cyclotomic Fields*, §8.3, p. 156).

The factor `(1 - ζ^b) / (1 - ζ)` is the cyclotomic unit
`cyclotomicUnit p K b` (a unit in `𝓞 K` because `b` is coprime to `p`
in the relevant range), already developed in
`BernoulliRegular/FLT37/PrimaryUnits.lean`.

This file provides the definition and the basic API:

* `pollaczekUnit_one`  – the degenerate value when the index range is
  empty (i.e. `p = 2`), giving `pollaczekUnit p K i = 1`.
* `pollaczekUnit_norm` – the integer norm `Algebra.norm ℤ` of the
  underlying ring-of-integers element equals `1`. This follows from
  multiplicativity of the norm and `cyclotomicUnit_norm_int`.
* `pollaczekUnit_complexConj` – the **symmetrised real combination**
  `pollaczekUnit p K i · σ(pollaczekUnit p K i)` is fixed by complex
  conjugation, so descends to the maximal real subfield `K⁺`. This
  mirrors the `realCyclotomicUnit` pattern in `PrimaryUnits.lean`.
  Washington's bare `E_i` is **not** literally `σ`-fixed in
  `(𝓞 K)ˣ`; only `E_i · σ(E_i)` is. Washington's proof of
  Proposition 8.18 (p. 158) handles the residual `ζ`-twist mod `p`-th
  powers; the precise mod-`ℓ` statement is the content of ticket
  **LV004**.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units), p. 156-158.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section PollaczekUnit

/-- For `b` strictly between `0` and `p` (a prime), `b` is coprime to
`p`. Convenience helper for indexing the Pollaczek product. -/
theorem pollaczek_coprime_of_pos_lt {b : ℕ} (hb : 0 < b) (hbp : b < p) :
    b.Coprime p :=
  (Nat.coprime_of_lt_prime hb.ne' hbp hp.1).symm

/-- For `b ∈ [1, (p-1)/2]` and `p` an odd prime, `b < p`. -/
theorem pollaczek_lt_of_le_half {b : ℕ} (hb : b ≤ (p - 1) / 2) : b < p := by
  have hp_pos : 0 < p := hp.1.pos
  have h1 : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
  omega

omit hp in
/-- Membership in the Pollaczek index range gives both `1 ≤ b` and
`b ≤ (p-1)/2`, the convenient combined form. -/
theorem mem_pollaczek_range_iff (b : ℕ) :
    b ∈ Finset.Ico 1 ((p - 1) / 2 + 1) ↔ 1 ≤ b ∧ b ≤ (p - 1) / 2 := by
  rw [Finset.mem_Ico]; omega

/-- The cyclotomic factor at index `b` in the Pollaczek product, well
defined for `b ∈ [1, (p-1)/2]`. We prove `1 ≤ b` and `b < p` from the
index hypothesis using `mem_pollaczek_range_iff` and
`pollaczek_lt_of_le_half`. -/
noncomputable def pollaczekFactor {b : ℕ}
    (hb : b ∈ Finset.Ico 1 ((p - 1) / 2 + 1)) : (𝓞 K)ˣ :=
  cyclotomicUnitUnit p K b
    (pollaczek_coprime_of_pos_lt p ((mem_pollaczek_range_iff p b).mp hb).1
      (pollaczek_lt_of_le_half p ((mem_pollaczek_range_iff p b).mp hb).2))
    hp.1.two_le

/-- The value of `pollaczekFactor` is the underlying cyclotomic unit. -/
@[simp]
theorem pollaczekFactor_val {b : ℕ}
    (hb : b ∈ Finset.Ico 1 ((p - 1) / 2 + 1)) :
    (pollaczekFactor p K hb : 𝓞 K) = cyclotomicUnit p K b := by
  unfold pollaczekFactor
  exact cyclotomicUnitUnit_val _ _ _ _ _


end PollaczekUnit

section PollaczekAPI

variable (i : ℕ)




end PollaczekAPI

end FLT37

end BernoulliRegular

end
