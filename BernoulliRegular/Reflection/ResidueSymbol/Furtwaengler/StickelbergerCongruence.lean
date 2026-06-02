module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Setup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitSum

/-!
# Stickelberger congruence assembly (Layer 2, REF-18c2c4)

This file contains the ideal-theoretic assembly step for the digit-sum
Stickelberger congruence.  Once the Gauss sum is known congruent modulo
`Q^(s+1)` to a leading term of exact `Q`-adic order `s`, the desired
membership/non-membership statement follows formally.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler


variable {p : ℕ} [Fact p.Prime]
variable {k : Type*} [Field k] [Fintype k]
variable {R' : Type*} [CommRing R'] [IsDomain R']

namespace StickelbergerSetup

variable (S : StickelbergerSetup p k R')

/-- Non-triviality of the powers `χ_q^a` in the Stickelberger range
`1 ≤ a ≤ p - 1`. -/
theorem residueChar_pow_ne_one {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.residueChar ^ a ≠ 1 := by
  intro h
  have h_order : orderOf S.residueChar = p := S.orderOf_residueChar
  have h_dvd : orderOf S.residueChar ∣ a := orderOf_dvd_of_pow_eq_one h
  rw [h_order] at h_dvd
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have ha_lt : a < p := lt_of_le_of_lt ha₂ (Nat.sub_lt hp_pos Nat.one_pos)
  have ha_ge_p : p ≤ a := Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.one_pos ha₁) h_dvd
  omega




end StickelbergerSetup

end Furtwaengler

end BernoulliRegular
