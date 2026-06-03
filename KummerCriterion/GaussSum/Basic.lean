module

public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Gauss sums for Dirichlet characters modulo a prime

Thin wrapper around mathlib's `gaussSum` specialised to Dirichlet characters
modulo a prime `p`, using the standard additive character
`ZMod.stdAddChar`.

## Main results

* `KummerCriterion.gaussSum_one_stdAddChar`: the Gauss sum of the trivial
 Dirichlet character modulo a prime `p` with the standard additive character
 equals `-1`.
* `KummerCriterion.gaussSum_mul_gaussSum_inv_stdAddChar`: for a non-trivial
 Dirichlet character `χ` modulo a prime `p`,
 `τ(χ) · τ(χ̄) = χ(-1) · p`.
* `KummerCriterion.DirichletCharacter.isPrimitive_of_prime_of_ne_one`:
 `p` prime, every non-trivial Dirichlet character mod `p` is primitive.
* `KummerCriterion.gaussSum_stdAddChar_mulShift`: the key Galois-equivariance
 identity for the Gauss sum: for nontrivial `χ` mod prime `p` and `a: ZMod p`,
 `gaussSum χ (stdAddChar.mulShift a) = χ⁻¹ a · gaussSum χ stdAddChar`.
* `KummerCriterion.isIntegral_gaussSum_stdAddChar`: the Gauss sum
 `τ(χ) = gaussSum χ ZMod.stdAddChar` is an algebraic integer — integral over `ℤ`
 as an element of `ℂ`.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

open scoped BigOperators ComplexConjugate

section GaussSum

variable (p : ℕ) [hp : Fact p.Prime]

/-- For a non-trivial Dirichlet character `χ` modulo a prime `p`,
`τ(χ) · τ(χ̄) = χ(-1) · p`, where `τ(χ) = gaussSum χ ZMod.stdAddChar` is
the classical Gauss sum. -/
theorem gaussSum_mul_gaussSum_inv_stdAddChar
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSum χ (ZMod.stdAddChar (N := p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) =
      χ (-1) * p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_prim : (ZMod.stdAddChar : AddChar (ZMod p) ℂ).IsPrimitive :=
    ZMod.isPrimitive_stdAddChar p
  have h_card : (Fintype.card (ZMod p) : ℂ) = p := by
    rw [ZMod.card]
  have h1 : gaussSum χ (ZMod.stdAddChar (N := p)) *
      gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))⁻¹ = (p : ℂ) := by
    rw [← h_card]; exact gaussSum_mul_gaussSum_eq_card hχ h_prim
  have h2 := mul_gaussSum_inv_eq_gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))
  have h_neg_unit : IsUnit (-1 : ZMod p) := isUnit_one.neg
  have h_sq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, show (-1 : ZMod p) * -1 = 1 from by ring, MulChar.map_one]
  have h_ne : χ (-1) ≠ 0 := fun h => by
    rw [h, mul_zero] at h_sq; exact zero_ne_one h_sq
  have h_inv_neg_one : χ⁻¹ (-1) = χ (-1) := by
    have h_inv_mul : χ⁻¹ (-1) * χ (-1) = 1 := by
      rw [← MulChar.mul_apply, MulChar.inv_mul, MulChar.one_apply h_neg_unit]
    exact mul_right_cancel₀ h_ne (h_inv_mul.trans h_sq.symm)
  rw [h_inv_neg_one] at h2
  have h3 : χ (-1) * (gaussSum χ (ZMod.stdAddChar (N := p)) *
      gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))⁻¹) = χ (-1) * p := by rw [h1]
  rw [show χ (-1) * (gaussSum χ (ZMod.stdAddChar (N := p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))⁻¹) =
      gaussSum χ (ZMod.stdAddChar (N := p)) *
        (χ (-1) * gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))⁻¹) from by ring, h2] at h3
  exact h3

/-- For a prime modulus `p`, any non-trivial Dirichlet character
is primitive. Follows from `χ.conductor ∣ p` and the fact that the only
character factoring through `1` is the trivial character. -/
theorem DirichletCharacter.isPrimitive_of_ne_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    χ.IsPrimitive := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime hp.out).mp χ.conductor_dvd_level with h | h
  · exact absurd ((DirichletCharacter.factorsThrough_one_iff χ).mp
      (h ▸ χ.factorsThrough_conductor)) hχ
  · exact h

/-- The quadratic Dirichlet character modulo `p`, viewed as
`ℂ`-valued so it can be paired with `ZMod.stdAddChar` in Gauss sums. -/
noncomputable def quadraticCharComplex : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- The quadratic character modulo `p`, after base change to
`ℂ`, is still quadratic. -/
theorem quadraticCharComplex_isQuadratic :
    (quadraticCharComplex p).IsQuadratic := by
  simpa [quadraticCharComplex] using
    (quadraticChar_isQuadratic (F := ZMod p)).comp (Int.castRingHom ℂ)

/-- For odd prime `p`, the quadratic character modulo `p` is
nontrivial after base change to `ℂ`. -/
theorem quadraticCharComplex_ne_one (hp₂ : p ≠ 2) :
    quadraticCharComplex p ≠ 1 := by
  simpa [quadraticCharComplex] using
    (MulChar.ringHomComp_ne_one_iff
      (f := Int.castRingHom ℂ) (hf := Int.cast_injective)).2
      (quadraticChar_ne_one (F := ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂))

/-- The quadratic character modulo `p` is self-inverse after
base change to `ℂ`. -/
theorem quadraticCharComplex_inv :
    (quadraticCharComplex p)⁻¹ = quadraticCharComplex p := by
  simpa using
    (quadraticCharComplex_isQuadratic (p := p)).inv

/-- The quadratic character at `-1` is given by `χ₄(p)`. -/
theorem quadraticCharComplex_eval_neg_one_eq_chi4 (hp₂ : p ≠ 2) :
    quadraticCharComplex p (-1) = ZMod.χ₄ p := by
  rw [quadraticCharComplex, MulChar.ringHomComp_apply,
    quadraticChar_neg_one (F := ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂), ZMod.card]
  rfl

/-- The value of the quadratic character at `-1` is determined
by `p % 4`. -/
theorem quadraticCharComplex_eval_neg_one (hp₂ : p ≠ 2) :
    quadraticCharComplex p (-1) = if p % 4 = 1 then 1 else -1 := by
  have hp_odd : p % 2 = 1 := by
    rcases hp.out.odd_of_ne_two hp₂ with ⟨k, hk⟩
    omega
  rw [quadraticCharComplex_eval_neg_one_eq_chi4 (p := p) hp₂, ZMod.χ₄_nat_eq_if_mod_four]
  simp [hp_odd]

/-- If `p ≡ 1 (mod 4)`, the quadratic character takes the value
`1` at `-1`. -/
theorem quadraticCharComplex_eval_neg_one_of_mod_four_eq_one (hp₂ : p ≠ 2)
    (hp₄ : p % 4 = 1) :
    quadraticCharComplex p (-1) = 1 := by
  simp [quadraticCharComplex_eval_neg_one (p := p) hp₂, hp₄]

/-- If `p ≡ 3 (mod 4)`, the quadratic character takes the value
`-1` at `-1`. -/
theorem quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (hp₂ : p ≠ 2)
    (hp₄ : p % 4 = 3) :
    quadraticCharComplex p (-1) = -1 := by
  simp [quadraticCharComplex_eval_neg_one (p := p) hp₂, hp₄]

end GaussSum

end KummerCriterion
