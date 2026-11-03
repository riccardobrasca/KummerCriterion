module

public import KummerCriterion.ZetaFactorisation.NumberFieldEulerProduct

/-!
# Euler-product assembly for cyclotomic zeta factorisation

This module contains the global Euler-product arguments
`KummerCriterion.ZetaFactorisation`.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped Topology nonZeroDivisors

namespace KummerCriterion

section ZetaFactorisation

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The finite product of character Euler products converges to the product of `L`-values. -/
lemma LProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun q : Nat.Primes ↦ (charLocalFactor p (q : ℕ) s)⁻¹) (LProduct p s) := by
  classical
  simpa only [LProduct, charLocalFactor, Finset.prod_inv_distrib,
    DirichletCharacter.LFunction_eq_LSeries _ hs] using
    (hasProd_prod (s := Finset.univ) fun χ _ ↦
      DirichletCharacter.LSeries_eulerProduct_hasProd χ hs)

lemma localFactors_agree_prime_ne_p {q : Nat.Primes} (hq : (q : ℕ) ≠ p) {s : ℂ} :
    dedekindLocalFactor K (q : ℕ) s = charLocalFactor (p := p) (q : ℕ) s := by
  have : Fact (q : ℕ).Prime := ⟨q.2⟩
  rw [dedekindLocalFactor_eq_pow_localResidueDegree (p := p) (K := K) hq,
    charLocalFactor_eq_pow_localResidueDegree (p := p) hq]

/-- For `K = ℚ(ζ_p)` with `p` prime, the product of Dirichlet `L`-functions of
all characters mod `p` equals `(1 - p^{-s}) · ζ_K(s)`.

The extra `(1 - p^{-s})` factor arises because `LFunctionTrivChar p s =
(1 - p^{-s}) · ζ(s)` uses the imprimitive convention for the trivial character
mod `p`, whereas the classical `ζ_K(s) = ∏_χ L(s, χ̃)` (Washington Thm 4.3)
uses the *primitive* `L`-function `ζ(s)` for the trivial character. -/
theorem LProduct_eq_one_sub_p_neg_s_mul_dedekindZeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LProduct (p := p) s = (1 - (p : ℂ) ^ (-s)) * NumberField.dedekindZeta K s := by
  classical
  let p₀ : Nat.Primes := ⟨p, hp.out⟩
  have hcombine : NumberField.dedekindZeta K s =
      LProduct p s * (1 - (p : ℂ) ^ (-s))⁻¹ := by
    refine (dedekindZeta_hasProd K hs).unique ?_
    convert (LProduct_hasProd p hs).mul
      (hasProd_pi_single p₀ ((1 - (p : ℂ) ^ (-s))⁻¹)) using 1
    ext q
    by_cases hq : q = p₀
    · subst q
      simp only [Pi.mulSingle_eq_same]
      rw [charLocalFactor_at_p, inv_one, one_mul, dedekindLocalFactor_at_p]
    · rw [Pi.mulSingle_eq_of_ne hq, mul_one,
        localFactors_agree_prime_ne_p (p := p) (K := K)
          (fun heq ↦ hq (Subtype.ext heq))]
  rw [hcombine]
  field_simp [Complex.one_sub_prime_cpow_ne_zero hp.out hs]

lemma LProduct_eq_trivial_mul_nontrivial {s : ℂ} :
    LProduct (p := p) s =
      DirichletCharacter.LFunctionTrivChar p s * nontrivialLProduct p s := by
  classical
  unfold LProduct nontrivialLProduct
  rw [show nontrivialCharacters (p := p) = Finset.univ.erase 1 from rfl,
    ← Finset.mul_prod_erase Finset.univ (fun χ => DirichletCharacter.LFunction χ s)
      (Finset.mem_univ 1)]

lemma nontrivialLProduct_eq_even_mul_odd {s : ℂ} :
    nontrivialLProduct p s = evenLProduct p s * oddLProduct p s := by
  classical
  unfold nontrivialLProduct evenLProduct oddLProduct
    nontrivialCharacters evenNontrivialCharacters oddCharacters
  have hdisj : Disjoint
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even ∧ χ ≠ 1)
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Odd) := by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχe hχo
    rw [Finset.mem_filter] at hχe hχo
    exact DirichletCharacter.Odd.not_even χ hχo.2 hχe.2.1
  have hunion : Finset.univ.erase (1 : DirichletCharacter ℂ p) =
      Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even ∧ χ ≠ 1) ∪
        Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd) := by
    ext χ
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      and_true, true_and]
    refine ⟨fun hne => ?_, ?_⟩
    · rcases DirichletCharacter.even_or_odd χ with he | ho
      · exact Or.inl ⟨he, hne⟩
      · exact Or.inr ho
    · rintro (⟨_, hne⟩ | ho)
      · exact hne
      · rintro rfl
        exact DirichletCharacter.Odd.not_even _ ho (by
          change (1 : DirichletCharacter ℂ p) (-1) = 1
          rw [MulChar.one_apply (isUnit_one.neg)])
  rw [hunion, Finset.prod_union hdisj]

/-- The classical Washington Thm 4.3 formula: `ζ_K(s) = ζ(s) · ∏_{χ≠1} L(s, χ)`
for `K = ℚ(ζ_p)`. -/
theorem dedekindZeta_eq_riemannZeta_mul_nontrivialLProduct_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    NumberField.dedekindZeta K s = riemannZeta s * nontrivialLProduct p s := by
  have hs_ne : s ≠ 1 := fun h => by
    rw [h] at hs
    simp at hs
  have h1 : LProduct (p := p) s = (1 - (p : ℂ) ^ (-s)) * NumberField.dedekindZeta K s :=
    LProduct_eq_one_sub_p_neg_s_mul_dedekindZeta_of_one_lt_re p K hs
  have h2 : LProduct (p := p) s =
      (1 - (p : ℂ) ^ (-s)) * (riemannZeta s * nontrivialLProduct p s) := by
    rw [LProduct_eq_trivial_mul_nontrivial p, LFunction_trivial_eq_mul_riemannZeta p hs_ne,
      mul_assoc]
  exact mul_left_cancel₀ (Complex.one_sub_prime_cpow_ne_zero hp.out hs) (h1.symm.trans h2)

end ZetaFactorisation

end KummerCriterion
