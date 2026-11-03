module

public import KummerCriterion.GaussSum.SignInvariant.BlockDeterminant
import KummerCriterion.GaussSum.SignInvariant.VandermondeEndpoint
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import TauCeti.NumberTheory.DirichletCharacter.Even

/-!
# Branch choice for the quadratic Gauss sum

This file compares the determinant formula coming from the block decomposition
with the independent Vandermonde computation, and uses that comparison to fix
the quadratic Gauss-sum branch in the two mod-`4` cases.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

attribute [local instance] Classical.decEq Classical.propDecidable

/-- Each prescribed parity occurs for half the complex Dirichlet characters modulo an odd prime. -/
theorem card_characters_apply_neg_one (hp₂ : p ≠ 2) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ p ↦ χ (-1) = ε).card = (p - 1) / 2 := by
  have h := DirichletCharacter.two_mul_card_apply_neg_one_mul_apply_neg_one_eq
    (R := ℂ) (a := p) (b := 1) (Or.inl (lt_of_le_of_ne hp.out.two_le hp₂.symm)) hε
  have e : {q : DirichletCharacter ℂ p × DirichletCharacter ℂ 1 //
      q.1 (-1) * q.2 (-1) = ε} ≃ {χ : DirichletCharacter ℂ p // χ (-1) = ε} :=
    (Equiv.prodUnique _ _).subtypeEquiv fun q ↦ by
      change q.1 (-1) * q.2 (-1) = ε ↔ q.1 (-1) = ε
      rw [DirichletCharacter.even_of_le_two (n := 1) (by decide) q.2, mul_one]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Nat.totient_one, mul_one, Nat.totient_prime hp.out] at h
  omega

/-- The even complex Dirichlet characters modulo `p` have cardinality
`(p - 1) / 2`. -/
theorem card_even_characters (hp₂ : p ≠ 2) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 :=
  card_characters_apply_neg_one p hp₂ (Or.inl rfl)

theorem quadraticCharComplex_odd_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    (quadraticCharComplex p).Odd := by
  simpa [DirichletCharacter.Odd] using
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (p := p) hp₂ hp₄

/-- The even non-self-dual characters. -/
noncomputable def evenNonselfdualCharacterFinset : Finset (DirichletCharacter ℂ p) :=
  (nonselfdualCharacterFinset (p := p)).filter fun χ => χ.Even

/-- One representative from each even non-self-dual inverse pair. -/
noncomputable def evenNonselfdualCharacterReps : Finset (DirichletCharacter ℂ p) :=
  (nonselfdualCharacterReps (p := p)).filter fun χ => χ.Even

theorem mem_evenNonselfdualCharacterFinset_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ evenNonselfdualCharacterFinset (p := p) ↔
      χ ∈ nonselfdualCharacterFinset (p := p) ∧ χ.Even := by
  simp [evenNonselfdualCharacterFinset]

theorem mem_evenNonselfdualCharacterReps_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ evenNonselfdualCharacterReps (p := p) ↔
      χ ∈ nonselfdualCharacterReps (p := p) ∧ χ.Even := by
  simp [evenNonselfdualCharacterReps]

theorem evenNonselfdualCharacterFinset_eq_union_evenReps_image_inv (hp₂ : p ≠ 2) :
    evenNonselfdualCharacterFinset (p := p) =
      evenNonselfdualCharacterReps (p := p) ∪
        (evenNonselfdualCharacterReps (p := p)).image fun χ => χ⁻¹ := by
  ext χ
  constructor
  · intro hχ
    rcases (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχnon, hχeven⟩
    rcases mem_reps_or_inv_mem_reps (p := p) (hp₂ := hp₂) hχnon with hχrep | hχinvrep
    · exact Finset.mem_union.mpr <| Or.inl <|
        (mem_evenNonselfdualCharacterReps_iff (p := p) χ).2 ⟨hχrep, hχeven⟩
    · have hχinv_even : (χ⁻¹ : DirichletCharacter ℂ p).Even :=
        (DirichletCharacter.even_inv_iff χ).2 hχeven
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_image.mpr ⟨χ⁻¹,
          (mem_evenNonselfdualCharacterReps_iff (p := p) (χ⁻¹)).2 ⟨hχinvrep, hχinv_even⟩,
          by simp⟩
  · intro hχ
    rcases Finset.mem_union.mp hχ with hχrep | hχimage
    · rcases (mem_evenNonselfdualCharacterReps_iff (p := p) χ).1 hχrep with
        ⟨hχrep', hχeven⟩
      exact (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).2
        ⟨(mem_nonselfdualCharacterReps_iff (p := p) χ).1 hχrep' |>.1, hχeven⟩
    · rcases Finset.mem_image.mp hχimage with ⟨ψ, hψrep, rfl⟩
      rcases (mem_evenNonselfdualCharacterReps_iff (p := p) ψ).1 hψrep with ⟨hψrep', hψeven⟩
      exact (mem_evenNonselfdualCharacterFinset_iff (p := p) ψ⁻¹).2
        ⟨inv_mem_nonselfdualCharacterFinset (p := p)
            ((mem_nonselfdualCharacterReps_iff (p := p) ψ).1 hψrep' |>.1),
          (DirichletCharacter.even_inv_iff ψ).2 hψeven⟩

theorem disjoint_evenNonselfdualCharacterReps_image_inv :
    Disjoint (evenNonselfdualCharacterReps (p := p))
      ((evenNonselfdualCharacterReps (p := p)).image fun χ => χ⁻¹) := by
  refine Finset.disjoint_left.mpr ?_
  intro χ hχrep hχimage
  rcases Finset.mem_image.mp hχimage with ⟨ψ, hψrep, hψ⟩
  have hψrep' : ψ ∈ nonselfdualCharacterReps (p := p) :=
    (mem_evenNonselfdualCharacterReps_iff (p := p) ψ).1 hψrep |>.1
  have hχrep' : χ ∈ nonselfdualCharacterReps (p := p) :=
    (mem_evenNonselfdualCharacterReps_iff (p := p) χ).1 hχrep |>.1
  have hψinv : ψ⁻¹ ∈ nonselfdualCharacterReps (p := p) := by
    simpa [hψ] using hχrep'
  exact (inv_not_mem_nonselfdualCharacterReps (p := p) hψrep') hψinv

theorem card_evenNonselfdualCharacterFinset_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    (evenNonselfdualCharacterFinset (p := p)).card = (p - 3) / 2 := by
  classical
  let E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Even
  have hquad_odd : (quadraticCharComplex p).Odd :=
    quadraticCharComplex_odd_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hq_not_even : ¬ (quadraticCharComplex p).Even :=
    DirichletCharacter.Odd.not_even (quadraticCharComplex p) hquad_odd
  have hrewrite :
      evenNonselfdualCharacterFinset (p := p) = E.erase (1 : DirichletCharacter ℂ p) := by
    ext χ
    constructor
    · intro hχ
      rcases (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχnon, hχeven⟩
      rcases (mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχnon with ⟨hχ1, _⟩
      simp [E, hχ1, hχeven]
    · intro hχ
      have hχ1 : χ ≠ (1 : DirichletCharacter ℂ p) := by
        simpa [E] using (Finset.mem_erase.mp hχ).1
      have hχeven : χ.Even := by
        simpa [E] using (Finset.mem_erase.mp hχ).2
      have hχquad : χ ≠ quadraticCharComplex p := fun hχquad =>
        hq_not_even (hχquad ▸ hχeven)
      exact (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).2
        ⟨(mem_nonselfdualCharacterFinset_iff (p := p) χ).2 ⟨hχ1, hχquad⟩, hχeven⟩
  rw [hrewrite, Finset.card_erase_of_mem]
  · rw [card_even_characters (p := p) hp₂]
    omega
  · simp [E]

theorem card_evenNonselfdualCharacterReps_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    (evenNonselfdualCharacterReps (p := p)).card = (p - 3) / 4 := by
  let reps := evenNonselfdualCharacterReps (p := p)
  have hsplit :
      (evenNonselfdualCharacterFinset (p := p)).card = reps.card + reps.card := by
    rw [evenNonselfdualCharacterFinset_eq_union_evenReps_image_inv (p := p) hp₂,
      Finset.card_union_of_disjoint (disjoint_evenNonselfdualCharacterReps_image_inv (p := p)),
      Finset.card_image_of_injective _ (fun χ ψ hEq => by simpa using congrArg Inv.inv hEq)]
  have hcard : (evenNonselfdualCharacterFinset (p := p)).card = (p - 3) / 2 :=
    card_evenNonselfdualCharacterFinset_of_mod_four_eq_three (p := p) hp₂ hp₄
  have htwice : (p - 3) / 2 = reps.card * 2 := by
    omega
  have hdiv : ((p - 3) / 2) / 2 = reps.card :=
    Nat.div_eq_of_eq_mul_left (by decide : 0 < 2) htwice
  have hquarter : ((p - 3) / 2) / 2 = (p - 3) / 4 := by
    omega
  calc
    reps.card = ((p - 3) / 2) / 2 := hdiv.symm
    _ = (p - 3) / 4 := hquarter

theorem prod_pairBlockDeterminants_eq_negOnePow_card_evenReps :
    Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ => -(χ (-1))) =
      (-1 : ℂ) ^ (evenNonselfdualCharacterReps (p := p)).card := by
  classical
  let reps := nonselfdualCharacterReps (p := p)
  let g : DirichletCharacter ℂ p → ℂ := fun χ => if χ.Even then (-1 : ℂ) else 1
  have hrewrite :
      Finset.prod reps (fun χ => -(χ (-1))) = Finset.prod reps g := by
    refine Finset.prod_congr rfl ?_
    intro χ hχ
    rcases DirichletCharacter.even_or_odd χ with hχeven | hχodd
    · have hχeval : χ (-1 : ZMod p) = 1 := by
        simpa [DirichletCharacter.Even] using hχeven
      simp [g, hχeven, hχeval]
    · have hχeval : χ (-1 : ZMod p) = -1 := by
        simpa [DirichletCharacter.Odd] using hχodd
      have hχnot_even : ¬ χ.Even := DirichletCharacter.Odd.not_even χ hχodd
      simp [g, hχnot_even, hχeval]
  have hfilter :
      reps.filter (fun χ => g χ ≠ 1) = reps.filter fun χ => χ.Even := by
    ext χ
    by_cases hχeven : χ.Even
    · have hneq : (-1 : ℂ) ≠ 1 := by norm_num
      simp [g, hχeven, hneq]
    · simp [g, hχeven]
  calc
    Finset.prod reps (fun χ => -(χ (-1))) = Finset.prod reps g := hrewrite
    _ = Finset.prod (reps.filter fun χ => χ.Even) g := by
          rw [← hfilter, Finset.prod_filter_ne_one]
    _ = Finset.prod (reps.filter fun χ => χ.Even) (fun _ => (-1 : ℂ)) := by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          simp [g, (Finset.mem_filter.mp hχ).2]
    _ = (-1 : ℂ) ^ (evenNonselfdualCharacterReps (p := p)).card := by
          simp [evenNonselfdualCharacterReps, reps]

theorem prod_pairBlockDeterminants_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ => -(χ (-1))) =
      (-1 : ℂ) ^ ((p - 3) / 4) := by
  rw [prod_pairBlockDeterminants_eq_negOnePow_card_evenReps (p := p),
    card_evenNonselfdualCharacterReps_of_mod_four_eq_three (p := p) hp₂ hp₄]

/-- On the quadratic line, the block scalar is the negative normalized
quadratic Gauss sum in the `p ≡ 3 [ZMOD 4]` branch. -/
theorem normalizedDft_quadraticScalar_eq_neg_scaledGaussSum_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) =
      -((Real.sqrt p : ℂ)⁻¹ *
        gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) := by
  have hq_ne : quadraticCharComplex p ≠ (1 : DirichletCharacter ℂ p) :=
    quadraticCharComplex_ne_one (p := p) hp₂
  simp [normalizedDftConstOneBasisScalar, hq_ne, quadraticCharComplex_inv (p := p),
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (p := p) hp₂ hp₄]

/-- In the imaginary branch, the quadratic block scalar is `-I`. -/
theorem normalizedDft_quadraticScalar_eq_neg_I_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) = -Complex.I := by
  let qScalar : ℂ := normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p))
  have hdet_block :=
    det_normalizedDft_eq_trivialBlock_mul_quadraticScalar_mul_prod_pairBlockDeterminants
      (p := p) hp₂
  have hdet_vand := det_normalizedDft_eq_negOnePow_mul_I_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hpair := prod_pairBlockDeterminants_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hdet_q :
      LinearMap.det (normalizedDft p) = (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) := by
    calc
      LinearMap.det (normalizedDft p)
          = (-1 : ℂ) * (qScalar * (-1 : ℂ) ^ ((p - 3) / 4)) := by
              simpa [qScalar, hpair] using hdet_block
      _ = (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) := by
            ring
  have hpow_ne : ((-1 : ℂ) ^ ((p - 3) / 4)) ≠ 0 := by simp
  have heq : (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) =
      Complex.I * (-1 : ℂ) ^ ((p - 3) / 4) := by
    calc
      (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) = LinearMap.det (normalizedDft p) :=
        hdet_q.symm
      _ = (-1 : ℂ) ^ ((p - 3) / 4) * Complex.I := hdet_vand
      _ = Complex.I * (-1 : ℂ) ^ ((p - 3) / 4) := by ring
  have hneg : qScalar * (-1 : ℂ) = Complex.I :=
    mul_right_cancel₀ hpow_ne heq
  calc
    qScalar = qScalar * (1 : ℂ) := by ring
    _ = qScalar * ((-1 : ℂ) * (-1 : ℂ)) := by ring
    _ = (qScalar * (-1 : ℂ)) * (-1 : ℂ) := by ring
    _ = Complex.I * (-1 : ℂ) := by rw [hneg]
    _ = -Complex.I := by ring

/-- In the `p ≡ 3 [ZMOD 4]` branch, the quadratic Gauss sum is `I * √p`. -/
theorem gaussSum_quadraticCharComplex_eq_I_mul_sqrt_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
      Complex.I * (Real.sqrt p : ℂ) := by
  have hp_pos_real : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hp_pos_real)
  have hscaled_neg :
      -((Real.sqrt p : ℂ)⁻¹ * gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) =
        -Complex.I := by
    rw [← normalizedDft_quadraticScalar_eq_neg_scaledGaussSum_of_mod_four_eq_three
      (p := p) hp₂ hp₄]
    exact normalizedDft_quadraticScalar_eq_neg_I_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hscaled := congrArg (fun z : ℂ => (-1 : ℂ) * z) hscaled_neg
  have hscaled' :
      (Real.sqrt p : ℂ)⁻¹ * gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
        Complex.I := by
    simpa [mul_assoc] using hscaled
  have hmul := congrArg (fun z : ℂ => (Real.sqrt p : ℂ) * z) hscaled'
  simpa [hsqrt_ne, mul_assoc, mul_left_comm, mul_comm] using hmul

end SignInvariant

end KummerCriterion
