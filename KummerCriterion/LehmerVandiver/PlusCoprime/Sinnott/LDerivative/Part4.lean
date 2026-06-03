import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part3

@[expose] public section

noncomputable section

open Real Complex
open scoped NumberField

namespace KummerCriterion

namespace LehmerVandiver

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
/-- **Generalised χ ↔ χ⁻¹ reindex** for products over `evenNontrivialCharacters`:
since the set is closed under inversion, the involution χ ↔ χ⁻¹ reindexes
the product without changing its value. -/
theorem prod_evenNontriv_eq_prod_evenNontriv_inv
    (f : DirichletCharacter ℂ p → ℂ) :
    ∏ χ ∈ KummerCriterion.evenNontrivialCharacters p, f χ =
      ∏ χ ∈ KummerCriterion.evenNontrivialCharacters p, f χ⁻¹ := by
  classical
  refine (Finset.prod_bij (fun χ _ => χ⁻¹) ?_ ?_ ?_ ?_).symm
  · intro χ hχ
    exact inv_mem_evenNontrivialCharacters (p := p) hχ
  · intro χ₁ _ χ₂ _ heq
    have := congrArg (fun ψ => ψ⁻¹) heq
    simpa using this
  · intro χ hχ
    refine ⟨χ⁻¹, inv_mem_evenNontrivialCharacters (p := p) hχ, ?_⟩
    exact inv_inv χ
  · intro χ _; rfl

/-- **Matrix-restriction step to the Sinnott matrix (named Prop)**: the
substantive remaining content for, expressing that the squared
determinant of the quotient convolution log-norm matrix times `2^(p-3)`
equals the squared trivial-eigenvalue times the squared regulator of the
cyclotomic-unit family:

 2^(p-3) · (det convolutionMatrixLogNormEven p)² =
 (quotientEigenvalue p 1)² · (regOfFamily...: ℂ)²

This isolates the matrix-restriction step from the abstract Frobenius
det chain: after extracting the trivial-character row/column, the
remaining `(p-3)/2 × (p-3)/2` block is the Sinnott log-embedding matrix,
whose determinant absolute value is `2^((p-3)/2) · |det(A−B)|`. The
factor `2^(p-3) = 4^((p-3)/2)` comes from `M_Sinnott = 2 · (A − B)`,
so `regOfFamily² = 4^((p-3)/2) · det(A−B)² = 2^(p-3) · det(A−B)²`.

The matrix-restriction is the substantive Sinnott regulator content;
the abstract Frobenius det infrastructure (shipped) reduces to
this single named identity. -/
def MatrixRestrictionToSinnott
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  (2 : ℂ) ^ (p - 3) * ((convolutionMatrixLogNormEven p).det) ^ 2 =
    (quotientEigenvalue p (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)) ^ 2 *
      ((NumberField.Units.regOfFamily
          (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2

/-- **Even-character bijection step (named Prop)**: the
`dirichletOfQuotientChar` map restricts to a bijection between the
nontrivial multiplicative characters of `CyclotomicEvenDelta p` and the
even nontrivial Dirichlet characters mod `p`, identifying the products:

 ∏ ξ ∈ univ.erase 1, DLS p (dirichletOfQuotientChar p ξ) =
 ∏ χ ∈ evenNontrivialCharacters p, DLS p χ.

This is the Pontryagin-duality identification between the dual of
`(ZMod p)ˣ / ⟨-1⟩` and the even-character subgroup of the dual of
`(ZMod p)ˣ`. -/
def QuotientCharBijectionToEvenNontriv : Prop :=
  haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  haveI : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  (∏ ξ ∈ (Finset.univ : Finset
      (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1,
    DirichletLogSum p (dirichletOfQuotientChar p ξ)) =
  ∏ χ ∈ KummerCriterion.evenNontrivialCharacters p, DirichletLogSum p χ

/-- **Proof of `QuotientCharBijectionToEvenNontriv` via cardinality-and-injection**:
for `p` prime with `p > 2` (so `p ≠ 2`), the product equality holds.

Strategy:
1. The map `ξ ↦ dirichletOfQuotientChar p ξ` is injective (shipped).
2. The image of `MulChar.erase 1` under this map lies in `evenNontrivialCharacters`
 (image is even by `dirichletOfQuotientChar_even`; ≠ 1 since `ξ ≠ 1` and
 the map is injective with `dirichletOfQuotientChar_one`).
3. Cardinalities match: both `MulChar.erase 1` and `evenNontrivialCharacters`
 have card `(p-3)/2` (via shipped `nat_card_mulChar_cyclotomicEvenDelta_eq` +
 `cyclotomicEvenDelta_card`, and `card_evenNontrivialCharacters`).
4. Hence the map is a bijection. -/
theorem quotientCharBijectionToEvenNontriv_proof (hp_two : 2 < p) :
    QuotientCharBijectionToEvenNontriv (p := p) := by
  classical
  letI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  change (∏ ξ ∈ (Finset.univ : Finset
        (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1,
      DirichletLogSum p (dirichletOfQuotientChar p ξ)) =
    ∏ χ ∈ KummerCriterion.evenNontrivialCharacters p, DirichletLogSum p χ
  have h_card_mc : Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      (p - 1) / 2 := by
    have h1 : Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
        Nat.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Nat.card_eq_fintype_card.symm
    rw [h1, nat_card_mulChar_cyclotomicEvenDelta_eq p]
    rw [Nat.card_eq_fintype_card]
    exact KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two
  have h_p_odd : Odd p := hp.out.odd_of_ne_two (by omega)
  refine Finset.prod_bij (fun ξ _ => dirichletOfQuotientChar p ξ) ?_ ?_ ?_ ?_
  · intro ξ hξ
    rw [Finset.mem_erase] at hξ
    obtain ⟨hξ_ne, _⟩ := hξ
    rw [KummerCriterion.evenNontrivialCharacters, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact dirichletOfQuotientChar_even p ξ
    · intro h_one
      apply hξ_ne
      have h_eq : dirichletOfQuotientChar p ξ = dirichletOfQuotientChar p 1 := by
        rw [dirichletOfQuotientChar_one]
        exact h_one
      exact dirichletOfQuotientChar_injective p h_eq
  · intro ξ₁ _ ξ₂ _ h
    exact dirichletOfQuotientChar_injective p h
  · intro χ hχ
    have h_card_eq : (KummerCriterion.evenNontrivialCharacters p).card =
        ((Finset.univ : Finset
            (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1).card := by
      rw [KummerCriterion.card_evenNontrivialCharacters (p := p) (by omega)]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
      rw [Finset.card_univ, h_card_mc]
      rcases h_p_odd with ⟨k, hk⟩
      omega
    have h_in : ∀ ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ,
        ξ ∈ (Finset.univ : Finset
              (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1 →
        dirichletOfQuotientChar p ξ ∈ KummerCriterion.evenNontrivialCharacters p := by
      intro ξ hξ
      rw [Finset.mem_erase] at hξ
      obtain ⟨hξ_ne, _⟩ := hξ
      rw [KummerCriterion.evenNontrivialCharacters, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact dirichletOfQuotientChar_even p ξ
      · intro h_one
        apply hξ_ne
        have h_eq : dirichletOfQuotientChar p ξ = dirichletOfQuotientChar p 1 := by
          rw [dirichletOfQuotientChar_one]
          exact h_one
        exact dirichletOfQuotientChar_injective p h_eq
    have h_surj := Finset.surj_on_of_inj_on_of_card_le
      (fun ξ (_ : ξ ∈ _) => dirichletOfQuotientChar p ξ)
      (fun ξ hξ => h_in ξ hξ)
      (fun ξ₁ ξ₂ _ _ h => dirichletOfQuotientChar_injective p h)
      h_card_eq.le χ hχ
    obtain ⟨a, ha_mem, ha_eq⟩ := h_surj
    exact ⟨a, ha_mem, ha_eq.symm⟩
  · intro ξ _
    rfl

/-- **`FrobeniusDetIdentity` from the two named hypotheses**: combining
`MatrixRestrictionToSinnott` (substantive matrix-restriction) and
`QuotientCharBijectionToEvenNontriv` (Pontryagin duality bijection)
with the shipped abstract Frobenius det chain on the quotient,
`FrobeniusDetIdentity` follows. -/
theorem FrobeniusDetIdentity_of_named_hypotheses
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h_matrix : MatrixRestrictionToSinnott (p := p) K hp_odd hp_three)
    (h_bij : QuotientCharBijectionToEvenNontriv (p := p)) :
    FrobeniusDetIdentity (p := p) K hp_odd hp_three := by
  classical
  letI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  letI : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  unfold FrobeniusDetIdentity
  have h_det_sq := det_convolutionMatrixLogNormEven_sq_eq_log_p_sq_mul_nontrivial_DLS_sq
      p hp_two
  unfold MatrixRestrictionToSinnott at h_matrix
  unfold QuotientCharBijectionToEvenNontriv at h_bij
  have h_qe := quotientEigenvalue_trivial_eq_half_log_p p hp_two
  rw [h_qe] at h_matrix
  have h_card : Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      (p - 1) / 2 := by
    have h1 : Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
        Nat.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Nat.card_eq_fintype_card.symm
    rw [h1, nat_card_mulChar_cyclotomicEvenDelta_eq p]
    rw [Nat.card_eq_fintype_card]
    exact KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two
  rw [← prod_evenNontriv_eq_prod_evenNontriv_inv (p := p) (DirichletLogSum p)]
  have h_log_ne : ((Real.log p : ℝ) : ℂ) ≠ 0 := by
    have h_pos : (1 : ℝ) < (p : ℝ) := by
      have : (1 : ℝ) < (2 : ℝ) := by norm_num
      exact lt_of_lt_of_le this (by exact_mod_cast hp_two.le)
    exact_mod_cast (Real.log_pos h_pos).ne'
  rw [h_bij] at h_det_sq
  rw [h_det_sq] at h_matrix
  have h_two_pow_card : (4 : ℂ) ^ Fintype.card
      (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      (2 : ℂ) ^ (p - 1) := by
    rw [h_card]
    rw [show (4 : ℂ) = 2 ^ 2 from by norm_num, ← pow_mul]
    congr 1
    have h_p_odd : Odd p := hp.out.odd_of_ne_two hp_odd
    rcases h_p_odd with ⟨k, hk⟩
    omega
  rw [h_two_pow_card] at h_matrix
  have h_log_sq_ne : (((Real.log p : ℝ) : ℂ)) ^ 2 ≠ 0 := pow_ne_zero _ h_log_ne
  have h_two_ne : ((2 : ℂ) ^ (p - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h_two_ne' : ((2 : ℂ) ^ (p - 3)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h_p_ge : (2 : ℂ) ^ (p - 1) = 4 * (2 : ℂ) ^ (p - 3) := by
    rw [show p - 1 = (p - 3) + 2 from by omega, pow_add]
    ring
  rw [h_p_ge] at h_matrix
  field_simp at h_matrix
  linear_combination -h_matrix / 4

/-- **`FrobeniusDetIdentity` from `MatrixRestrictionToSinnott` alone**: with
the proven `QuotientCharBijectionToEvenNontriv` discharged, reduces to
the SINGLE named hypothesis `MatrixRestrictionToSinnott`. -/
theorem FrobeniusDetIdentity_of_MatrixRestrictionToSinnott
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h_matrix : MatrixRestrictionToSinnott (p := p) K hp_odd hp_three) :
    FrobeniusDetIdentity (p := p) K hp_odd hp_three :=
  FrobeniusDetIdentity_of_named_hypotheses (p := p) K hp_odd hp_three hp_two
    h_matrix
    (quotientCharBijectionToEvenNontriv_proof (p := p) hp_two)

/-- **`KummerDirichletDeterminant` from `MatrixRestrictionToSinnott` alone**:
final compositional theorem reducing (KummerDirichletDeterminant) to the
single substantive hypothesis `MatrixRestrictionToSinnott`. -/
theorem KummerDirichletDeterminant_of_MatrixRestrictionToSinnott
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h_matrix : MatrixRestrictionToSinnott (p := p) K hp_odd hp_three) :
    KummerCriterion.LehmerVandiver.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three :=
  KummerDirichletDeterminant_of_FrobeniusDetIdentity (p := p) K hp_odd hp_three
    (FrobeniusDetIdentity_of_MatrixRestrictionToSinnott (p := p) K hp_odd
      hp_three hp_two h_matrix)

/-- **Cardinality of `InfinitePlace K`**: for K = ℚ(ζ_p) (cyclotomic field of
prime conductor p > 2), the number of infinite places equals `(p-1)/2`.
K is totally complex (CM-field, no real places), so by
`IsTotallyComplex.finrank` we have `finrank ℚ K = 2 · nrComplexPlaces K`.
Combined with `IsCyclotomicExtension.finrank` giving `finrank ℚ K = p - 1`
(totient of prime p), this yields `nrComplexPlaces = (p-1)/2`. -/
theorem fintype_card_InfinitePlace_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsTotallyComplex K] (_hp_two : 2 < p) :
    Fintype.card (NumberField.InfinitePlace K) = (p - 1) / 2 := by
  classical
  haveI : Fact (Nat.Prime p) := hp
  have h_finrank_eq : Module.finrank ℚ K = p - 1 := by
    have : Module.finrank ℚ K = (p : ℕ).totient :=
      IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.out.pos)
    rw [this, Nat.totient_prime hp.out]
  have h_totally_complex := NumberField.IsTotallyComplex.finrank K
  rw [h_finrank_eq] at h_totally_complex
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  rw [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (K := K), zero_add]
  omega

/-- **K-place ↔ CyclotomicEvenDelta bijection**: for K = ℚ(ζ_p) cyclotomic
totally complex, there is a non-canonical bijection between infinite places
of K and elements of `CyclotomicEvenDelta p`, both of cardinality `(p-1)/2`.
This is the Pontryagin-cardinality-based existence statement; the canonical
bijection comes from the Galois orbit-stabilizer correspondence (orbits of
the (ZMod p)ˣ-action with stabilizer ⟨-1⟩). -/
noncomputable def InfinitePlaceEquivCyclotomicEvenDelta
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsTotallyComplex K] (hp_two : 2 < p) :
    NumberField.InfinitePlace K ≃ KummerCriterion.CyclotomicEvenDelta p := by
  classical
  refine Fintype.equivOfCardEq ?_
  rw [fintype_card_InfinitePlace_eq (p := p) K hp_two]
  rw [KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two]

/-- **K⁺-place ↔ CyclotomicEvenDelta bijection**: composing the mathlib
`NumberField.IsCMField.equivInfinitePlace` (K-places ↔ K⁺-places) with
the K-place bijection gives the K⁺-place bijection. This is the actual
bijection used to index the Sinnott log-embedding matrix in
`CyclotomicEvenDelta` form. -/
noncomputable def KplusInfinitePlaceEquivCyclotomicEvenDelta
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    NumberField.InfinitePlace (NumberField.maximalRealSubfield K) ≃
      KummerCriterion.CyclotomicEvenDelta p :=
  (NumberField.IsCMField.equivInfinitePlace K).symm.trans
    (InfinitePlaceEquivCyclotomicEvenDelta (p := p) K hp_two)

/-- **Sinnott matrix-entry decomposition wrapper**: gives the matrix `M_Sinnott[i, w]`
in the form `2 (log w_K(ζ^(idx_i+2) - 1) - log w_K(ζ - 1))`.

The K⁺-side cyclotomic-unit log-embedding matrix
`regOfFamily_cyclotomicUnitFamilyKplus_eq_det` has entries decomposed by
`log_realCyclotomicUnit_at_Kplus_place_eq_sub_decomp` (per-entry). This is
the matrix-level wrapper: every entry follows the per-entry decomposition.
The second term `2 log w_K(ζ - 1)` is **column-constant** — independent of
the row index `i` — which is the key structural fact for the matrix
restriction step: row operations cancel the column-constant part.

This is a structural step toward `MatrixRestrictionToSinnott`. -/
theorem sinnottMatrix_entry_decomp
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    Real.log
        (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
          ((LehmerVandiver.realCyclotomicUnit p K
            ((((NumberField.Units.equivFinRank
                (NumberField.maximalRealSubfield K)).symm i).cast
              ((NumberField.IsCMField.units_rank_eq_units_rank
                  (K := K)).trans
                (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                  (p := p) (K := K)))) + 2) : 𝓞 K) : K)) =
      2 * Real.log
            (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
              (((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' :
                  (𝓞 K)ˣ) : 𝓞 K) : K) ^
                (((((NumberField.Units.equivFinRank
                    (NumberField.maximalRealSubfield K)).symm i).cast
                  ((NumberField.IsCMField.units_rank_eq_units_rank
                      (K := K)).trans
                    (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                      (p := p) (K := K)))) + 2 : ℕ)) - 1)) -
        2 * Real.log
            (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
              ((((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' :
                  (𝓞 K)ˣ) : 𝓞 K) : K)) - 1)) := by
  set k_idx : ℕ := ((((NumberField.Units.equivFinRank
              (NumberField.maximalRealSubfield K)).symm i).cast
            ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2 : ℕ) with hk_idx
  have h_idx_coprime : k_idx.Coprime p := by
    have h_p_prime : Nat.Prime p := hp.out
    rw [Nat.coprime_comm, h_p_prime.coprime_iff_not_dvd]
    intro h_dvd
    have h_p_odd : Odd p := h_p_prime.odd_of_ne_two hp_odd
    rcases h_p_odd with ⟨k, hk⟩
    have h_fin_lt :
        (((NumberField.Units.equivFinRank
            (NumberField.maximalRealSubfield K)).symm i).cast
              ((NumberField.IsCMField.units_rank_eq_units_rank
                  (K := K)).trans
                (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                  (p := p) (K := K)))).val < (p - 3) / 2 :=
      Fin.isLt _
    have h_lt_p : k_idx < p := by
      change ((((NumberField.Units.equivFinRank
                (NumberField.maximalRealSubfield K)).symm i).cast _) + 2 : ℕ) < p
      omega
    have h_pos : 0 < k_idx := by
      change 0 < ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast _) + 2 : ℕ)
      omega
    have := Nat.le_of_dvd h_pos h_dvd
    omega
  have h_p_ge_two : 2 ≤ p := by omega
  exact log_realCyclotomicUnit_at_Kplus_place_eq_sub_decomp (p := p) (K := K)
    k_idx h_idx_coprime h_p_ge_two w.val

/-- **Sinnott `A`-matrix**: the `i,w`-dependent part of the Sinnott
log-embedding matrix. `A[i, w] = log w_K((ζ_K^(idx_i+2)) - 1)`. -/
noncomputable def sinnottMatrixA
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    Matrix {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℝ :=
  Matrix.of fun i w =>
    Real.log
      (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
        (((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' :
            (𝓞 K)ˣ) : 𝓞 K) : K) ^
          (((((NumberField.Units.equivFinRank
              (NumberField.maximalRealSubfield K)).symm i).cast
            ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2 : ℕ)) - 1))

/-- **Sinnott `B`-matrix**: the column-constant part of the Sinnott
log-embedding matrix. `B[i, w] = log w_K(ζ_K - 1)` — depends only on the
column `w`, not on the row `i`. This is the **rank-1 fact**: the rows
of `B` are all identical.

(Strictly, the rank may be 0 if the row vector is identically zero, but
its zero-ness is not used in the determinant analysis.) -/
noncomputable def sinnottMatrixB
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    Matrix {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℝ :=
  Matrix.of fun (_ : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) w =>
    Real.log
      (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
        ((((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' :
            (𝓞 K)ˣ) : 𝓞 K) : K)) - 1))

/-- **Sinnott matrix as `2·A - 2·B`**: the matrix-level decomposition
of the Sinnott log-embedding matrix
`regOfFamily_cyclotomicUnitFamilyKplus_eq_det`.

 `M_Sinnott = 2 · sinnottMatrixA - 2 · sinnottMatrixB`

where `sinnottMatrixA` is the `(i, w)`-dependent part and
`sinnottMatrixB` is the column-constant part. This is the matrix-form
lift of `sinnottMatrix_entry_decomp`. -/
theorem sinnottMatrix_eq_two_A_sub_two_B
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((LehmerVandiver.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))) =
      (2 : ℝ) • sinnottMatrixA p K - (2 : ℝ) • sinnottMatrixB p K := by
  ext i w
  simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    sinnottMatrixA, sinnottMatrixB]
  exact sinnottMatrix_entry_decomp p K hp_odd hp_three i w

/-- **Sinnott matrix as `2 · (A - B)`**: factored form. The Sinnott
log-embedding matrix equals `2 · (sinnottMatrixA - sinnottMatrixB)`,
which lets us pull the factor of `2` out for determinant evaluation. -/
theorem sinnottMatrix_eq_two_smul_A_sub_B
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((LehmerVandiver.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))) =
      (2 : ℝ) • (sinnottMatrixA p K - sinnottMatrixB p K) := by
  rw [sinnottMatrix_eq_two_A_sub_two_B p K hp_odd hp_three]
  rw [smul_sub]

/-- **`convolutionLogNormDescended` at the `q(a)` quotient class**: the descended
log-norm function evaluated at the quotient class of a unit `a` equals the
explicit ℝ-cast `log‖1 - stdAddChar(↑a)‖`. Direct
`evenFunctionDescend_apply_mk` for the cyclotomic-unit log-norm. -/
theorem convolutionLogNormDescended_apply_quotient
    (a : KummerCriterion.CyclotomicUnitDelta p) :
    convolutionLogNormDescended p
        (KummerCriterion.cyclotomicEvenDeltaQuotient p a) =
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) := by
  unfold convolutionLogNormDescended
  rw [show KummerCriterion.cyclotomicEvenDeltaQuotient p a = QuotientGroup.mk a from rfl]
  rw [KummerCriterion.evenFunctionDescend_apply_mk]

/-- **Squared det = qe(1)² · (∏ ξ≠1 qe(ξ))² (reformulation)**:
extracting the trivial-character eigenvalue factor
`det_convolutionMatrixLogNormEven_sq_eq_prod_quotientEigenvalue_sq`.

This is the trivial-extracted form: `det²(M_even) = qe(1)² · (∏_{ξ≠1} qe(ξ))²`.
It exhibits the substantive matrix-restriction content as
`regOfFamily² = (∏_{ξ ≠ 1} qe(ξ))²` — the eigenvalue identification that
completes `MatrixRestrictionToSinnott`. -/
theorem det_convolutionMatrixLogNormEven_sq_eq_qe_one_sq_mul_prod_nontrivial_qe_sq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    haveI : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Classical.decEq _
    (convolutionMatrixLogNormEven p).det ^ 2 =
      quotientEigenvalue p (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) ^ 2 *
        (∏ ξ ∈ (Finset.univ : Finset
            (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1,
          quotientEigenvalue p ξ) ^ 2 := by
  classical
  letI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  letI : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  rw [det_convolutionMatrixLogNormEven_sq_eq_prod_quotientEigenvalue_sq p hp_two]
  rw [← Finset.prod_pow]
  rw [prod_quot_eq_prod_mulChar p (fun ξ => (quotientEigenvalue p ξ) ^ 2)]
  rw [Finset.prod_pow]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ
    (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ))]
  ring

end Sinnott

end LehmerVandiver

end KummerCriterion

end
