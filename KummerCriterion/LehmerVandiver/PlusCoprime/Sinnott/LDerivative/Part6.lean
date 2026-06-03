module

public import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part5
import KummerCriterion.UnitQuotient.FreeCharacterProfile

@[expose] public section

noncomputable section

open Real Complex
open scoped NumberField

namespace KummerCriterion

namespace LehmerVandiver

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

/-- **`q(familyIndexAsUnit i) ≠ 1`** in `CyclotomicEvenDelta p`. Direct
`familyIndexAsUnit_ne_one_and_neg_one`: q-equality with 1 means the unit
itself is in `⟨-1⟩ = {1, -1}`. -/
theorem familyIndexAsUnit_quotient_ne_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    KummerCriterion.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i) ≠ 1 := by
  classical
  intro h
  have h_mem : familyIndexAsUnit p K hp_odd hp_three i ∈
      KummerCriterion.CyclotomicEvenDeltaSubgroup p := by
    rw [← QuotientGroup.eq_one_iff]
    exact h
  rw [KummerCriterion.CyclotomicEvenDeltaSubgroup, Subgroup.mem_zpowers_iff] at h_mem
  obtain ⟨k, hk⟩ := h_mem
  have h_sq : ((-1 : KummerCriterion.CyclotomicUnitDelta p)) ^ (2 : ℕ) = 1 := by
    rw [sq, neg_one_mul, neg_neg]
  rw [zpow_eq_zpow_emod' k h_sq] at hk
  have h_mod : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  obtain ⟨h_ne_one, h_ne_neg_one⟩ :=
    familyIndexAsUnit_ne_one_and_neg_one (p := p) K hp_odd hp_three hp_ge_five i
  rcases h_mod with h0 | h1
  · rw [h0, zpow_zero] at hk
    exact h_ne_one hk.symm
  · rw [h1, zpow_one] at hk
    exact h_ne_neg_one hk.symm

/-- **`familyIndexAsUnit` is injective**: distinct family indices give
distinct `(ZMod p)ˣ` units.

Reason: the underlying ZMod p-value of `familyIndexAsUnit i` is `idx_i + 2`,
which is determined by the family index `i`. -/
theorem familyIndexAsUnit_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Function.Injective (familyIndexAsUnit p K hp_odd hp_three) := by
  classical
  intro i₁ i₂ h_eq
  have h_val_eq : ((familyIndexAsUnit p K hp_odd hp_three i₁ : (ZMod p)ˣ) : ZMod p).val =
      ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val := by
    rw [h_eq]
  have h_p_prime : Nat.Prime p := hp.out
  have h_p_odd : Odd p := h_p_prime.odd_of_ne_two hp_odd
  rcases h_p_odd with ⟨n, hn⟩
  set j₁ : Fin ((p - 3) / 2) :=
    (((NumberField.Units.equivFinRank
        (NumberField.maximalRealSubfield K)).symm i₁).cast
      ((NumberField.IsCMField.units_rank_eq_units_rank
          (K := K)).trans
        (KummerCriterion.units_rank_eq_prime_sub_three_div_two
          (p := p) (K := K)))) with hj₁_def
  set j₂ : Fin ((p - 3) / 2) :=
    (((NumberField.Units.equivFinRank
        (NumberField.maximalRealSubfield K)).symm i₂).cast
      ((NumberField.IsCMField.units_rank_eq_units_rank
          (K := K)).trans
        (KummerCriterion.units_rank_eq_prime_sub_three_div_two
          (p := p) (K := K)))) with hj₂_def
  have h_j₁_lt : j₁.val < (p - 3) / 2 := Fin.isLt _
  have h_j₂_lt : j₂.val < (p - 3) / 2 := Fin.isLt _
  have h_lt_p₁ : j₁.val + 2 < p := by omega
  have h_lt_p₂ : j₂.val + 2 < p := by omega
  have h_v1 : ((familyIndexAsUnit p K hp_odd hp_three i₁ : (ZMod p)ˣ) : ZMod p).val =
      j₁.val + 2 := by
    have h_v_spec := familyIndexAsUnit_val (p := p) K hp_odd hp_three i₁
    rw [h_v_spec, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt h_lt_p₁
  have h_v2 : ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val =
      j₂.val + 2 := by
    have h_v_spec := familyIndexAsUnit_val (p := p) K hp_odd hp_three i₂
    rw [h_v_spec, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt h_lt_p₂
  rw [h_v1, h_v2] at h_val_eq
  have h_fin_eq : j₁.val = j₂.val := by omega
  have h_fin : j₁ = j₂ := Fin.ext h_fin_eq
  have h_symm_eq : (NumberField.Units.equivFinRank
      (NumberField.maximalRealSubfield K)).symm i₁ =
      (NumberField.Units.equivFinRank
        (NumberField.maximalRealSubfield K)).symm i₂ := by
    have h_val_symm : (((NumberField.Units.equivFinRank
          (NumberField.maximalRealSubfield K)).symm i₁) : ℕ) =
        (((NumberField.Units.equivFinRank
          (NumberField.maximalRealSubfield K)).symm i₂) : ℕ) := h_fin_eq
    exact Fin.ext h_val_symm
  exact (NumberField.Units.equivFinRank
      (NumberField.maximalRealSubfield K)).symm.injective h_symm_eq

/-- **`q ∘ familyIndexAsUnit` is injective**: distinct family indices give
distinct quotient elements in `CyclotomicEvenDelta p`.

Reason: `familyIndexAsUnit i` has value in `[2, (p-1)/2]` as a `ZMod p`
element. Negating sends this to `[(p+1)/2, p-2]` (the val of `-a` is `p - val(a)`),
which is disjoint from `[2, (p-1)/2]` for `p ≥ 5`. So
`familyIndexAsUnit i₁ ≠ -familyIndexAsUnit i₂`. Combined with
`familyIndexAsUnit_injective`, the composite `q ∘ familyIndexAsUnit` is
injective. -/
theorem familyIndexAsUnit_quotient_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) :
    Function.Injective (fun i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =>
      KummerCriterion.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i)) := by
  classical
  intro i₁ i₂ h_eq
  simp only at h_eq
  have h_div : familyIndexAsUnit p K hp_odd hp_three i₁ /
      familyIndexAsUnit p K hp_odd hp_three i₂ ∈
      KummerCriterion.CyclotomicEvenDeltaSubgroup p :=
    QuotientGroup.eq_iff_div_mem.mp h_eq
  rw [div_eq_mul_inv, KummerCriterion.CyclotomicEvenDeltaSubgroup,
      Subgroup.mem_zpowers_iff] at h_div
  obtain ⟨k, hk⟩ := h_div
  have h_sq : ((-1 : KummerCriterion.CyclotomicUnitDelta p)) ^ (2 : ℕ) = 1 := by
    rw [sq, neg_one_mul, neg_neg]
  rw [zpow_eq_zpow_emod' k h_sq] at hk
  have h_mod : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  obtain ⟨h_ge_one, h_le_one⟩ := familyIndexAsUnit_val_in_range
    (p := p) K hp_odd hp_three i₁
  obtain ⟨h_ge_two, h_le_two⟩ := familyIndexAsUnit_val_in_range
    (p := p) K hp_odd hp_three i₂
  rcases h_mod with h0 | h1
  · -- Case 1: a₁ * a₂⁻¹ = 1. So a₁ = a₂, hence i₁ = i₂.
    rw [h0, zpow_zero] at hk
    have h_a_eq : familyIndexAsUnit p K hp_odd hp_three i₁ =
        familyIndexAsUnit p K hp_odd hp_three i₂ := by
      have : familyIndexAsUnit p K hp_odd hp_three i₁ *
          (familyIndexAsUnit p K hp_odd hp_three i₂)⁻¹ *
            familyIndexAsUnit p K hp_odd hp_three i₂ =
          1 * familyIndexAsUnit p K hp_odd hp_three i₂ := by rw [hk]
      rwa [inv_mul_cancel_right, one_mul] at this
    exact familyIndexAsUnit_injective (p := p) K hp_odd hp_three h_a_eq
  · -- Case 2: a₁ * a₂⁻¹ = -1. So a₁ = -a₂. But val(a₁), val(a₂) ∈ [2, (p-1)/2],
    rw [h1, zpow_one] at hk
    have h_neg : familyIndexAsUnit p K hp_odd hp_three i₁ =
        -familyIndexAsUnit p K hp_odd hp_three i₂ := by
      have : familyIndexAsUnit p K hp_odd hp_three i₁ *
          (familyIndexAsUnit p K hp_odd hp_three i₂)⁻¹ *
            familyIndexAsUnit p K hp_odd hp_three i₂ =
          -1 * familyIndexAsUnit p K hp_odd hp_three i₂ := by rw [hk]
      rwa [inv_mul_cancel_right, neg_one_mul] at this
    have h_p_prime : Nat.Prime p := hp.out
    haveI : NeZero p := ⟨h_p_prime.ne_zero⟩
    haveI : NeZero ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p) := by
      refine ⟨?_⟩
      intro h_zero
      rw [show ((((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p)).val) = 0 from
        by rw [h_zero]; exact ZMod.val_zero] at h_ge_two
      omega
    have h_v_eq : ((familyIndexAsUnit p K hp_odd hp_three i₁ : (ZMod p)ˣ) : ZMod p).val =
        ((-familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val := by
      rw [h_neg]
    have h_v_neg : ((-familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val =
        p - ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val := by
      change ((-((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p))).val =
        p - ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val
      exact ZMod.val_neg_of_ne_zero _
    rw [h_v_neg] at h_v_eq
    omega

/-- **Row-side bijection** (cardinality form): the family-index set
`{w_K⁺ // w ≠ w₀}` bijects to `{c: CyclotomicEvenDelta p // c ≠ 1}`.

Both have cardinality `(p-3)/2`. Established via `Fintype.equivOfCardEq` after
proving the cardinality equality via the canonical embedding-index bijection. -/
noncomputable def familyIndexEquivNonTrivialCE
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (_hp_odd : p ≠ 2) (_hp_three : 3 ≤ p)
    (hp_two : 2 < p) :
    {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      {c : KummerCriterion.CyclotomicEvenDelta p // c ≠ 1} := by
  classical
  refine Fintype.equivOfCardEq ?_
  have h_bij : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) ≃
      KummerCriterion.CyclotomicEvenDelta p :=
    KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical
      (p := p) K hp_two
  rw [Fintype.card_subtype_compl (p := fun w =>
    w = NumberField.Units.dirichletUnitTheorem.w₀)]
  rw [Fintype.card_subtype_compl (p := fun c => c = 1)]
  rw [Fintype.card_congr h_bij]
  rfl

/-- **Row-side bijection bundle** (functional form): for each family-index `i`,
`q(familyIndexAsUnit i)` lies in `{c: CyclotomicEvenDelta p // c ≠ 1}`.

Packages `familyIndexAsUnit_quotient_ne_one` into a function with codomain
restricted to the non-trivial subtype. -/
noncomputable def familyIndexAsCEnotOne
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    {c : KummerCriterion.CyclotomicEvenDelta p // c ≠ 1} :=
  ⟨KummerCriterion.cyclotomicEvenDeltaQuotient p
      (familyIndexAsUnit p K hp_odd hp_three i),
    familyIndexAsUnit_quotient_ne_one (p := p) K hp_odd hp_three hp_ge_five i⟩

/-- **`familyIndexAsCEnotOne` is injective**: bundles
`familyIndexAsUnit_quotient_injective` into the subtype codomain form. -/
theorem familyIndexAsCEnotOne_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) :
    Function.Injective (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five) := by
  intro i₁ i₂ h_eq
  have h_eq_val : (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five i₁).val =
      (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five i₂).val := by
    rw [h_eq]
  exact familyIndexAsUnit_quotient_injective (p := p) K hp_odd hp_three hp_ge_five h_eq_val

/-- **Row-side bijection** as an `Equiv` via `familyIndexAsCEnotOne`.

Bundles `familyIndexAsCEnotOne_injective` + cardinality equality
(`familyIndexEquivNonTrivialCE`) into a noncomputable `Equiv`
the family-index set to `{c: CyclotomicEvenDelta p // c ≠ 1}`. -/
noncomputable def familyIndexAsCEnotOneEquiv
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) (hp_two : 2 < p) :
    {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      {c : KummerCriterion.CyclotomicEvenDelta p // c ≠ 1} := by
  classical
  refine Equiv.ofBijective
    (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five) ?_
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨familyIndexAsCEnotOne_injective (p := p) K hp_odd hp_three hp_ge_five, ?_⟩
  exact Fintype.card_congr
    (familyIndexEquivNonTrivialCE (p := p) K hp_odd hp_three hp_two)

/-- **Specification of `familyIndexAsCEnotOneEquiv`**: the apply value
unwraps to `q(familyIndexAsUnit i)`. -/
@[simp]
theorem familyIndexAsCEnotOneEquiv_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) (hp_two : 2 < p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (familyIndexAsCEnotOneEquiv (p := p) K hp_odd hp_three hp_ge_five hp_two i).val =
      KummerCriterion.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i) :=
  rfl

/-- **Cardinality of `{c: CyclotomicEvenDelta p // c ≠ 1}`** equals `(p-3)/2`.

Direct from `Fintype.card_subtype_compl` + `cyclotomicEvenDelta_card`. -/
theorem fintype_card_nonTrivialCE_eq (hp_two : 2 < p) :
    Fintype.card {c : KummerCriterion.CyclotomicEvenDelta p // c ≠ 1} =
      (p - 1) / 2 - 1 := by
  classical
  rw [Fintype.card_subtype_compl (p := fun c => c = 1)]
  rw [KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two]
  rw [Fintype.card_subtype_eq]

/-- **Shifted K⁺-place embedding-index quotient**: divides
`kplusEmbeddingIndexQuotient` by `kplusEmbeddingIndexQuotient w₀`, so that
the distinguished place `w₀` maps to `1` in `CyclotomicEvenDelta p`.

Useful for matrix-level reindexing where one wants the excluded "base"
column to correspond to the identity element of `CyclotomicEvenDelta p`. -/
noncomputable def kplusEmbeddingIndexQuotientShifted
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (v : NumberField.InfinitePlace (NumberField.maximalRealSubfield K)) :
    KummerCriterion.CyclotomicEvenDelta p :=
  kplusEmbeddingIndexQuotient (p := p) K v *
    (kplusEmbeddingIndexQuotient (p := p) K
      NumberField.Units.dirichletUnitTheorem.w₀)⁻¹

/-- **Shifted quotient sends `w₀` to `1`**. -/
@[simp]
theorem kplusEmbeddingIndexQuotientShifted_w₀
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    kplusEmbeddingIndexQuotientShifted (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀ = 1 := by
  unfold kplusEmbeddingIndexQuotientShifted
  exact mul_inv_cancel _

/-- **Shifted quotient is a bijection**: the shifted version of the K⁺-place
embedding-index quotient is also a bijection `InfinitePlace K⁺ ≃
CyclotomicEvenDelta p`. Multiplication by `k(w₀)⁻¹` is a group bijection
(an `Equiv` of CE with itself), so the composition with the bijective
`kplusEmbeddingIndexQuotient` is a bijection. -/
theorem kplusEmbeddingIndexQuotientShifted_bijective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    Function.Bijective (kplusEmbeddingIndexQuotientShifted (p := p) K) := by
  classical
  set kw₀_inv : KummerCriterion.CyclotomicEvenDelta p :=
    (kplusEmbeddingIndexQuotient (p := p) K
      NumberField.Units.dirichletUnitTheorem.w₀)⁻¹ with h_kw₀_inv
  have h_mul_bij : Function.Bijective
      (fun c : KummerCriterion.CyclotomicEvenDelta p => c * kw₀_inv) :=
    Group.mulRight_bijective kw₀_inv
  exact h_mul_bij.comp (kplusEmbeddingIndexQuotient_bijective (p := p) K hp_two)

/-- **Shifted K⁺-place ↔ CyclotomicEvenDelta p Equiv**: bundles the shifted
bijection that sends `w₀ → 1` into a noncomputable `Equiv`. -/
noncomputable def KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    NumberField.InfinitePlace (NumberField.maximalRealSubfield K) ≃
      KummerCriterion.CyclotomicEvenDelta p :=
  Equiv.ofBijective (kplusEmbeddingIndexQuotientShifted (p := p) K)
    (kplusEmbeddingIndexQuotientShifted_bijective (p := p) K hp_two)

/-- **Shifted Apply at `w₀`**: the shifted bijection at the distinguished
place `w₀` gives `1` (the identity element of `CyclotomicEvenDelta p`). -/
@[simp]
theorem KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted_apply_w₀
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted (p := p) K hp_two
        NumberField.Units.dirichletUnitTheorem.w₀ = 1 :=
  kplusEmbeddingIndexQuotientShifted_w₀ (p := p) K

end Sinnott

end LehmerVandiver

end KummerCriterion

end
