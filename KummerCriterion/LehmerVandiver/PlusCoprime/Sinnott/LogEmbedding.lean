module

public import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitFamily
public import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.PollaczekFamilyDescent
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Logarithmic embedding of cyclotomic-unit family elements

For the K⁺-side cyclotomic-unit family, we compute the logarithmic
embedding `logEmbedding K⁺: (𝓞 K⁺)ˣ → logSpace K⁺` explicitly.

For totally real K⁺, all infinite places are real (`mult w = 1`), so

 `logEmbedding K⁺ (family j) w = Real.log (w (family j))`

for `w: InfinitePlace K⁺` with `w ≠ w₀` (the distinguished place).

This file is **LV-SIN-A** of the Cor 8.19 / Sinnott bridge construction.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField NumberField.InfinitePlace

namespace KummerCriterion

namespace LehmerVandiver

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- For totally real `K⁺`, the multiplicity of any infinite place is `1`. -/
theorem mult_eq_one_of_maximalRealSubfield (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    mult w = 1 := by
  rw [mult]
  simp [IsTotallyReal.isReal w]

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- The logarithmic embedding of a unit `u: (𝓞 K⁺)ˣ` at a non-distinguished
infinite place `w` is just `Real.log (w u)`, since `mult w = 1`
totally real K⁺. -/
theorem logEmbedding_apply_maximalRealSubfield
    (u : (𝓞 (NumberField.maximalRealSubfield K))ˣ)
    (w : {w : InfinitePlace (NumberField.maximalRealSubfield K) //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    NumberField.Units.logEmbedding (NumberField.maximalRealSubfield K)
        (Additive.ofMul u) w =
      Real.log (w.val (u : NumberField.maximalRealSubfield K)) := by
  rw [NumberField.Units.dirichletUnitTheorem.logEmbedding_component]
  rw [mult_eq_one_of_maximalRealSubfield (K := K)]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- For the cyclotomic-unit family element `cyclotomicUnitFamilyKplusFinRank j`,
the value of an infinite place `w` of K⁺ on this element factors through
algebraMap to K. -/
theorem infinitePlace_cyclotomicUnitFamilyKplus_eq
    (j : Fin (NumberField.Units.rank
        (NumberField.maximalRealSubfield K)))
    (w : InfinitePlace (NumberField.maximalRealSubfield K))
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    w ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
        (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
        NumberField.maximalRealSubfield K) =
      ((NumberField.IsCMField.equivInfinitePlace K).symm w)
        (algebraMap (NumberField.maximalRealSubfield K) K
          ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
            (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
            NumberField.maximalRealSubfield K)) := by
  rw [NumberField.IsCMField.equivInfinitePlace_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The value of an infinite place of K⁺ on `cyclotomicUnitFamilyKplus j`
equals the value of the corresponding place of K on `realCyclotomicUnit (j+2)`. -/
theorem infinitePlace_cyclotomicUnitFamilyKplus_eq_realCyclotomicUnit
    (j : Fin (NumberField.Units.rank
        (NumberField.maximalRealSubfield K)))
    (w : InfinitePlace (NumberField.maximalRealSubfield K))
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    w ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
        (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
        NumberField.maximalRealSubfield K) =
      ((NumberField.IsCMField.equivInfinitePlace K).symm w)
        ((LehmerVandiver.realCyclotomicUnit p K
          ((j.cast ((NumberField.IsCMField.units_rank_eq_units_rank
              (K := K)).trans
            (KummerCriterion.units_rank_eq_prime_sub_three_div_two
              (p := p) (K := K)))) + 2) : 𝓞 K) : K) := by
  rw [infinitePlace_cyclotomicUnitFamilyKplus_eq]
  congr 1
  have h := algebraMap_cyclotomicUnitFamilyKplus p K j hp_odd hp_three
  rw [← IsScalarTower.algebraMap_apply
    (𝓞 (NumberField.maximalRealSubfield K)) (NumberField.maximalRealSubfield K) K]
  rw [IsScalarTower.algebraMap_apply
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) K]
  rw [h]

set_option backward.isDefEq.respectTransparency false in
/-- The log embedding of `cyclotomicUnitFamilyKplus j` at place `w` of K⁺
equals `Real.log (w'(realCyclotomicUnit (j+2)))` where `w'` is the
corresponding place of K. -/
theorem logEmbedding_cyclotomicUnitFamilyKplus_apply
    (j : Fin (NumberField.Units.rank
        (NumberField.maximalRealSubfield K)))
    (w : {w : InfinitePlace (NumberField.maximalRealSubfield K) //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    NumberField.Units.logEmbedding (NumberField.maximalRealSubfield K)
        (Additive.ofMul (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j)) w =
      Real.log
        (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
          ((LehmerVandiver.realCyclotomicUnit p K
            ((j.cast ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2) : 𝓞 K) : K)) := by
  rw [logEmbedding_apply_maximalRealSubfield (K := K)]
  congr 1
  exact infinitePlace_cyclotomicUnitFamilyKplus_eq_realCyclotomicUnit p K j w.val hp_odd hp_three

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- The log-embedding matrix of `cyclotomicUnitFamilyKplusFinRank` has
entries given by `Real.log (w' (realCyclotomicUnit (j+2)))` where `w'`
is the K-side place. The matrix is square: rows and columns both
indexed by `{w: InfinitePlace K⁺ // w ≠ w₀}` (places of K⁺ excluding w₀).
The "row place" determines which family element via `equivFinRank.symm`. -/
theorem regOfFamily_cyclotomicUnitFamilyKplus_eq_det
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
      |(Matrix.of fun (i : {w : InfinitePlace (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (w : {w : InfinitePlace (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((LehmerVandiver.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))).det| := by
  letI : DecidableEq {w : InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := Classical.decEq _
  rw [NumberField.Units.regOfFamily_eq_det']
  congr 1
  congr 1
  funext i
  funext w
  simp only [Matrix.of_apply]
  exact logEmbedding_cyclotomicUnitFamilyKplus_apply p K
    ((NumberField.Units.equivFinRank (NumberField.maximalRealSubfield K)).symm i)
    w hp_odd hp_three

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **helper.** Multiplicativity of `w` applied to
`zeta_sub_one_mul_cyclotomicUnit`. -/
theorem norm_cyclotomicUnit_mul_zeta_sub_one (k : ℕ) (w : InfinitePlace K) :
    w ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K) *
        w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1) =
      w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) ^ k - 1) := by
  rw [mul_comm, ← map_mul]
  congr 1
  exact_mod_cast LehmerVandiver.zeta_sub_one_mul_cyclotomicUnit p K k

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **helper (zeta - 1 nonzero).** For p ≥ 2 (i.e., any prime p),
the K-element `ζ - 1` is non-zero. -/
theorem zeta_sub_one_ne_zero_K (hp_two : 2 ≤ p) :
    ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1) ≠ 0 := by
  intro h
  have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  have h_OK_zero : ((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) - 1 = 0 :=
    h_inj (by simpa [map_sub, map_one] using h)
  exact (IsCyclotomicExtension.zeta_spec p ℚ K).unit'_coe.sub_one_ne_zero (by omega) h_OK_zero

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **helper (cyclotomicUnit nonzero in K).** For `k` coprime to
`p` and `p ≥ 2`, `cyclotomicUnit p K k` is non-zero in K.

Direct from `isUnit_cyclotomicUnit` (unit is non-zero) +
algebraMap-of-nonzero is non-zero. -/
theorem cyclotomicUnit_ne_zero_K
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K) ≠ 0 := by
  have hU := LehmerVandiver.isUnit_cyclotomicUnit p K k hk hp_two
  intro h
  apply hU.ne_zero
  have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  exact h_inj (by simpa using h)

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **helper (log form).** From the product identity
`w(cyclotomicUnit k) · w(ζ - 1) = w(ζ^k - 1)`:
`log w(cyclotomicUnit k) = log w(ζ^k - 1) - log w(ζ - 1)`.

Requires `k.Coprime p` and `p ≥ 2` so that `cyclotomicUnit k` is a
unit (hence non-zero in K). The non-zero condition for `ζ - 1`
is shipped as `zeta_sub_one_ne_zero_K`. -/
theorem log_norm_cyclotomicUnit_eq_sub
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) (w : InfinitePlace K) :
    Real.log (w ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K)) =
      Real.log
        (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) ^ k - 1)) -
        Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1)) := by
  have h_w_cycU : w ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K) ≠ 0 := by
    refine (InfinitePlace.pos_iff.mpr ?_).ne'
    exact cyclotomicUnit_ne_zero_K p K k hk hp_two
  have h_w_zsub :
      w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1) ≠ 0 := by
    refine (InfinitePlace.pos_iff.mpr ?_).ne'
    exact zeta_sub_one_ne_zero_K p K hp_two
  have h_prod := norm_cyclotomicUnit_mul_zeta_sub_one p K k w
  have h_log_prod : Real.log (w ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K)) +
      Real.log
        (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1)) =
        Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) ^ k - 1)) := by
    rw [← Real.log_mul h_w_cycU h_w_zsub, h_prod]
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- **Real.** `Real.log (w (realCyclotomicUnit k)) =
2 · Real.log (w (cyclotomicUnit k))` for any infinite place `w` of K.

Proof: σ-symmetrization + `infinitePlace_complexConj` + `Real.log_pow`. -/
theorem log_infinitePlace_realCyclotomicUnit
    (k : ℕ) (w : InfinitePlace K) :
    Real.log (w ((LehmerVandiver.realCyclotomicUnit p K k : 𝓞 K) : K)) =
      2 * Real.log (w ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K)) := by
  have h_eq : ((LehmerVandiver.realCyclotomicUnit p K k : 𝓞 K) : K) =
      ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K) *
        complexConj K ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K) := by
    unfold LehmerVandiver.realCyclotomicUnit
    push_cast
    rw [← coe_ringOfIntegersComplexConj]
  rw [h_eq, map_mul, infinitePlace_complexConj, ← sq, Real.log_pow]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- **MatrixDecomp (per-entry form).** Combining Real
(`log_infinitePlace_realCyclotomicUnit`) with log
(`log_norm_cyclotomicUnit_eq_sub`):
`log w(realCyclotomicUnit k) = 2 · log w(ζ^k - 1) - 2 · log w(ζ - 1)`.

This is the per-entry form of the matrix decomposition `M = 2·A - 2·B`
for the log-embedding matrix of `cyclotomicUnitFamilyKplus`. -/
theorem log_realCyclotomicUnit_eq_sub_decomp
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) (w : InfinitePlace K) :
    Real.log (w ((LehmerVandiver.realCyclotomicUnit p K k : 𝓞 K) : K)) =
      2 * Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) ^ k - 1)) -
        2 * Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1)) := by
  rw [log_infinitePlace_realCyclotomicUnit, log_norm_cyclotomicUnit_eq_sub p K k hk hp_two w]
  ring

/-- **MatrixDecomp at K⁺-places.** The per-entry decomposition
specialised to K⁺-places (the column index of the
`cyclotomicUnitFamilyKplusFinRank` log-embedding matrix). -/
theorem log_realCyclotomicUnit_at_Kplus_place_eq_sub_decomp
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace (NumberField.maximalRealSubfield K)) :
    Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
        ((LehmerVandiver.realCyclotomicUnit p K k : 𝓞 K) : K)) =
      2 * Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
          ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) ^ k - 1)) -
        2 * Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
          ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1)) :=
  log_realCyclotomicUnit_eq_sub_decomp p K k hk hp_two
    ((NumberField.IsCMField.equivInfinitePlace K).symm w)

set_option backward.isDefEq.respectTransparency false in
/-- **`KummerDirichletDeterminant`**: the explicit determinant evaluation.

For the matrix `M` from `regOfFamily_cyclotomicUnitFamilyKplus_eq_det`,
`|det M| = 2^((p-3)/2) · (hPlus K: ℝ) · regulator K⁺`.

The factor `2^((p-3)/2)` is the index `[C⁺: ⟨squared cyclotomic family⟩]`:
the project's family `realCyclotomicUnit_k = c_k · σ(c_k)` is the
square of a "smaller" cyclotomic unit (under K-embedding,
`σ(realCyclotomicUnit_k) = |σ(c_k)|²`), so `⟨family⟩` has index
`2^((p-3)/2)` in the standard cyclotomic unit subgroup `C⁺`.
Combined with the Sinnott index identity `[U⁺: C⁺] = h⁺`, the total
index is `2^((p-3)/2) · h⁺`, hence
`regOfFamily(family) = 2^((p-3)/2) · h⁺ · regulator(K⁺)`.

This is the cyclotomic case of Sinnott's class number formula. -/
def KummerDirichletDeterminant (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
    (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) * NumberField.Units.regulator
      (NumberField.maximalRealSubfield K)

set_option backward.isDefEq.respectTransparency false in
/-- **`KummerDirichletDeterminant` = `SinnottRegulatorIdentity`**: as
formulated, both Props are literally the same equation. -/
theorem sinnottRegulatorIdentity_iff_kummerDirichletDeterminant
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    KummerDirichletDeterminant p K hp_odd hp_three ↔
      SinnottRegulatorIdentity p K hp_odd hp_three :=
  Iff.rfl

end Sinnott

end LehmerVandiver

end KummerCriterion

end
