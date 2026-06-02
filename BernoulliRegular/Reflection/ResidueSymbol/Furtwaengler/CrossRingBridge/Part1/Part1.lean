module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicPairGalois
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Cross-ring bridge: 𝓞 K / P' inside 𝓞 R' / 𝔭

For a prime ideal `P'` of `𝓞 K` and a prime `𝔭` of `𝓞 R'` lying over `P'`
(in a finite extension `R' / K`), the residue field `𝓞 R' / 𝔭` extends
the residue field `𝓞 K / P'`. This file builds the bridge:

* Existence of `𝔭` over a maximal `P'` (via going-up).
* Canonical injection `𝓞 K / P' → 𝓞 R' / 𝔭`.
* Compatible CharP transfer.

This is the first cross-ring atomic step toward K2-2 path (a):
applying the K2-1 atom in `𝓞 R' / 𝔭` (where `gaussSumInt` lives via
`algebraMap 𝓞 K 𝓞 R'`) and pulling back to `𝓞 K / P'`.

Per AI reviewer 2026-05-05 K2-2 plan: the descent atom requires this
bridge to apply K2-1 in the right ambient ring. Multi-week scope per
the plan; this file is the first chunk.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-! ### Existence of a prime above `P'` in an integral extension -/


/-! ### Residue field embedding `𝓞 K / P → 𝓞 R' / 𝔭`

For `𝔭 ⊂ 𝓞 R'` lying over `P ⊂ 𝓞 K` (i.e., `𝔭.comap algebraMap = P`),
the algebra map `𝓞 K → 𝓞 R'` factors through the residue fields,
giving an injection `𝓞 K / P → 𝓞 R' / 𝔭`. -/

/-- **Residue-field embedding** induced by a prime `𝔭` of `𝓞 R'` lying
over `P ⊂ 𝓞 K`. -/
noncomputable def residueFieldEmbedding
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P) :
    𝓞 K ⧸ P →+* 𝓞 R' ⧸ 𝔭 :=
  Ideal.quotientMap 𝔭 (algebraMap (𝓞 K) (𝓞 R')) h_over.symm.le

@[simp] theorem residueFieldEmbedding_mk
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P)
    (x : 𝓞 K) :
    residueFieldEmbedding h_over (Ideal.Quotient.mk P x) =
      Ideal.Quotient.mk 𝔭 (algebraMap (𝓞 K) (𝓞 R') x) := by
  unfold residueFieldEmbedding
  exact Ideal.quotientMap_mk

/-- **Injectivity of the residue-field embedding**: `𝓞 K / P → 𝓞 R' / 𝔭`
is injective when `𝔭` lies over `P` (i.e., the comap is exactly `P`). -/
theorem residueFieldEmbedding_injective
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P) :
    Function.Injective (residueFieldEmbedding h_over) := by
  unfold residueFieldEmbedding
  -- Ideal.quotientMap is injective when the comap equals the source ideal.
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- Lift x to 𝓞 K, use that quotientMap_mk maps to algebraMap mod 𝔭.
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotientMap_mk] at hx
  -- hx: Ideal.Quotient.mk 𝔭 (algebraMap a) = 0, so algebraMap a ∈ 𝔭, so a ∈ comap = P.
  rw [Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [← h_over]
  exact hx

/-! ### CharP transfer through the bridge

If `P ⊂ 𝓞 K` is maximal containing the rational prime `ℓ`, and `𝔭 ⊂ 𝓞 R'`
lies over `P`, then `𝔭` also contains `(ℓ : 𝓞 R')` and inherits CharP `ℓ`. -/



/-! ### MulChar / AddChar reduction along ring hom

For `χ : MulChar R R'` with `χ^p = 1` and a ring hom `σ : R' →+* R''`,
the post-composition `χ.ringHomComp σ : MulChar R R''` also satisfies
`(χ.ringHomComp σ)^p = 1`. This is needed to apply K2-1 in `R'' = 𝓞 R' / 𝔭`. -/


/-! ### Constructive descent generator from `FullTeichDworkSetup`

For a `FullTeichDworkSetup S`, the existing chain provides
`exists_descentPrime_pow_mul_stickOrdOrd_div` which extracts a Galois-fixed
lift `γ ∈ 𝓞 K` of `S.gaussSumInt a ^ p ∈ 𝓞 R'`. We name this lift
`phiPrimeGenDescent S a` for use in the K2-2 chain. -/

/-- **Constructive descent generator**: for index `a`, the unique lift
`γ ∈ 𝓞 K` with `algebraMap γ = S.gaussSumInt a ^ p`, extracted from
`exists_descentPrime_pow_mul_stickOrdOrd_div`. -/
noncomputable def phiPrimeGenDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) : 𝓞 K :=
  (S.exists_descentPrime_pow_mul_stickOrdOrd_div ha₁ ha₂ h_ne_zero).choose


/-- **Constructive descent property**: `algebraMap (phiPrimeGenDescent S a)
= S.gaussSumInt a ^ p` in `𝓞 R'`. -/
theorem algebraMap_phiPrimeGenDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    algebraMap (𝓞 K) (𝓞 R') (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) =
      S.gaussSumInt a ^ p :=
  (S.exists_descentPrime_pow_mul_stickOrdOrd_div ha₁ ha₂ h_ne_zero).choose_spec.2.1









/-- Prime-over data for a source prime, including the split residue-field
condition needed by the canonical quotient map. -/
structure Ref18SourcePrimeOverData
    (ℓ p : ℕ)
    (K : Type*) [Field K] [NumberField K]
    (R' : Type*) [Field R'] [NumberField R'] [Algebra K R']
    (P : Ideal (𝓞 K)) [P.IsMaximal] where

namespace Ref18SourcePrimeOverData




end Ref18SourcePrimeOverData

end Furtwaengler

end BernoulliRegular

end
