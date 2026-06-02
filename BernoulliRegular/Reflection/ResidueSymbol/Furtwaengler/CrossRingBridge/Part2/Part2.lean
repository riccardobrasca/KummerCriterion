module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.Part2.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler









/-! ### Embedding bridge: `phiPrimeGenDescent mod P'` ↔ `gaussSumInt^p mod 𝔭`

The embedding `𝓞 K / P' → 𝓞 R' / 𝔭` sends `phiPrimeGenDescent S a mod P'`
to `gaussSumInt a^p mod 𝔭`, since `algebraMap phiPrimeGenDescent S a =
gaussSumInt a^p` (the constructive descent property). -/

/-- **Embedding sends `phiPrimeGenDescent` to `gaussSumInt^p` mod `𝔭`**. -/
theorem residueFieldEmbedding_phiPrimeGenDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P') :
    residueFieldEmbedding h_over
      ((Ideal.Quotient.mk P' (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)) :
        𝓞 K ⧸ P') =
      ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a ^ p)) : 𝓞 R' ⧸ 𝔭) := by
  rw [residueFieldEmbedding_mk h_over]
  rw [algebraMap_phiPrimeGenDescent]

/-! ### gaussSumInt reduction mod 𝔭

The gaussSumInt (in `𝓞 R'`) reduces mod `𝔭` to a Gauss sum in `𝓞 R' / 𝔭`
of the post-composed characters. This is the standard `gaussSum_ringHomComp`
applied to the quotient map. -/

/-- **gaussSumInt reduced mod 𝔭 is a Gauss sum** of post-composed
characters in `𝓞 R' / 𝔭`. -/
theorem ideal_quotient_mk_gaussSumInt
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (a : ℕ)
    (𝔭 : Ideal (𝓞 R')) :
    Ideal.Quotient.mk 𝔭 (S.gaussSumInt a) =
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) := by
  unfold ConcreteStickelbergerSetup.gaussSumInt
  exact gaussSum_ringHomComp _ _ (Ideal.Quotient.mk 𝔭)

/-! ### K2-1 application in 𝓞 R' / 𝔭

Combining the cross-ring atoms above: under appropriate hypotheses on
`𝔭` (lying over `P'`), the K2-1 atom applies to `gaussSumInt a` in
`𝓞 R' / 𝔭`. -/

/-- **K2-1 in cross-ring `𝓞 R' / 𝔭`**: for `gaussSumInt a` reduced mod
the prime `𝔭 ⊂ 𝓞 R'` (with `𝓞 R' / 𝔭` of `CharP ℓ_P'` and the right
unit witness), the K2-1 cancellation form holds. -/
theorem ideal_quotient_mk_gaussSumInt_pow_pow_div_apply_smul_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (a : ℕ)
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f) (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0) :
    ((S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭)) unit_a *
        (((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^ ((ℓ' ^ f - 1) / p) = 1 := by
  rw [ideal_quotient_mk_gaussSumInt]
  exact gaussSum_pow_p_pow_div_apply_smul_eq_one_of_charP_field hp _ h_χp_eq_one _
    hf hN_mod_p unit_a h_unit hg_ne


/-! ### Cross-ring K2-2c bridge: residueMulChar values

For the canonical residue character `residueMulChar zeta_q ... zeta_R`
post-composed with the quotient `𝓞 R' → 𝓞 R' / 𝔭`, the value at `α mod P`
relates to the canonical residue exponent at `P`. -/


/-! ### Embedding of `canonicalResidueZetaP P'` into `𝓞 R' / 𝔭`

The canonical primitive `p`-th root in `(𝓞 K / P')ˣ` embeds into
`(𝓞 R' / 𝔭)ˣ` via the residue field embedding, giving a primitive
`p`-th root in the larger residue ring. -/

/-- **Embedded canonical zeta in `𝓞 R' / 𝔭`**: the image of
`canonicalResidueZetaP P'` under the residue field embedding (as an
element of `(𝓞 R' / 𝔭)ˣ`). -/
noncomputable def canonicalResidueZetaP_image
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P') : (𝓞 R' ⧸ 𝔭)ˣ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- canonicalResidueZetaP P' ∈ (𝓞 K / P')ˣ. Its image under the embedding
  -- 𝓞 K / P' →+* 𝓞 R' / 𝔭 is a unit (since the embedding is a ring hom
  -- and respects units). We extract the unit form.
  have hu : IsUnit ((residueFieldEmbedding h_over)
      (canonicalResidueZetaP (p := p) (K := K) P' : 𝓞 K ⧸ P')) :=
    (canonicalResidueZetaP (p := p) (K := K) P').isUnit.map (residueFieldEmbedding h_over)
  hu.unit

@[simp] theorem canonicalResidueZetaP_image_val
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P') :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((canonicalResidueZetaP_image (p := p) (K := K) (R' := R')
      h_over) : 𝓞 R' ⧸ 𝔭) =
      (residueFieldEmbedding h_over)
        (canonicalResidueZetaP (p := p) (K := K) P' : 𝓞 K ⧸ P') := by
  rfl


/-! ### K2-2c bridge in cross-ring (residueMulChar.ringHomComp value)

The post-composed residue character at a quotient class equals the
post-composed `zeta_R` raised to the canonical residue exponent.
Direct from K2-2c (in `PhiPrimeSymbol.lean`) plus pow-preserved-by-ring-hom. -/


/-! ### Zeta-compatibility: connecting setup `zeta_p_int` to `canonicalResidueZetaP_image`

The `FullTeichDworkSetup`'s chosen primitive `p`-th root `zeta_p_int : 𝓞 R'`
needs to be compatible with the canonical primitive root `cyclotomicZetaInteger K`
modulo `𝔭` for the K2-2 chain to close cleanly. We expose this compatibility
as a named predicate. -/

/-- **Setup-zeta compatibility predicate**: in the residue ring `𝓞 R' / 𝔭`,
the setup's `zeta_p_int` reduces to the same element as the canonical
zeta from `K`. -/
def SetupZetaCompatible
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {𝔭 : Ideal (𝓞 R')} : Prop :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  Ideal.Quotient.mk 𝔭
      (S.zeta_p_int) =
    Ideal.Quotient.mk 𝔭
      ((algebraMap (𝓞 K) (𝓞 R'))
        (BernoulliRegular.cyclotomicZetaInteger (p := p) K))


/-- **Identification under setup-zeta compatibility**: under
`SetupZetaCompatible`, the setup's `zeta_p_int` reduced mod `𝔭` equals
the underlying value of `canonicalResidueZetaP_image`. -/
theorem ideal_quotient_mk_zeta_p_int_eq_canonicalResidueZetaP_image
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    Ideal.Quotient.mk 𝔭
      (S.zeta_p_int) =
      ((canonicalResidueZetaP_image (p := p) (K := K) (R' := R')
        h_over) : 𝓞 R' ⧸ 𝔭) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [h_compat, canonicalResidueZetaP_image_val h_over,
      canonicalResidueZetaP_val P', residueFieldEmbedding_mk h_over]

/-! ### Embedding respects pow

A simple consequence of `residueFieldEmbedding` being a ring hom: it
preserves `pow` operations. -/


/-! ### K2-1 cross-ring on embedded `phiPrimeGenDescent`

Combining the embedding bridge `e (Quotient.mk P' phiPrimeGenDescent) =
Quotient.mk 𝔭 (gaussSumInt^p)` with K2-1 in the cross-ring, we get the
K2-1 cancellation form on the embedded descent generator. -/

end Furtwaengler

end BernoulliRegular

end

end
