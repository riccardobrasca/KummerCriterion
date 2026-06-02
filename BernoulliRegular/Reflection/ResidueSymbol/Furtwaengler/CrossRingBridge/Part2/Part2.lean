module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.Part2.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler









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


end Furtwaengler

end BernoulliRegular

end
