import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part2

@[expose] public section

noncomputable section

open Real Complex
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]


/-- **Frobenius determinant identity (named Prop)**: the squared
regulator of the cyclotomic-unit family equals
`(∏_{χ even nontriv} DirichletLogSum p χ⁻¹)²` in ℂ.

This is the **algebraic-side closed form** that PF-1's algebraic
side reduces to. Combining with the analytic identity
`(hPlus · regulator)² · 2^(p-3) = (∏ DLS)²` (`hPlus_mul_regulator_sq_eq`)
gives the corrected Sinnott target
`regOfFamily² = 2^(p-3) · (hPlus · regulator)²`. -/
def FrobeniusDetIdentity
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  ((NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2 =
    (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
        DirichletLogSum p χ⁻¹) ^ 2

/-- **`KummerDirichletDeterminant` from `FrobeniusDetIdentity`**:
under the algebraic-side Frobenius-determinant identity, the corrected
Kummer-Dirichlet identity `regOfFamily = 2^((p-3)/2) · h⁺ · R(K⁺)` holds.
The factor `2^((p-3)/2)` comes from comparing the corrected FrobDet
`regOfFamily² = (∏ DLS)²` against the analytic identity
`(h⁺ · R)² · 2^(p-3) = (∏ DLS)²`. -/
theorem KummerDirichletDeterminant_of_FrobeniusDetIdentity
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h_frob : FrobeniusDetIdentity (p := p) K hp_odd hp_three) :
    FLT37.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three := by
  unfold FLT37.Sinnott.KummerDirichletDeterminant
  unfold FrobeniusDetIdentity at h_frob
  -- h_frob : ↑regOfFamily ^ 2 = (∏ DLS χ⁻¹)² in ℂ
  have h_analytic := hPlus_mul_regulator_sq_eq (p := p) K hp_odd hp_three
  -- h_analytic : (↑hPlus · ↑regulator)² = (∏ DLS χ⁻¹)² / 2^(p-3) in ℂ
  -- Combine: regOfFamily² = (∏ DLS)² = 2^(p-3) · (hPlus · regulator)²
  --                      = (2^((p-3)/2) · hPlus · regulator)²
  have h_sq_eq_C : ((NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2 =
      (((2 : ℝ) ^ ((p - 3) / 2) : ℝ) : ℂ) ^ 2 *
      (((BernoulliRegular.hPlus K : ℕ) : ℂ) *
        ((NumberField.Units.regulator (NumberField.maximalRealSubfield K) : ℝ) : ℂ)) ^ 2 := by
    rw [h_frob]
    rw [show (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
            DirichletLogSum p χ⁻¹) ^ 2 =
        ((2 : ℂ) ^ (p - 3)) *
          ((∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
            DirichletLogSum p χ⁻¹) ^ 2 / (2 : ℂ) ^ (p - 3)) from by
      field_simp]
    rw [← h_analytic]
    -- Goal: 2^(p-3) · (hPlus · R)² = (2^((p-3)/2))² · (hPlus · R)²
    have h_pow_eq : (((2 : ℝ) ^ ((p - 3) / 2) : ℝ) : ℂ) ^ 2 = (2 : ℂ) ^ (p - 3) := by
      push_cast
      rw [← pow_mul]
      congr 1
      have h_p_odd : Odd p := hp.out.odd_of_ne_two hp_odd
      rcases h_p_odd with ⟨k, hk⟩
      omega
    rw [h_pow_eq]
  -- Cast h_sq_eq_C to ℝ.
  have h_sq_eq_R : (NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ^ 2 =
      ((2 : ℝ) ^ ((p - 3) / 2) * ((BernoulliRegular.hPlus K : ℕ) : ℝ) *
        NumberField.Units.regulator (NumberField.maximalRealSubfield K)) ^ 2 := by
    have h_cast : ((NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) ^ 2 : ℝ) : ℂ) =
        (((2 : ℝ) ^ ((p - 3) / 2) * ((BernoulliRegular.hPlus K : ℕ) : ℝ) *
          NumberField.Units.regulator (NumberField.maximalRealSubfield K)) ^ 2 : ℂ) := by
      push_cast
      push_cast at h_sq_eq_C
      linear_combination h_sq_eq_C
    exact_mod_cast h_cast
  -- Positivity: regOfFamily ≥ 0 and 2^((p-3)/2) · hPlus · regulator > 0.
  have h_reg_nonneg : (0 : ℝ) ≤ NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) := by
    rw [BernoulliRegular.FLT37.Sinnott.regOfFamily_cyclotomicUnitFamilyKplus_eq_det
      (p := p) (K := K) hp_odd hp_three]
    exact abs_nonneg _
  have h_rhs_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ ((p - 3) / 2) *
      ((BernoulliRegular.hPlus K : ℕ) : ℝ) *
      NumberField.Units.regulator (NumberField.maximalRealSubfield K) := by
    refine mul_nonneg (mul_nonneg ?_ ?_) (NumberField.Units.regulator_pos _).le
    · positivity
    · exact Nat.cast_nonneg _
  -- Conclude: a² = b² with a, b ≥ 0 implies a = b.
  exact (sq_eq_sq₀ h_reg_nonneg h_rhs_nonneg).mp h_sq_eq_R

/-! ## Character matrix infrastructure for the Frobenius determinant formula

The Frobenius determinant formula for cyclic groups says that for a function
`f : G → ℂ` on a finite cyclic group `G` and the matrix `M[a, b] = f(a · b)`,
`det M = ∏_χ (∑_a χ(a) · f(a))`. Specialised to `G = (ZMod p)ˣ` for prime `p`,
this is the key identity behind `FrobeniusDetIdentity`.

The proof uses the **character matrix** `F[χ, a] = χ(a)` and the
multiplicative-action eigenvalue formula `(F · M)[χ, b] = χ(b)⁻¹ · λ_χ`,
where `λ_χ = ∑_a χ(a) · f(a)`. -/

/-- **Character matrix** for `(ZMod p)ˣ` mod `p`: the `(p-1) × (p-1)` matrix
with rows indexed by Dirichlet characters and columns by units, with entries
`F[χ, a] = χ(a)`. This is the discrete Fourier transform matrix for the
multiplicative-character diagonalisation. -/
noncomputable def characterMatrix :
    Matrix (DirichletCharacter ℂ p) ((ZMod p)ˣ) ℂ :=
  Matrix.of fun χ a => χ ((a : ZMod p))

/-- **Convolution matrix** for a function `f : (ZMod p)ˣ → ℂ`: the matrix
indexed by `(ZMod p)ˣ × (ZMod p)ˣ` with entries `M[a, b] = f(a · b)`. The
DFT-diagonalisation lifts this to a "diagonal" form via the character
matrix. -/
noncomputable def convolutionMatrix (f : (ZMod p)ˣ → ℂ) :
    Matrix ((ZMod p)ˣ) ((ZMod p)ˣ) ℂ :=
  Matrix.of fun a b => f (a * b)

/-- **Matrix-level eigenvalue formula for the multiplicative convolution
matrix**: `(characterMatrix · convolutionMatrix f)[χ, b] = χ(b)⁻¹ · (∑_a χ(a) · f(a))`.

This is the "characters diagonalise the convolution matrix" step in the
Frobenius determinant formula for cyclic groups. The proof uses the
substitution `a → a · b⁻¹` and character multiplicativity. -/
theorem characterMatrix_mul_convolutionMatrix_apply
    (f : (ZMod p)ˣ → ℂ) (χ : DirichletCharacter ℂ p) (b : (ZMod p)ˣ) :
    (characterMatrix p * convolutionMatrix p f) χ b =
      χ ((b⁻¹ : (ZMod p)ˣ) : ZMod p) * ∑ a : (ZMod p)ˣ, χ ((a : ZMod p)) * f a := by
  classical
  simp only [Matrix.mul_apply, characterMatrix, convolutionMatrix, Matrix.of_apply]
  -- Reindex the LHS sum a → a · b⁻¹ via the bijection `Equiv.mulRight b`.
  have h_reindex : ∑ a : (ZMod p)ˣ, χ ((a : ZMod p)) * f (a * b) =
      ∑ a : (ZMod p)ˣ, χ (((a * b⁻¹ : (ZMod p)ˣ) : ZMod p)) * f a := by
    apply (Fintype.sum_equiv (Equiv.mulRight b⁻¹) _ _ _).symm
    intro a
    rw [Equiv.coe_mulRight]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [h_reindex]
  -- Each summand factors: χ((a·b⁻¹).val) · f a = χ(b⁻¹.val) · (χ(a.val) · f a).
  have h_factor : ∀ a : (ZMod p)ˣ,
      χ (((a * b⁻¹ : (ZMod p)ˣ) : ZMod p)) * f a =
      χ ((b⁻¹ : (ZMod p)ˣ) : ZMod p) * (χ ((a : ZMod p)) * f a) := by
    intro a
    rw [Units.val_mul, map_mul]
    ring
  rw [Finset.sum_congr rfl (fun a _ => h_factor a)]
  rw [← Finset.mul_sum]



/-- **Dirichlet character / units equivalence** for prime `p` (extraction of
the mathlib `Nonempty (DirichletCharacter ℂ p ≃* (ZMod p)ˣ)` existence into
a concrete equivalence via choice). Used to re-index character matrices as
square matrices for determinant computations. -/
noncomputable def dirichletCharEquivUnits :
    DirichletCharacter ℂ p ≃* (ZMod p)ˣ :=
  (DirichletCharacter.mulEquiv_units ℂ p).some

/-- **Square character matrix**: the `(p-1) × (p-1)` matrix indexed by
`(ZMod p)ˣ × (ZMod p)ˣ` with entries `((dirichletCharEquivUnits p).symm k) (a)`,
i.e., row `k` is the Dirichlet character corresponding to `k` under the
Pontryagin equivalence. This is `characterMatrix p` reindexed via the
equivalence on rows. -/
noncomputable def characterMatrixSquare :
    Matrix ((ZMod p)ˣ) ((ZMod p)ˣ) ℂ :=
  Matrix.of fun k a => ((dirichletCharEquivUnits p).symm k) ((a : ZMod p))








/-- **Helper**: for a Dirichlet character ψ mod p, the sum over units of
ψ at the unit cast to `ZMod p` equals the sum over all of `ZMod p` of ψ.

This is because `ψ(0) = 0` (mathlib's `MulChar.map_zero`) and the units
of `ZMod p` (for p prime) correspond bijectively to the non-zero elements
of `ZMod p`. -/
private theorem mulChar_sum_units_eq_sum_all (ψ : DirichletCharacter ℂ p) :
    ∑ a : (ZMod p)ˣ, ψ ((a : ZMod p)) = ∑ a : ZMod p, ψ a := by
  classical
  -- Bridge via Finset.sum_attach style:
  -- ∑ a : ZMod p, ψ a = (a=0 term ψ 0 = 0) + ∑_{a ≠ 0} ψ a
  --                  = ∑_{a ∈ Finset.univ.erase 0}, ψ a
  --                  = ∑_a : (ZMod p)ˣ, ψ ((a : ZMod p))   (bijection)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
  rw [ψ.map_zero, add_zero]
  -- Goal: ∑ a : (ZMod p)ˣ, ψ ((a : ZMod p)) = ∑ a ∈ Finset.univ.erase 0, ψ a
  refine Finset.sum_bij (fun (a : (ZMod p)ˣ) _ => (a : ZMod p)) ?_ ?_ ?_ ?_
  · -- mem: a unit, (a : ZMod p) ≠ 0
    intro a _
    rw [Finset.mem_erase]
    refine ⟨a.isUnit.ne_zero, Finset.mem_univ _⟩
  · -- inj
    intro a₁ _ a₂ _ h
    exact Units.ext h
  · -- surj
    intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨hb_ne, _⟩ := hb
    have h_b_val_ne : b.val ≠ 0 := fun h_val =>
      hb_ne <| (ZMod.val_eq_zero b).mp h_val
    have h_b_val_lt : b.val < p := ZMod.val_lt b
    have hp_prime : Nat.Prime p := hp.out
    have h_coprime : Nat.Coprime b.val p := by
      rw [Nat.coprime_comm]
      rw [hp_prime.coprime_iff_not_dvd]
      intro h_dvd
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h_b_val_ne) h_dvd) (by omega)
    refine ⟨ZMod.unitOfCoprime b.val h_coprime, Finset.mem_univ _, ?_⟩
    change ((ZMod.unitOfCoprime b.val h_coprime : (ZMod p)ˣ) : ZMod p) = b
    rw [ZMod.coe_unitOfCoprime]
    exact ZMod.natCast_zmod_val b
  · intro a _; rfl




/-- **Sin-norm bridge at units**: for a unit `a : (ZMod p)ˣ` in prime `p`,
`Real.log ‖1 - stdAddChar a‖ = Real.log (2 · |sin(π · a.val / p)|)`.

Uses the project's `norm_one_sub_exp_two_pi_I_mul` identity. -/
theorem log_norm_one_sub_stdAddChar_unit (a : (ZMod p)ˣ) :
    Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ =
      Real.log (2 * |Real.sin (Real.pi * (ZMod.val (a : ZMod p) : ℕ) / p)|) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set k : ℕ := ZMod.val ((a : ZMod p))
  have h_val_cast : ((a : ZMod p)) = ((k : ℤ) : ZMod p) := by
    change (a : ZMod p) = ((ZMod.val (a : ZMod p) : ℤ) : ZMod p)
    push_cast
    exact (ZMod.natCast_zmod_val (a : ZMod p)).symm
  rw [h_val_cast, ZMod.stdAddChar_coe (N := p) (k : ℤ)]
  push_cast
  have h_eq : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / p) =
      ((2 * Real.pi * ((k : ℕ) / p : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h_eq, norm_one_sub_exp_two_pi_I_mul]
  ring_nf

/-- **Sum of log-norm over units equals `log p`**: the unit-group sum
`∑ a : (ZMod p)ˣ, log‖1 - stdAddChar(↑a)‖ = log p`.

Composes the sin-norm bridge `log_norm_one_sub_stdAddChar_unit` with the
reindex `sum_units_val_eq_sum_Ico` and the cyclotomic product identity
`DirichletLogSum_principal_eq_neg_log` (which says `DLS p 1 = -log p`,
i.e., `∑ n ∈ Ico 1 p, log(2|sin(πn/p)|) = log p`). -/
theorem sum_units_logNorm_eq_log_p :
    ∑ a : BernoulliRegular.CyclotomicUnitDelta p,
        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) =
      ((Real.log p : ℝ) : ℂ) := by
  have h_summand : ∀ a : BernoulliRegular.CyclotomicUnitDelta p,
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) =
        ((Real.log
          (2 * |Real.sin (Real.pi * (ZMod.val (a : ZMod p) : ℕ) / p)|) : ℝ) :
            ℂ) := by
    intro a
    rw [log_norm_one_sub_stdAddChar_unit p a]
  simp_rw [h_summand]
  rw [sum_units_val_eq_sum_Ico (p := p)
      (fun n => ((Real.log (2 * |Real.sin (Real.pi * n / p)|) : ℝ) : ℂ))]
  have h_dls := DirichletLogSum_principal_eq_neg_log p
  unfold DirichletLogSum at h_dls
  have h_eval : ∀ n ∈ Finset.Ico 1 p,
      (1 : DirichletCharacter ℂ p) ((n : ℕ) : ZMod p) *
        ((Real.log (2 * |Real.sin (Real.pi * n / p)|) : ℝ) : ℂ) =
      ((Real.log (2 * |Real.sin (Real.pi * n / p)|) : ℝ) : ℂ) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have h_unit : IsUnit ((n : ℕ) : ZMod p) := by
      rw [isUnit_iff_ne_zero]
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      have hp_prime : Nat.Prime p := hp.out
      exact absurd (Nat.le_of_dvd hn.1 h) (by omega)
    rw [MulChar.one_apply h_unit, one_mul]
  have h_sum_eq : ∑ n ∈ Finset.Ico 1 p,
        ((Real.log (2 * |Real.sin (Real.pi * n / p)|) : ℝ) : ℂ) =
      ∑ n ∈ Finset.Ico 1 p,
        (1 : DirichletCharacter ℂ p) ((n : ℕ) : ZMod p) *
          ((Real.log (2 * |Real.sin (Real.pi * n / p)|) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl (fun n hn => (h_eval n hn).symm)
  rw [h_sum_eq]
  -- LHS: ∑ n, (1)(↑n) · log(2|sin|). RHS: log p.
  -- h_dls : -∑ n, (1)(↑n) · log(2|sin|) = -log p
  -- So ∑ n, (1)(↑n) · log(2|sin|) = log p.
  linear_combination -h_dls

/-- **Dirichlet character extension of a `CyclotomicEvenDelta` character**:
for `ξ : MulChar (CyclotomicEvenDelta p) ℂ`, produce the natural Dirichlet
character mod `p` that:
- agrees with the pullback `ξ ∘ q` on units,
- is 0 at 0.

Construction: pull `ξ` back to `MulChar ((ZMod p)ˣ) ℂ` via the quotient
map, convert to a unit-hom via `toUnitHom` (composed with `toUnits` to
go `(ZMod p)ˣ → ((ZMod p)ˣ)ˣ`), then extend by 0 via `MulChar.ofUnitHom`. -/
noncomputable def dirichletOfQuotientChar
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :
    DirichletCharacter ℂ p :=
  MulChar.ofUnitHom
    ((BernoulliRegular.evenDeltaCharacterPullback (p := p) ξ).toUnitHom.comp
      toUnits.toMonoidHom)

/-- **Extension value on units**: for `ξ : MulChar (CyclotomicEvenDelta p) ℂ`
and `a : (ZMod p)ˣ`, the Dirichlet extension at `↑a` equals `ξ (q a)`. -/
theorem dirichletOfQuotientChar_apply_unit
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
    (a : BernoulliRegular.CyclotomicUnitDelta p) :
    dirichletOfQuotientChar p ξ ((a : ZMod p)) =
      ξ (BernoulliRegular.cyclotomicEvenDeltaQuotient p a) := by
  unfold dirichletOfQuotientChar
  rw [MulChar.ofUnitHom_coe]
  rw [MonoidHom.comp_apply]
  rw [MulChar.coe_toUnitHom]
  change (BernoulliRegular.evenDeltaCharacterPullback (p := p) ξ)
      ((toUnits a).val) = _
  change (BernoulliRegular.evenDeltaCharacterPullback (p := p) ξ) a = _
  rfl

/-- **Dirichlet extension is always even**: for any `ξ : MulChar (CyclotomicEvenDelta p) ℂ`,
the Dirichlet extension `dirichletOfQuotientChar p ξ` is an even character of
`(ZMod p)`. This is because the extension factors through the quotient
`(ZMod p)ˣ ⧸ ⟨-1⟩`, so the character value at `-1` equals the value at `1`. -/
theorem dirichletOfQuotientChar_even
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :
    (dirichletOfQuotientChar p ξ).Even := by
  -- (dirichletOfQuotientChar ξ).Even := (dirichletOfQuotientChar ξ) (-1 : ZMod p) = 1.
  change (dirichletOfQuotientChar p ξ) (-1 : ZMod p) = 1
  -- Recast: (-1 : ZMod p) = ↑((-1 : (ZMod p)ˣ)). Then apply dirichletOfQuotientChar_apply_unit.
  have h_cast : (-1 : ZMod p) = ((-1 : (ZMod p)ˣ) : ZMod p) := by
    rw [Units.val_neg, Units.val_one]
  rw [h_cast]
  rw [dirichletOfQuotientChar_apply_unit p ξ (-1 : (ZMod p)ˣ)]
  -- Now: ξ (q (-1)) = ξ 1 = 1.
  rw [BernoulliRegular.cyclotomicEvenDeltaQuotient_neg_one]
  exact MulChar.map_one ξ

/-- **`dirichletOfQuotientChar` is injective**: distinct quotient characters
give distinct Dirichlet extensions. Used to establish the bijection between
quotient characters and even Dirichlet characters. -/
theorem dirichletOfQuotientChar_injective :
    Function.Injective (dirichletOfQuotientChar p) := by
  intro ξ₁ ξ₂ h
  apply MulChar.ext
  intro ā
  -- ā : (CyclotomicEvenDelta p)ˣ. Every element of CyclotomicEvenDelta is q(a) for some a.
  have h_repr : ∃ a : BernoulliRegular.CyclotomicUnitDelta p,
      BernoulliRegular.cyclotomicEvenDeltaQuotient p a =
        ((ā : BernoulliRegular.CyclotomicEvenDelta p)) := by
    refine ⟨Quotient.out ((ā : BernoulliRegular.CyclotomicEvenDelta p)), ?_⟩
    rw [BernoulliRegular.cyclotomicEvenDeltaQuotient_apply]
    exact Quotient.out_eq _
  obtain ⟨a, ha⟩ := h_repr
  rw [← ha]
  -- Want: ξ₁ (q a) = ξ₂ (q a). Use h at a.
  have h_at_a : dirichletOfQuotientChar p ξ₁ ((a : ZMod p)) =
      dirichletOfQuotientChar p ξ₂ ((a : ZMod p)) := by
    rw [h]
  rw [dirichletOfQuotientChar_apply_unit p ξ₁ a,
      dirichletOfQuotientChar_apply_unit p ξ₂ a] at h_at_a
  exact h_at_a

/-- **Dirichlet extension of trivial character is trivial**:
`dirichletOfQuotientChar p 1 = 1` as Dirichlet characters. -/
theorem dirichletOfQuotientChar_one :
    dirichletOfQuotientChar p
        (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
      (1 : DirichletCharacter ℂ p) := by
  apply MulChar.ext
  intro u
  rw [dirichletOfQuotientChar_apply_unit]
  -- LHS: 1 (q u) where q is the quotient map. = 1 since q u is a unit.
  -- RHS: 1 (↑u) = 1 since u is a unit.
  rw [MulChar.one_apply u.isUnit]
  rw [MulChar.one_apply (Group.isUnit _)]

/-- **Trivial-character product split on the quotient**: the product over
all `ξ : MulChar (CyclotomicEvenDelta p) ℂ` of `DLS p (ext ξ)` factors as
`DLS p 1 · ∏_{ξ ≠ 1} DLS p (ext ξ)`. Parallel to
`prod_dirichletCharacter_eq_trivial_mul_nontrivial`. -/
theorem prod_mulChar_DLS_eq_trivial_mul_nontrivial :
    haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    haveI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Classical.decEq _
    ∏ ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ,
        DirichletLogSum p (dirichletOfQuotientChar p ξ) =
      DirichletLogSum p (1 : DirichletCharacter ℂ p) *
        ∏ ξ ∈ (Finset.univ : Finset
            (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
          DirichletLogSum p (dirichletOfQuotientChar p ξ) := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  letI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ
    (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ))]
  rw [dirichletOfQuotientChar_one]
  ring


/-- **Quotient eigenvalue at trivial character is `(log p)/2`**:
combining `two_mul_quotientEigenvalue_trivial_eq_sum_logNorm` (full-group
sum form) with `sum_units_logNorm_eq_log_p` (the value `log p`) gives the
explicit trivial-eigenvalue value of the quotient Frobenius determinant. -/
theorem quotientEigenvalue_trivial_eq_half_log_p (hp_two : 2 < p) :
    quotientEigenvalue p (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
      ((Real.log p : ℝ) : ℂ) / 2 := by
  have h := two_mul_quotientEigenvalue_trivial_eq_sum_logNorm p hp_two
  rw [sum_units_logNorm_eq_log_p p] at h
  linear_combination h / 2


/-- **Frobenius eigenvalue identification**: for `χ` a Dirichlet character
mod `p`, the eigenvalue of the cyclotomic-unit convolution matrix at `χ`
equals `-DirichletLogSum p χ`:

  ∑_{a : (ZMod p)ˣ} χ(↑a) · log‖1 - stdAddChar(↑a)‖ = -DirichletLogSum p χ.

Combines `mulChar_sum_units_eq_sum_all`-style bridge + the shipped
`evenLValueLogSum_eq_neg_DirichletLogSum_inv` (at χ⁻¹, with double-inv
cancellation). -/
theorem frobenius_eigenvalue_eq_neg_DirichletLogSum
    (χ : DirichletCharacter ℂ p) :
    ∑ a : (ZMod p)ˣ, χ ((a : ZMod p)) *
        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) =
      -DirichletLogSum p χ := by
  classical
  -- Step 1: convert sum-over-units to sum-over-ZMod-p (extending by 0 at 0).
  have h_units_sum_eq : ∑ a : (ZMod p)ˣ,
        χ ((a : ZMod p)) *
          ((Real.log ‖(1 : ℂ) -
            ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) =
      ∑ a : ZMod p,
        χ a * ((Real.log ‖(1 : ℂ) -
          ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) := by
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
    -- a = 0 term: χ(0) · log‖1 - stdAddChar 0‖ = 0 · log 0 = 0
    rw [χ.map_zero, zero_mul, add_zero]
    -- Sum over (ZMod p)ˣ = sum over univ.erase 0 (ZMod p). Bij a ↦ (a : ZMod p).
    refine Finset.sum_bij (fun (a : (ZMod p)ˣ) _ => (a : ZMod p)) ?_ ?_ ?_ ?_
    · intro a _
      rw [Finset.mem_erase]
      exact ⟨a.isUnit.ne_zero, Finset.mem_univ _⟩
    · intro a₁ _ a₂ _ h
      exact Units.ext h
    · intro b hb
      rw [Finset.mem_erase] at hb
      obtain ⟨hb_ne, _⟩ := hb
      have h_b_val_ne : b.val ≠ 0 := fun h_val =>
        hb_ne ((ZMod.val_eq_zero b).mp h_val)
      have h_b_val_lt : b.val < p := ZMod.val_lt b
      have hp_prime : Nat.Prime p := hp.out
      have h_coprime : Nat.Coprime b.val p := by
        rw [Nat.coprime_comm]
        rw [hp_prime.coprime_iff_not_dvd]
        intro h_dvd
        exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h_b_val_ne) h_dvd) (by omega)
      refine ⟨ZMod.unitOfCoprime b.val h_coprime, Finset.mem_univ _, ?_⟩
      change ((ZMod.unitOfCoprime b.val h_coprime : (ZMod p)ˣ) : ZMod p) = b
      rw [ZMod.coe_unitOfCoprime]
      exact ZMod.natCast_zmod_val b
    · intro a _; rfl
  rw [h_units_sum_eq]
  -- Step 2: convert ∑ a : ZMod p, χ(a) · log|...| to evenLValueLogSum p χ⁻¹.
  have h_sum_eq_evenL : ∑ a : ZMod p,
        χ a * ((Real.log ‖(1 : ℂ) -
          ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) =
      BernoulliRegular.evenLValueLogSum p χ⁻¹ := by
    unfold BernoulliRegular.evenLValueLogSum
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [inv_inv]
  rw [h_sum_eq_evenL]
  rw [evenLValueLogSum_eq_neg_DirichletLogSum_inv]
  rw [inv_inv]

/-- **General quotient-eigenvalue identification**: for
`ξ : MulChar (CyclotomicEvenDelta p) ℂ` and `p > 2`, the quotient
eigenvalue relates to the DLS at the Dirichlet extension
`dirichletOfQuotientChar p ξ`:

  2 · quotientEigenvalue p ξ = -DirichletLogSum p (dirichletOfQuotientChar p ξ).

Direct composition of:
- `two_mul_quotientEigenvalue_eq_sum_full` (full-group character sum form).
- `dirichletOfQuotientChar_apply_unit` (pullback ↔ extension at units).
- `frobenius_eigenvalue_eq_neg_DirichletLogSum` (DLS form for the extension).

This is the eigenvalue identification: every quotient-Frobenius
eigenvalue is `-(1/2) · DLS p (extension)`. For the trivial character ξ = 1,
this gives `(log p)/2` (consistent with `DLS p 1 = -log p`, see
`quotientEigenvalue_trivial_eq_half_log_p`). For non-trivial even
characters, it gives the substantive `DLS` factor that enters the
Sinnott regulator formula. -/
theorem two_mul_quotientEigenvalue_eq_neg_DLS
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) (hp_two : 2 < p) :
    2 * quotientEigenvalue p ξ =
      -DirichletLogSum p (dirichletOfQuotientChar p ξ) := by
  rw [two_mul_quotientEigenvalue_eq_sum_full p ξ hp_two]
  rw [← frobenius_eigenvalue_eq_neg_DirichletLogSum p (dirichletOfQuotientChar p ξ)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  rw [dirichletOfQuotientChar_apply_unit]
  rfl

/-- **Squared eigenvalue identity**: squaring
`two_mul_quotientEigenvalue_eq_neg_DLS` and dividing by 4 gives the
clean identity

  (quotientEigenvalue p ξ)² = (DirichletLogSum p (dirichletOfQuotientChar p ξ))² / 4.

This is the key form used in the squared Frobenius determinant
identity, since it eliminates signs and the explicit factor of 2. -/
theorem quotientEigenvalue_sq_eq_DLS_sq_div_four
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) (hp_two : 2 < p) :
    (quotientEigenvalue p ξ) ^ 2 =
      (DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2 / 4 := by
  have h := two_mul_quotientEigenvalue_eq_neg_DLS p ξ hp_two
  have h_sq : (2 * quotientEigenvalue p ξ) ^ 2 =
      (-DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2 := by
    rw [h]
  rw [neg_pow, neg_one_sq, one_mul] at h_sq
  linear_combination h_sq / 4

/-- **Det squared in DLS-product form**: combining the squared det formula
in eigenvalue form with the squared-eigenvalue identification
`quotientEigenvalue_sq_eq_DLS_sq_div_four`:

  det(convolutionMatrixLogNormEven p)² =
    (∏ ξ : MulChar, DLS p (dirichletOfQuotientChar p ξ))² / 4^(card MulChar). -/
theorem det_convolutionMatrixLogNormEven_sq_eq_prod_DLS_sq_div_four_pow
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    (convolutionMatrixLogNormEven p).det ^ 2 =
      (∏ ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ,
        (DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2) /
      4 ^ (Fintype.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)) := by
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  rw [det_convolutionMatrixLogNormEven_sq_eq_prod_quotientEigenvalue_sq p hp_two]
  rw [← Finset.prod_pow]
  rw [prod_quot_eq_prod_mulChar p (fun ξ => (quotientEigenvalue p ξ) ^ 2)]
  have h_eigen_sq : ∀ ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ,
      (quotientEigenvalue p ξ) ^ 2 =
        (DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2 / 4 := fun ξ =>
    quotientEigenvalue_sq_eq_DLS_sq_div_four p ξ hp_two
  rw [Finset.prod_congr rfl (fun ξ _ => h_eigen_sq ξ)]
  rw [Finset.prod_div_distrib]
  rw [Finset.prod_const, Finset.card_univ]

/-- **Squared det in `(log p)² · (∏ nontriv DLS)² / 4^card` form**: combining
the squared det formula in `(∏ all DLS)² / 4^card` form with the trivial-
character split and `DLS p 1 = -log p` gives the explicit factorisation
extracting the trivial-character contribution. -/
theorem det_convolutionMatrixLogNormEven_sq_eq_log_p_sq_mul_nontrivial_DLS_sq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    haveI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Classical.decEq _
    (convolutionMatrixLogNormEven p).det ^ 2 =
      (((Real.log p : ℝ) : ℂ)) ^ 2 *
        (∏ ξ ∈ (Finset.univ : Finset
            (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
          DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2 /
      4 ^ (Fintype.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)) := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  letI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  have h_sq_eq : (∏ ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ,
      (DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2) =
    (∏ ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ,
      DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2 := by
    rw [Finset.prod_pow]
  rw [det_convolutionMatrixLogNormEven_sq_eq_prod_DLS_sq_div_four_pow p hp_two]
  rw [h_sq_eq]
  rw [prod_mulChar_DLS_eq_trivial_mul_nontrivial p]
  rw [DirichletLogSum_principal_eq_neg_log p]
  rw [mul_pow]
  congr 1
  ring

end Sinnott

end FLT37

end BernoulliRegular

end
