module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.Part1.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler






/-! ### Conductor-flexible reciprocal exponent normalization -/

namespace ConductorFlexibleFullTeichDworkSetup

/-- Flexible residue-degree-one form of the ordinary-convention Dwork order at
index `p - a.val`. -/
theorem stickOrdOrd_sub_val_eq_val_mul_stickD_of_f_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1) (a : CyclotomicUnitDelta p) :
    S.stickOrdOrd (p - (a : ZMod p).val) =
      (a : ZMod p).val * S.stickD := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hℓ_two : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  have h_card : Fintype.card k = ℓ := by
    rw [S.card_k, hf, pow_one]
  have hpd : p * S.stickD = ℓ - 1 := by
    rw [S.toConductorFlexibleTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one,
      h_card]
  have hD_pos : 0 < S.stickD := by
    by_contra hpos
    have hD_zero : S.stickD = 0 := Nat.eq_zero_of_not_pos hpos
    have hℓ_sub_zero : ℓ - 1 = 0 := by
      rw [← hpd, hD_zero, mul_zero]
    omega
  have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
  have harg_lt : (a : ZMod p).val * S.stickD < ℓ := by
    have hmul_lt :
        (a : ZMod p).val * S.stickD < p * S.stickD :=
      Nat.mul_lt_mul_of_pos_right ha_lt hD_pos
    rw [hpd] at hmul_lt
    omega
  unfold ConductorFlexibleTraceFormStickelbergerSetup.stickOrdOrd
    ConductorFlexibleTraceFormStickelbergerSetup.stickOrd
  rw [show p - (p - (a : ZMod p).val) = (a : ZMod p).val by omega]
  exact digitSum_eq_self_of_lt hℓ_two harg_lt

/-- Flexible divisibility form of the split reciprocal Dwork exponent
normalization. -/
theorem descentRamificationIdx_dvd_p_mul_stickOrdOrd_sub_val_of_f_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1)
    (he : S.concrete.descentRamificationIdx = ℓ - 1)
    (a : CyclotomicUnitDelta p) :
    S.concrete.descentRamificationIdx ∣
      p * S.stickOrdOrd (p - (a : ZMod p).val) := by
  have h_card : Fintype.card k = ℓ := by
    rw [S.card_k, hf, pow_one]
  have hpd : p * S.stickD = ℓ - 1 := by
    rw [S.toConductorFlexibleTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one,
      h_card]
  have hord :=
    S.stickOrdOrd_sub_val_eq_val_mul_stickD_of_f_eq_one hf a
  rw [he, hord]
  refine ⟨(a : ZMod p).val, ?_⟩
  nlinarith

/-- Flexible quotient form of the split reciprocal Dwork exponent
normalization. -/
theorem dworkExponent_sub_val_div_descentRamificationIdx_eq_val_of_f_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1)
    (he : S.concrete.descentRamificationIdx = ℓ - 1)
    (a : CyclotomicUnitDelta p) :
    (p * S.stickOrdOrd (p - (a : ZMod p).val)) /
        S.concrete.descentRamificationIdx =
      (a : ZMod p).val := by
  have hℓ_sub_pos : 0 < ℓ - 1 := by
    have hℓ_two : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
    omega
  have h_card : Fintype.card k = ℓ := by
    rw [S.card_k, hf, pow_one]
  have hpd : p * S.stickD = ℓ - 1 := by
    rw [S.toConductorFlexibleTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one,
      h_card]
  have hord :=
    S.stickOrdOrd_sub_val_eq_val_mul_stickD_of_f_eq_one hf a
  have hnum :
      p * S.stickOrdOrd (p - (a : ZMod p).val) =
        (ℓ - 1) * (a : ZMod p).val := by
    rw [hord]
    nlinarith
  rw [he, hnum, Nat.mul_comm (ℓ - 1) ((a : ZMod p).val),
    Nat.mul_div_left _ hℓ_sub_pos]

/-- Arbitrary-residue-degree Dwork exponent formula before dividing by the
descent ramification index.

This replaces the residue-degree-one digit argument by the cyclic carry
calculation over the Frobenius orbit of `ℓ mod p`. -/
theorem p_mul_stickOrdOrd_sub_val_eq_ell_sub_one_mul_residueOrbitSum_of_f_eq_orderOf
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hℓp : ℓ.Coprime p)
    (hf : S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (a : CyclotomicUnitDelta p) :
    p * S.stickOrdOrd (p - (a : ZMod p).val) =
      (ℓ - 1) *
        ∑ i ∈ Finset.range
          (orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)),
          residueOrbit ℓ p (a : ZMod p).val i := by
  classical
  let u : CyclotomicUnitDelta p := ZMod.unitOfCoprime ℓ hℓp
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hℓ_pos : 0 < ℓ := (Fact.out : Nat.Prime ℓ).pos
  have hℓ_one : 1 < ℓ := (Fact.out : Nat.Prime ℓ).one_lt
  have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
  have hpow_zmod : ((ℓ ^ orderOf u : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    have hval : ((u ^ orderOf u : CyclotomicUnitDelta p) : ZMod p) = (1 : ZMod p) :=
      congrArg (fun x : CyclotomicUnitDelta p => (x : ZMod p))
        (pow_orderOf_eq_one u)
    have hleft : ((u ^ orderOf u : CyclotomicUnitDelta p) : ZMod p) =
        ((ℓ ^ orderOf u : ℕ) : ZMod p) := by
      rw [Units.val_pow_eq_pow_val]
      have hu : (u : ZMod p) = (ℓ : ZMod p) := by
        simp [u, ZMod.coe_unitOfCoprime]
      rw [hu]
      simp
    rw [← hleft]
    have hone : (1 : ZMod p) = ((1 : ℕ) : ZMod p) := by norm_num
    exact hval.trans hone
  have hpow : ℓ ^ orderOf u ≡ 1 [MOD p] :=
    (ZMod.natCast_eq_natCast_iff (ℓ ^ orderOf u) 1 p).mp hpow_zmod
  have hdiv : p ∣ ℓ ^ orderOf u - 1 := by
    have hle : 1 ≤ ℓ ^ orderOf u := Nat.one_le_pow (orderOf u) ℓ hℓ_pos
    exact (Nat.modEq_iff_dvd' hle).mp hpow.symm
  have hstick :
      S.stickOrdOrd (p - (a : ZMod p).val) =
        digitSum ℓ ((a : ZMod p).val * ((ℓ ^ orderOf u - 1) / p)) := by
    unfold ConductorFlexibleTraceFormStickelbergerSetup.stickOrdOrd
      ConductorFlexibleTraceFormStickelbergerSetup.stickOrd
      ConductorFlexibleTraceFormStickelbergerSetup.stickD
    rw [show p - (p - (a : ZMod p).val) = (a : ZMod p).val by omega]
    rw [S.card_k, hf]
  rw [hstick]
  simpa [u] using
    (p_mul_digitSum_mul_div_eq_ell_sub_one_mul_residueOrbitSum
      (ℓ := ℓ) (p := p) (A := (a : ZMod p).val) (f := orderOf u)
      hℓ_one hp_pos ha_lt hpow hdiv)

/-- Arbitrary-residue-degree Dwork exponent formula collected over the
collapsed Frobenius coset, hence expressed as the repeated Stickelberger
multiplicity of the actual conjugate prime. -/
theorem p_mul_stickOrdOrd_sub_val_eq_descentRamificationIdx_mul_repeatedMultiplicity_of_f_eq_orderOf
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hℓp : ℓ.Coprime p)
    (hf : S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he : S.concrete.descentRamificationIdx = ℓ - 1)
    (a : CyclotomicUnitDelta p) :
    p * S.stickOrdOrd (p - (a : ZMod p).val) =
      S.concrete.descentRamificationIdx *
        S.StickelbergerRepeatedMultiplicity
          (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.concrete.descentPrime) := by
  classical
  rw [he]
  calc
    p * S.stickOrdOrd (p - (a : ZMod p).val) =
        (ℓ - 1) *
          ∑ i ∈ Finset.range
            (orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)),
            residueOrbit ℓ p (a : ZMod p).val i :=
      S.p_mul_stickOrdOrd_sub_val_eq_ell_sub_one_mul_residueOrbitSum_of_f_eq_orderOf
        hℓp hf a
    _ = (ℓ - 1) *
        S.StickelbergerRepeatedMultiplicity
          (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.concrete.descentPrime) := by
      rw [S.StickelbergerRepeatedMultiplicity_conjugate_eq_frobeniusCosetSum hℓp a,
        frobeniusCosetWeightSum_eq_residueOrbitSum hℓp a]



end ConductorFlexibleFullTeichDworkSetup




end Furtwaengler

end BernoulliRegular

end

end
