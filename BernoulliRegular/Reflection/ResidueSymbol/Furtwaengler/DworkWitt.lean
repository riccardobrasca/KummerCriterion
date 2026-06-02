module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.FullTeichSetup
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-!
# Witt-vector bridge for Dwork splitting

This file contains the Witt-vector uniqueness bridge needed by the all-order
Artin-Hasse/Dwork splitting proof. The key point is that in every quotient
`𝓞 R' / Q^(N+1)`, the residue characteristic `ℓ` is nilpotent, so mathlib's
Teichmüller-series uniqueness theorem for Witt vectors applies.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

theorem wittGhostComponent_mem_ideal_pow_succ_of_coeff_mem
    {r : ℕ} [Fact (Nat.Prime r)]
    {A : Type*} [CommRing A] (I : Ideal A) (hrI : (r : A) ∈ I)
    {x : WittVector r A} {n : ℕ}
    (hx : ∀ i : ℕ, i ≤ n → x.coeff i ∈ I) :
    WittVector.ghostComponent n x ∈ I ^ (n + 1) := by
  rw [WittVector.ghostComponent_apply, wittPolynomial, MvPolynomial.aeval_sum]
  refine Ideal.sum_mem _ ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  have hi_le : i ≤ n := Nat.le_of_lt_succ hi
  have hterm :
      (MvPolynomial.aeval x.coeff)
          ((MvPolynomial.monomial (R := ℤ) (Finsupp.single i (r ^ (n - i))))
            (r ^ i)) =
        ((r : A) ^ i) * (x.coeff i) ^ (r ^ (n - i)) := by
    simp [MvPolynomial.aeval_monomial, map_pow]
  rw [hterm]
  have hrpow : (r : A) ^ i ∈ I ^ i := Ideal.pow_mem_pow hrI i
  have hxpow : (x.coeff i) ^ (r ^ (n - i)) ∈ I ^ (r ^ (n - i)) :=
    Ideal.pow_mem_pow (hx i hi_le) (r ^ (n - i))
  have hmul :
      ((r : A) ^ i) * (x.coeff i) ^ (r ^ (n - i)) ∈
        I ^ (i + r ^ (n - i)) := by
    have hmul' :
        ((r : A) ^ i) * (x.coeff i) ^ (r ^ (n - i)) ∈
          I ^ i * I ^ (r ^ (n - i)) :=
      Ideal.mul_mem_mul hrpow hxpow
    simpa [pow_add] using hmul'
  exact Ideal.pow_le_pow_right
    (by
      have htwo : 2 ≤ r := (Fact.out : Nat.Prime r).two_le
      have hpow :
          n - i + 1 ≤ r ^ (n - i) :=
        ((n - i).lt_two_pow_self).succ_le.trans
          (pow_left_mono (n - i) htwo)
      omega)
    hmul

theorem witt_ker_map_le_ker_mk_comp_ghostComponent
    {r : ℕ} [Fact (Nat.Prime r)]
    {A : Type*} [CommRing A] (I : Ideal A) (hrI : (r : A) ∈ I) (n : ℕ) :
    RingHom.ker (WittVector.map (Ideal.Quotient.mk I)) ≤
      RingHom.ker
        ((Ideal.Quotient.mk (I ^ (n + 1))).comp (WittVector.ghostComponent (p := r) n)) := by
  intro x hx
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  refine wittGhostComponent_mem_ideal_pow_succ_of_coeff_mem I hrI ?_
  rw [RingHom.mem_ker, WittVector.map_eq_zero_iff] at hx
  intro i _hi
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hx i)

/-- The `n`-th Witt ghost component descends from `W(A/I)` to
`A/I^(n+1)` whenever the Witt prime lies in `I`. -/
noncomputable def wittGhostComponentModIdealPow
    {r : ℕ} [Fact (Nat.Prime r)]
    {A : Type*} [CommRing A] (I : Ideal A) (hrI : (r : A) ∈ I) (n : ℕ) :
    WittVector r (A ⧸ I) →+* A ⧸ I ^ (n + 1) :=
  RingHom.liftOfSurjective (WittVector.map (Ideal.Quotient.mk I))
    (WittVector.map_surjective _ Ideal.Quotient.mk_surjective)
    ⟨(Ideal.Quotient.mk (I ^ (n + 1))).comp (WittVector.ghostComponent (p := r) n),
      witt_ker_map_le_ker_mk_comp_ghostComponent I hrI n⟩

@[simp]
theorem wittGhostComponentModIdealPow_map_mk
    {r : ℕ} [Fact (Nat.Prime r)]
    {A : Type*} [CommRing A] (I : Ideal A) (hrI : (r : A) ∈ I)
    (n : ℕ) (x : WittVector r A) :
    wittGhostComponentModIdealPow I hrI n
        (WittVector.map (Ideal.Quotient.mk I) x) =
      Ideal.Quotient.mk (I ^ (n + 1)) (WittVector.ghostComponent n x) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _

@[simp]
theorem wittGhostComponentModIdealPow_teichmuller_mk
    {r : ℕ} [Fact (Nat.Prime r)]
    {A : Type*} [CommRing A] (I : Ideal A) (hrI : (r : A) ∈ I)
    (n : ℕ) (a : A) :
    wittGhostComponentModIdealPow I hrI n
        (WittVector.teichmuller r (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (I ^ (n + 1)) (a ^ r ^ n) := by
  rw [← WittVector.map_teichmuller r (Ideal.Quotient.mk I) a,
    wittGhostComponentModIdealPow_map_mk, WittVector.ghostComponent_teichmuller]

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

omit [Fintype k] in
/-- Witt Frobenius sends Teichmüller representatives to Teichmüller
representatives of Frobenius powers. -/
theorem witt_frobenius_teichmuller (x : k) :
    WittVector.frobenius (WittVector.teichmuller ℓ x) =
      WittVector.teichmuller ℓ (x ^ ℓ) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller]
  rfl

omit [Fintype k] in
/-- Iterated Witt Frobenius on a Teichmüller representative. -/
theorem witt_iterate_frobenius_teichmuller (i : ℕ) (x : k) :
    (WittVector.frobenius^[i]) (WittVector.teichmuller ℓ x) =
      WittVector.teichmuller ℓ (x ^ (ℓ ^ i)) := by
  induction i with
  | zero =>
      simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, witt_frobenius_teichmuller]
      congr 1
      rw [← pow_mul, Nat.pow_succ]

/-- The finite Witt-Frobenius trace. -/
noncomputable def wittFrobeniusTrace (f : ℕ) (x : WittVector ℓ k) :
    WittVector ℓ k :=
  ∑ i : Fin f, (WittVector.frobenius^[i.1]) x

omit [Fintype k] in
/-- The finite Witt-Frobenius trace of a Teichmüller representative is the
sum of the Teichmüller representatives of its finite-field Frobenius powers. -/
theorem wittFrobeniusTrace_teichmuller (f : ℕ) (x : k) :
    wittFrobeniusTrace (ℓ := ℓ) (k := k) f (WittVector.teichmuller ℓ x) =
      ∑ i : Fin f, WittVector.teichmuller ℓ (x ^ (ℓ ^ (i : ℕ))) := by
  classical
  simp [wittFrobeniusTrace, witt_iterate_frobenius_teichmuller]

omit [Fintype k] in
/-- The zeroth Witt coefficient of the finite Frobenius trace is the usual
finite Frobenius trace sum. -/
theorem wittFrobeniusTrace_teichmuller_coeff_zero (f : ℕ) (x : k) :
    (wittFrobeniusTrace (ℓ := ℓ) (k := k) f
        (WittVector.teichmuller ℓ x)).coeff 0 =
      ∑ i : Fin f, x ^ (ℓ ^ (i : ℕ)) := by
  classical
  rw [wittFrobeniusTrace_teichmuller]
  change WittVector.constantCoeff
      (∑ i : Fin f, WittVector.teichmuller ℓ (x ^ (ℓ ^ (i : ℕ)))) =
    ∑ i : Fin f, x ^ (ℓ ^ (i : ℕ))
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact WittVector.teichmuller_coeff_zero (p := ℓ) (x ^ (ℓ ^ (i : ℕ)))

omit [Fintype k] in
/-- Every Witt vector is congruent modulo `ℓ` to the Teichmüller lift of its
zeroth coefficient. -/
theorem wittVector_sub_teichmuller_coeff_zero_dvd_prime
    [PerfectRing k ℓ] (x : WittVector ℓ k) :
    (ℓ : WittVector ℓ k) ∣ x - WittVector.teichmuller ℓ (x.coeff 0) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  have h :=
    (WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := ℓ) x 0)
  have hsum :
      (∑ i ∈ Finset.Iic 0,
          WittVector.teichmuller ℓ (((_root_.frobeniusEquiv k ℓ).symm ^ i) (x.coeff i)) *
            (ℓ : WittVector ℓ k) ^ i) =
        WittVector.teichmuller ℓ (x.coeff 0) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hne
      exact (hne (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp hi))).elim
    · intro hnot
      exact (hnot (Finset.mem_Iic.mpr le_rfl)).elim
  rw [hsum] at h
  simpa using h

omit [Fintype k] in
/-- The finite Witt-Frobenius trace differs from the Teichmüller lift of its
zeroth finite-field trace coefficient by an `ℓ`-multiple. -/
theorem wittFrobeniusTrace_teichmuller_sub_teichmuller_coeff_zero_dvd_prime
    [PerfectRing k ℓ] (f : ℕ) (x : k) :
    (ℓ : WittVector ℓ k) ∣
      wittFrobeniusTrace (ℓ := ℓ) (k := k) f (WittVector.teichmuller ℓ x) -
        WittVector.teichmuller ℓ (∑ i : Fin f, x ^ (ℓ ^ (i : ℕ))) := by
  simpa [wittFrobeniusTrace_teichmuller_coeff_zero] using
    wittVector_sub_teichmuller_coeff_zero_dvd_prime
      (ℓ := ℓ)
      (x := wittFrobeniusTrace (ℓ := ℓ) (k := k) f (WittVector.teichmuller ℓ x))

omit [Fintype k] in
/-- A natural representative of an element of `ZMod ℓ`, viewed as a Witt
vector over `k`, differs from the Teichmüller lift of that residue class by
an `ℓ`-multiple. -/
theorem natCast_zmod_val_sub_teichmuller_dvd_prime
    [PerfectRing k ℓ] (a : ZMod ℓ) :
    (ℓ : WittVector ℓ k) ∣
      ((a.val : ℕ) : WittVector ℓ k) -
        WittVector.teichmuller ℓ (algebraMap (ZMod ℓ) k a) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  have hcoeff :
      (((a.val : ℕ) : WittVector ℓ k).coeff 0) =
        algebraMap (ZMod ℓ) k a := by
    change WittVector.constantCoeff (((a.val : ℕ) : WittVector ℓ k)) =
      algebraMap (ZMod ℓ) k a
    rw [map_natCast]
    have h := congrArg (algebraMap (ZMod ℓ) k) (ZMod.natCast_zmod_val a)
    rw [map_natCast] at h
    exact h
  have h :=
    wittVector_sub_teichmuller_coeff_zero_dvd_prime
      (ℓ := ℓ) (k := k) (x := ((a.val : ℕ) : WittVector ℓ k))
  rw [hcoeff] at h
  exact h

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- Fontaine-style `Q`-adic ghost map from Witt vectors over the concrete
residue-field model to the quotient `𝓞 R' / Q^(N+1)`.

The inverse Frobenius twist is the standard one: on Teichmüller inputs it
lets the `N`-th ghost component recover the selected Teichmüller lift at
precision `N`. -/
noncomputable def wittThetaModQPow (N : ℕ) :
    WittVector ℓ k →+* (𝓞 R' ⧸ S.Q ^ (N + 1)) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  exact
    (wittGhostComponentModIdealPow S.Q S.hQ N).comp
      ((WittVector.map S.residueQuotientEquiv.symm.toRingHom).comp
        (WittVector.map ((_root_.iterateFrobeniusEquiv k ℓ N).symm.toRingHom)))



end ConcreteStickelbergerSetup

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (F : FullTeichStickelbergerSetup ℓ p k K R')

/-- On a Teichmüller unit, the concrete Fontaine-style Witt map recovers the
chosen integral Teichmüller lift modulo `Q^(N+1)`, provided `xN` is the
inverse-Frobenius preimage used by the map. -/
theorem wittThetaModQPow_teichmuller_unit_of_pow
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (x xN : kˣ)
    (hxN :
      ((_root_.iterateFrobeniusEquiv k ℓ N).symm (x : k)) = (xN : k))
    (hxNpow : xN ^ (ℓ ^ N) = x) :
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (WittVector.teichmuller ℓ (x : k)) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  have hquot :
      F.toConcreteStickelbergerSetup.residueQuotientEquiv.symm (xN : k) =
        Ideal.Quotient.mk F.Q (F.teichUnitFullVal xN) := by
    apply F.toConcreteStickelbergerSetup.residueQuotientEquiv.injective
    simp [F.residueMap_teichUnitFullVal xN]
  have hquot' :
      F.toConcreteStickelbergerSetup.residueQuotientEquiv.symm.toRingHom (xN : k) =
        Ideal.Quotient.mk F.Q (F.teichUnitFullVal xN) := hquot
  have hxN' :
      (_root_.iterateFrobeniusEquiv k ℓ N).symm.toRingHom (x : k) = (xN : k) := hxN
  rw [ConcreteStickelbergerSetup.wittThetaModQPow]
  simp only [RingHom.comp_apply]
  rw [WittVector.map_teichmuller, hxN', WittVector.map_teichmuller, hquot',
    wittGhostComponentModIdealPow_teichmuller_mk, ← F.teichUnitFullVal_pow, hxNpow]

omit [Fact (Nat.Prime ℓ)] [Fintype k] [Algebra (ZMod ℓ) k] in
/-- The inverse iterated Frobenius preimage of a residue-field unit. -/
noncomputable def frobeniusUnitPreimage
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) : kˣ :=
  Units.mapEquiv ((_root_.iterateFrobeniusEquiv k ℓ N).symm.toMulEquiv) x

omit [Fact (Nat.Prime ℓ)] [Fintype k] [Algebra (ZMod ℓ) k] in
@[simp]
theorem frobeniusUnitPreimage_val
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) :
    (frobeniusUnitPreimage (ℓ := ℓ) N x : k) =
      (_root_.iterateFrobeniusEquiv k ℓ N).symm (x : k) := by
  rfl

omit [Fact (Nat.Prime ℓ)] [Fintype k] [Algebra (ZMod ℓ) k] in
theorem frobeniusUnitPreimage_pow
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) :
    frobeniusUnitPreimage (ℓ := ℓ) N x ^ (ℓ ^ N) = x := by
  ext
  rw [Units.val_pow_eq_pow_val, frobeniusUnitPreimage_val]
  change ((_root_.iterateFrobeniusEquiv k ℓ N)
      ((_root_.iterateFrobeniusEquiv k ℓ N).symm (x : k))) = (x : k)
  rw [RingEquiv.apply_symm_apply]

/-- The concrete Teichmüller lift extended from units to all residue-field
elements by sending `0` to `0`. -/
noncomputable def teichFullVal
    (F : FullTeichStickelbergerSetup ℓ p k K R') (x : k) : 𝓞 R' := by
  classical
  exact if hx : x = 0 then 0 else F.teichUnitFullVal (Units.mk0 x hx)





/-- On a Teichmüller unit, the concrete Fontaine-style Witt map recovers the
chosen integral Teichmüller lift modulo `Q^(N+1)`. -/
theorem wittThetaModQPow_teichmuller_unit
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) :
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (WittVector.teichmuller ℓ (x : k)) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x) := by
  refine F.wittThetaModQPow_teichmuller_unit_of_pow
    N x (frobeniusUnitPreimage (ℓ := ℓ) N x) ?_ ?_
  · exact (frobeniusUnitPreimage_val (ℓ := ℓ) N x).symm
  · exact frobeniusUnitPreimage_pow (ℓ := ℓ) N x




end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
