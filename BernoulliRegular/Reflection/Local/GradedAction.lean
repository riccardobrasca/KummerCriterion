module

public import BernoulliRegular.Reflection.Local.DeltaAction
public import BernoulliRegular.Reflection.SingularKummer.CharacterProjection

/-!
# Delta action on completed local graded pieces

This file starts REF-11c.  It packages the first completed graded quotient
`completed U_1 / completed U_2`, gives it the induced cyclotomic `Delta`
action, and records the Teichmuller action on the distinguished zeta class.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section AlgebraLemmas

variable {R : Type*} [CommRing R] (I : Ideal R)

private theorem pow_sub_natCast_mul_pow_mem_succ_of_sub_mem_sq
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) {A n : ℕ}
    (hxy : y - (A : R) * x ∈ I ^ 2) :
    y ^ n - (A ^ n : R) * x ^ n ∈ I ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hleft : (y ^ n - (A ^ n : R) * x ^ n) * y ∈ I ^ (n + 2) := by
        have hmul : (y ^ n - (A ^ n : R) * x ^ n) * y ∈ I ^ (n + 1) * I :=
          Ideal.mul_mem_mul ih hy
        simpa [pow_succ, Nat.add_assoc] using hmul
      have hxpow : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
      have hright : ((A ^ n : R) * x ^ n) * (y - (A : R) * x) ∈ I ^ (n + 2) := by
        have hmul : x ^ n * (y - (A : R) * x) ∈ I ^ n * I ^ 2 :=
          Ideal.mul_mem_mul hxpow hxy
        have hmul' : x ^ n * (y - (A : R) * x) ∈ I ^ (n + 2) := by
          simpa [pow_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul
        simpa [mul_assoc] using Ideal.mul_mem_left (I ^ (n + 2)) (A ^ n : R) hmul'
      have hsum :
          (y ^ n - (A ^ n : R) * x ^ n) * y +
              ((A ^ n : R) * x ^ n) * (y - (A : R) * x) ∈ I ^ (n + 2) :=
        Ideal.add_mem _ hleft hright
      convert hsum using 1
      simp only [pow_succ]
      ring

private theorem one_add_pow_sub_one_sub_natCast_mul_mem_pow_succ
    {n : ℕ} (hn : 1 ≤ n) {x : R} (hx : x ∈ I ^ n) (k : ℕ) :
    (1 + x) ^ k - 1 - (k : R) * x ∈ I ^ (n + 1) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hleft :
          ((1 + x) ^ k - 1 - (k : R) * x) * (1 + x) ∈ I ^ (n + 1) :=
        Ideal.mul_mem_right (1 + x) (I ^ (n + 1)) ih
      have hxx : x * x ∈ I ^ (n + 1) := by
        have hx2 : x * x ∈ I ^ n * I ^ n := Ideal.mul_mem_mul hx hx
        have hx2' : x * x ∈ I ^ (n + n) := by
          simpa [pow_add] using hx2
        exact Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + n) hx2'
      have hright : (k : R) * (x * x) ∈ I ^ (n + 1) :=
        Ideal.mul_mem_left (I ^ (n + 1)) (k : R) hxx
      have hsum :
          ((1 + x) ^ k - 1 - (k : R) * x) * (1 + x) +
              (k : R) * (x * x) ∈ I ^ (n + 1) :=
        Ideal.add_mem _ hleft hright
      convert hsum using 1
      rw [pow_succ, Nat.cast_succ]
      ring

end AlgebraLemmas

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The local cyclotomic action sends the distinguished root of unity to its
Teichmuller power. -/
@[simp]
theorem localCyclotomicUnitEquiv_zetaUnit
    (a : CyclotomicUnitDelta p) :
    localCyclotomicUnitEquiv (p := p) K a (localCyclotomicZetaUnit p K) =
      localCyclotomicZetaUnit p K ^ (a : ZMod p).val := by
  apply Units.ext
  change localCyclotomicRingEquiv (p := p) K a
      ((localCyclotomicZetaUnit p K : localCyclotomicUnitGroup p K) :
        localCyclotomicRing p K) =
    ((localCyclotomicZetaUnit p K ^ (a : ZMod p).val :
      localCyclotomicUnitGroup p K) : localCyclotomicRing p K)
  rw [localCyclotomicZetaUnit_coe, localCyclotomicRingEquiv_algebraMap]
  simp only [Units.val_pow_eq_pow_val, localCyclotomicZetaUnit_coe]
  rw [← map_pow]
  change algebraMap (𝓞 K) (localCyclotomicRing p K)
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        (zeta_spec p ℚ K).toInteger) =
    algebraMap (𝓞 K) (localCyclotomicRing p K)
      ((zeta_spec p ℚ K).toInteger ^ (a : ZMod p).val)
  congr 1
  change cyclotomicSigmaOfUnit (p := p) K a • (zeta_spec p ℚ K).toInteger =
    (zeta_spec p ℚ K).toInteger ^ (a : ZMod p).val
  exact cyclotomicSigmaOfUnit_smul_zetaInteger (p := p) (K := K) a

@[simp]
theorem completedLocalCyclotomicRingEquiv_algebraMap
    (a : CyclotomicUnitDelta p) (x : localCyclotomicRing p K) :
    completedLocalCyclotomicRingEquiv (p := p) K a
        (algebraMap (localCyclotomicRing p K) (completedLocalCyclotomicRing p K) x) =
      algebraMap (localCyclotomicRing p K) (completedLocalCyclotomicRing p K)
        (localCyclotomicRingEquiv (p := p) K a x) := by
  let M := localCyclotomicMaximalIdeal p K
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_completedLocalCyclotomicRingEquiv]
  change Ideal.quotientMap (M ^ n)
      (localCyclotomicRingEquiv (p := p) K a :
        localCyclotomicRing p K →+* localCyclotomicRing p K)
      (ideal_pow_le_comap_ringEquiv_of_map_eq (I := M)
        (localCyclotomicRingEquiv (p := p) K a)
        (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
          (p := p) (K := K) a)
        n)
      (AdicCompletion.evalₐ M n
        (algebraMap (localCyclotomicRing p K) (AdicCompletion M (localCyclotomicRing p K))
          x)) =
    AdicCompletion.evalₐ M n
      (algebraMap (localCyclotomicRing p K) (AdicCompletion M (localCyclotomicRing p K))
        (localCyclotomicRingEquiv (p := p) K a x))
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]
  simp

/-- The completed cyclotomic action sends the distinguished root of unity to
its Teichmuller power. -/
@[simp]
theorem completedLocalCyclotomicUnitEquiv_zetaUnit
    (a : CyclotomicUnitDelta p) :
    completedLocalCyclotomicUnitEquiv (p := p) K a
        (completedLocalCyclotomicZetaUnit p K) =
      completedLocalCyclotomicZetaUnit p K ^ (a : ZMod p).val := by
  apply Units.ext
  change completedLocalCyclotomicRingEquiv (p := p) K a
      ((completedLocalCyclotomicZetaUnit p K :
        completedLocalCyclotomicUnitGroup p K) : completedLocalCyclotomicRing p K) =
    ((completedLocalCyclotomicZetaUnit p K ^ (a : ZMod p).val :
      completedLocalCyclotomicUnitGroup p K) : completedLocalCyclotomicRing p K)
  rw [completedLocalCyclotomicZetaUnit_coe, completedLocalCyclotomicRingEquiv_algebraMap]
  have hlocal := congrArg
    (fun u : localCyclotomicUnitGroup p K => (u : localCyclotomicRing p K))
    (localCyclotomicUnitEquiv_zetaUnit (p := p) (K := K) a)
  change localCyclotomicRingEquiv (p := p) K a
      (localCyclotomicZetaUnit p K : localCyclotomicRing p K) =
    ((localCyclotomicZetaUnit p K ^ (a : ZMod p).val :
      localCyclotomicUnitGroup p K) : localCyclotomicRing p K) at hlocal
  rw [hlocal]
  simp [completedLocalCyclotomicZetaUnit_coe, map_pow]


end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular

end
