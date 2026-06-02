module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitVectors
public import Mathlib.Data.Fintype.Units
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Full-Teichmüller Stickelberger setup (REF-18c2c4-L2c3d-0)

The route-D proof of the digit-sum Stickelberger congruence requires a
multiplicative section
`teichUnitFull : kˣ →* (𝓞 R')ˣ` whose values reduce modulo `Q` to the
identity on `kˣ`. Such a section has order exactly `q − 1` (with
`q = #k`), and exists in the integral closure as soon as `R'` contains
primitive `(q − 1)`-th roots of unity.

The base `TraceFormStickelbergerSetup` only requires
`[IsCyclotomicExtension {p, ℓ} ℚ R']`, which gives `lcm(p, ℓ)`-th roots
only — generally insufficient. The reviewer's recommended fix is an
extension layer that takes the order-`(q−1)` Teichmüller as an explicit
bundle hypothesis. Concrete instances are constructed over the auxiliary
field `R' = ℚ(ζ_{ℓ(q−1)})` (which contains both `ζ_p` and `ζ_{q−1}`,
since `p ∣ q−1`).

## Main definition

* `FullTeichStickelbergerSetup`: extends `TraceFormStickelbergerSetup`
  with `teichUnitFull` plus the residue compatibility identity and the
  bridge to `residueCharInt`.

## Downstream usage

The Wave-2 Stickelberger lemmas
(`teichUnitFull_sum_pow_units`,
`residueCharInt_rec_eq_teichUnitFull_pow`,
`digit_expansion_inner_sum_eval`,
`leadingCoeff_not_mem_Q`)
are stated against this richer setup; the existing arithmetic /
digit-vector layer (Wave-1) remains stated against the base
`TraceFormStickelbergerSetup` and is reused unchanged through the
inheritance. The actual digit-sum Stickelberger statements
(`gaussSumIntRec_mem_Q_pow_stickOrd_dwork`,
`gaussSumIntRec_not_mem_Q_pow_stickOrd_succ_dwork`, and assemblies)
live on the further refinement `FullTeichDworkSetup` in
`DworkAssembly.lean`, which carries the Dwork splitting expansion that
correctly replaces the originally-planned (false) denominator-cleared
digit-bounded expansion.

## Constructibility note

A concrete `FullTeichStickelbergerSetup` is **not** constructed in this
file. The instance over `R' = ℚ(ζ_{ℓ(q−1)})` (with the canonical
Teichmüller given by Hensel-lifted `(q−1)`-th roots) is tracked
separately. The uniformizer fact `pi_not_mem_Q_sq` is inherited from
the base setup and remains valid at the enlarged conductor `ℓ(q−1)`
because the ramification index at `ℓ` is still `ℓ − 1`
(`IsCyclotomicExtension.Rat.ramificationIdx_eq` with `n = ℓ^1·(q−1)`,
`ℓ ∤ (q−1)`).
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- Full-Teichmüller refinement of `TraceFormStickelbergerSetup`. Adds
an order-`(q − 1)` multiplicative section `teichUnitFull : kˣ →* (𝓞 R')ˣ`
of the residue map, together with the bridge identity
`residueCharInt(x) = teichUnitFull(x)^d` where `d = (q − 1)/p`.

A concrete instance requires `R'` to contain primitive `(q − 1)`-th
roots of unity (e.g., as supplied by
`[IsCyclotomicExtension {ℓ * (#k − 1)} ℚ R']`). At the structure level,
this is encoded as a hypothesis (`teichUnitFull` is supplied by the
user). -/
structure FullTeichStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] extends
    TraceFormStickelbergerSetup ℓ p k K R' where
  /-- Multiplicative section `kˣ →* (𝓞 R')ˣ` of the residue map. Its
  values reduce modulo `Q` to the identity on `kˣ` and have order
  dividing `q − 1` (= `#k − 1`). -/
  teichUnitFull : kˣ →* (𝓞 R')ˣ
  /-- Residue compatibility: `teichUnitFull` is a section of the
  composed map `(𝓞 R')ˣ →* (𝓞 R'/Q)ˣ ≃* kˣ`. -/
  teichUnitFull_residue :
    ∀ x : kˣ,
      toConcreteStickelbergerSetup.residueQuotientEquiv
          (Ideal.Quotient.mk toConcreteStickelbergerSetup.Q
            (teichUnitFull x : 𝓞 R')) =
        (x : k)
  /-- The integral residue character is the `d`-th power of the full
  Teichmüller, where `d = (#k − 1) / p`. -/
  residueCharInt_eq_teichUnitFull_pow_d :
    ∀ x : kˣ,
      toConcreteStickelbergerSetup.residueCharInt (x : k) =
        ((teichUnitFull x : 𝓞 R') ^ ((Fintype.card k - 1) / p) : 𝓞 R')

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

















end TraceFormStickelbergerSetup

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : FullTeichStickelbergerSetup ℓ p k K R')

/-- The underlying integral element of a Teichmüller value. -/
def teichUnitFullVal (x : kˣ) : 𝓞 R' := (S.teichUnitFull x : 𝓞 R')

/-- Multiplicativity of the integral Teichmüller value. -/
@[simp]
theorem teichUnitFullVal_mul (x y : kˣ) :
    S.teichUnitFullVal (x * y) =
      S.teichUnitFullVal x * S.teichUnitFullVal y := by
  unfold teichUnitFullVal
  rw [map_mul]
  rfl


/-- Compatibility of the integral Teichmüller value with powers in `kˣ`. -/
@[simp]
theorem teichUnitFullVal_pow (x : kˣ) (n : ℕ) :
    S.teichUnitFullVal (x ^ n) = S.teichUnitFullVal x ^ n := by
  unfold teichUnitFullVal
  rw [map_pow]
  rfl

/-- The Teichmüller residue identity in residue-map form: applying
`residueMap` to `teichUnitFullVal x` yields `x` (as an element of `k`). -/
theorem residueMap_teichUnitFullVal (x : kˣ) :
    S.residueMap (S.teichUnitFullVal x) = (x : k) := by
  unfold teichUnitFullVal
  -- residueMap factors as `Quotient.mk` then `residueQuotientEquiv`.
  have h := S.teichUnitFull_residue x
  rw [← S.toConcreteStickelbergerSetup.residueQuotientEquiv_mk]
  exact h

section TeichOrthogonality

variable [DecidableEq k]

omit [DecidableEq k] in
/-- The integral Teichmüller value has order dividing `q - 1` (= `#k - 1`).
This follows from `teichUnitFull` being a `MonoidHom` from `kˣ` and
`x^(#kˣ) = 1`. -/
theorem teichUnitFullVal_pow_card_sub_one (x : kˣ) :
    S.teichUnitFullVal x ^ (Fintype.card k - 1) = 1 := by
  haveI : DecidableEq k := Classical.decEq _
  unfold teichUnitFullVal
  -- Reduce via Units.val_pow and map_pow.
  rw [show (Fintype.card k - 1) = Fintype.card kˣ from
    (Fintype.card_units (α := k)).symm]
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one]
  rfl


/-- **L2c3d-1: full Teichmüller power-sum orthogonality.** -/
theorem teichUnitFull_sum_pow_units (r : ℕ) :
    (∑ x : kˣ, S.teichUnitFullVal x ^ r) =
      if (Fintype.card k - 1) ∣ r
      then (Fintype.card k - 1 : 𝓞 R')
      else 0 := by
  classical
  rcases Decidable.em ((Fintype.card k - 1) ∣ r) with hdvd | hndvd
  · -- (q-1) ∣ r: every term is 1, sum is (number of units) = q - 1.
    rw [if_pos hdvd]
    obtain ⟨c, hc⟩ := hdvd
    have h_term : ∀ x : kˣ, S.teichUnitFullVal x ^ r = 1 := by
      intro x
      rw [hc, pow_mul, S.teichUnitFullVal_pow_card_sub_one, one_pow]
    rw [Finset.sum_congr rfl fun x _ => h_term x]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_units]
    -- `(card k - 1) • (1 : 𝓞 R') = ↑(card k - 1) = ↑(card k) - 1`.
    rw [nsmul_eq_mul, mul_one]
    have hpos : 1 ≤ Fintype.card k := Fintype.card_pos
    rw [Nat.cast_sub hpos, Nat.cast_one]
  · -- (q-1) ∤ r: sum is 0.
    rw [if_neg hndvd]
    -- Choose generator y of kˣ.
    obtain ⟨y, hy⟩ : ∃ y : kˣ, ∀ z : kˣ, z ∈ Subgroup.zpowers y :=
      IsCyclic.exists_generator
    -- t := teichUnitFullVal y. Show (t^r) * sum = sum.
    set t := S.teichUnitFullVal y with ht_def
    have h_t_mul_sum :
        t ^ r * (∑ x : kˣ, S.teichUnitFullVal x ^ r) =
          ∑ x : kˣ, S.teichUnitFullVal x ^ r := by
      rw [Finset.mul_sum]
      -- Term-wise: t^r * (teichUnitFullVal x)^r = teichUnitFullVal(y*x)^r.
      have h_term_mul : ∀ x : kˣ,
          t ^ r * S.teichUnitFullVal x ^ r =
            S.teichUnitFullVal (y * x) ^ r := by
        intro x
        rw [ht_def, ← mul_pow, ← S.teichUnitFullVal_mul]
      rw [Finset.sum_congr rfl fun x _ => h_term_mul x]
      -- Reindex via the bijection `x ↦ y * x` on `kˣ`.
      let e : kˣ ≃ kˣ := Equiv.mulLeft y
      have : (∑ x : kˣ, S.teichUnitFullVal (y * x) ^ r) =
              ∑ x : kˣ, S.teichUnitFullVal (e x) ^ r := rfl
      rw [this]
      exact Finset.sum_equiv e (by simp) (by intros; rfl)
    -- (t^r - 1) * sum = 0.
    have h_factor :
        (t ^ r - 1) * (∑ x : kˣ, S.teichUnitFullVal x ^ r) = 0 := by
      rw [sub_mul, one_mul, sub_eq_zero, h_t_mul_sum]
    -- t^r ≠ 1 because residueMap(t^r) = y^r ≠ 1 in k.
    have h_t_ne : t ^ r ≠ 1 := by
      intro hcontra
      have hres : S.residueMap (t ^ r) = 1 := by
        rw [hcontra]; exact map_one _
      rw [ht_def, map_pow, S.residueMap_teichUnitFullVal] at hres
      -- y^r = 1 in k means (q-1) ∣ r since y has order q-1.
      have h_y_unit_pow : ((y : k) ^ r) = 1 := hres
      -- Lift to kˣ.
      have h_y_pow_unit : (y : kˣ) ^ r = 1 := by
        ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact h_y_unit_pow
      -- Order of y divides r ⇒ (#kˣ) ∣ r ⇒ (q-1) ∣ r.
      have h_ord_dvd : orderOf y ∣ r := orderOf_dvd_of_pow_eq_one h_y_pow_unit
      have h_y_gen : orderOf y = Fintype.card kˣ := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hy, Nat.card_eq_fintype_card]
      rw [h_y_gen, Fintype.card_units] at h_ord_dvd
      exact hndvd h_ord_dvd
    -- (t^r - 1) ≠ 0.
    have h_t_sub_ne : t ^ r - 1 ≠ 0 := sub_ne_zero.mpr h_t_ne
    -- Integral domain: (a - 1) * b = 0 and (a - 1) ≠ 0 ⇒ b = 0.
    rcases mul_eq_zero.mp h_factor with h | h
    · exact absurd h h_t_sub_ne
    · exact h

/-- **L2c3d-5: inner Teichmüller sum evaluation.** The inner sum in the
denominator-cleared digit expansion factors via multiplicativity and
evaluates by Teichmüller power-sum orthogonality. -/
theorem teichUnitFull_innerSum_eval (A M : ℕ) (c : kˣ) :
    (∑ x : kˣ,
        S.teichUnitFullVal x ^ A *
          S.teichUnitFullVal (c * x) ^ M) =
      if (Fintype.card k - 1) ∣ (A + M)
      then (Fintype.card k - 1 : 𝓞 R') *
            S.teichUnitFullVal c ^ M
      else 0 := by
  classical
  -- ω(c·x)^M = ω(c)^M · ω(x)^M.
  have h_term : ∀ x : kˣ,
      S.teichUnitFullVal x ^ A * S.teichUnitFullVal (c * x) ^ M =
        S.teichUnitFullVal c ^ M * S.teichUnitFullVal x ^ (A + M) := by
    intro x
    rw [S.teichUnitFullVal_mul, mul_pow, pow_add]
    ring
  rw [Finset.sum_congr rfl fun x _ => h_term x]
  rw [← Finset.mul_sum]
  rw [S.teichUnitFull_sum_pow_units (A + M)]
  -- Distribute the if/then.
  by_cases hdvd : (Fintype.card k - 1) ∣ (A + M)
  · rw [if_pos hdvd, if_pos hdvd]; ring
  · rw [if_neg hdvd, if_neg hdvd]; ring

end TeichOrthogonality


/-- **L2c3d-2 (raw form): the reciprocal residue character is a power
of the full Teichmüller.** Stated using the raw cofactor
`(#k - 1) / p`; the `stickD`-form wrapper lives in `LeadingTerm.lean`. -/
theorem residueCharInt_rec_eq_teichUnitFull_pow
    (a : ℕ) (_ha₁ : 1 ≤ a) (_ha₂ : a ≤ p - 1) (x : kˣ) :
    S.residueCharInt (x : k) ^ (p - a) =
      (S.teichUnitFull x : 𝓞 R') ^ ((p - a) * ((Fintype.card k - 1) / p)) := by
  rw [S.residueCharInt_eq_teichUnitFull_pow_d x, ← pow_mul, mul_comm]

end FullTeichStickelbergerSetup

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

/-- A natural number not divisible by `ℓ` is a `Q`-unit. -/
theorem natCast_not_mem_Q_of_not_dvd {n : ℕ} (hn : ¬ ℓ ∣ n) :
    (n : 𝓞 R') ∉ S.Q := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  intro hmem
  rw [S.toConcreteStickelbergerSetup.mem_Q_iff_residueMap_eq_zero] at hmem
  rw [map_natCast] at hmem
  exact hn ((CharP.cast_eq_zero_iff k ℓ n).1 hmem)

/-- The cardinality of the residue field has positive `f`-exponent. -/
theorem f_pos : 0 < S.f := by
  have h_card_ge : 2 ≤ Fintype.card k := Fintype.one_lt_card
  have hcard_eq : Fintype.card k = ℓ ^ S.f := S.card_k
  by_contra h
  push Not at h
  have hf : S.f = 0 := Nat.le_zero.mp h
  rw [hf, pow_zero] at hcard_eq
  omega

/-- `ℓ` does not divide `Fintype.card k - 1`. -/
theorem ell_not_dvd_card_k_sub_one (S : TraceFormStickelbergerSetup ℓ p k K R') :
    ¬ ℓ ∣ (Fintype.card k - 1) := by
  intro hdvd
  have hcard_eq : Fintype.card k = ℓ ^ S.f := S.card_k
  have hf_pos : 0 < S.f := S.f_pos
  have hℓ_dvd_card : ℓ ∣ Fintype.card k := by
    rw [hcard_eq]
    exact dvd_pow_self ℓ hf_pos.ne'
  have hcard_pos : 1 ≤ Fintype.card k := Fintype.card_pos
  -- ℓ ∣ card k and ℓ ∣ (card k - 1) ⇒ ℓ ∣ 1.
  have hone : ℓ ∣ 1 := by
    have h := Nat.dvd_sub hℓ_dvd_card hdvd
    rwa [Nat.sub_sub_self hcard_pos] at h
  exact (Fact.out : Nat.Prime ℓ).one_lt.ne' (Nat.dvd_one.mp hone)

/-- The uniformizer `π = ζ_ℓ - 1` is non-zero in `𝓞 R'`. Follows from
`zeta_ell_int` being a primitive `ℓ`-th root of unity with `ℓ ≥ 2`. -/
theorem pi_ne_zero : S.π ≠ 0 := by
  rw [S.toConcreteStickelbergerSetup.π_def]
  intro hc
  have h1 : S.zeta_ell_int = 1 := by linear_combination hc
  have h_prim := S.toConcreteStickelbergerSetup.zeta_ell_int_isPrimitiveRoot
  have hℓ_two_le : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  have h_ord_one : S.zeta_ell_int ^ 1 = 1 := by rw [pow_one]; exact h1
  have h_ord_dvd : ℓ ∣ 1 := h_prim.dvd_of_pow_eq_one 1 h_ord_one
  have : ℓ ≤ 1 := Nat.le_of_dvd (by omega) h_ord_dvd
  omega

end TraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
