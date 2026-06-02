module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup


/-!
# Galois action on the trace-form additive character (REF-18c2c5-b)

This file connects the cyclotomic Galois action on `R'` to the
Stickelberger psi-shift compatibility for trace-form bundles. The key
input is:

  *Hypothesis*: `σ : R' →+* R'` is a ring hom satisfying
  `σ S.zeta_ell = S.zeta_ell ^ c.val` for some `c : (ZMod ℓ)ˣ`.

The output is a unit `a' : kˣ` (the image of `c` in `kˣ` via the
algebra structure `Algebra (ZMod ℓ) k`) such that
`σ.toMonoidHom.compAddChar S.psi = AddChar.mulShift S.psi a'`.

This discharges the **psi-shift content** of `IsGalCompatible`
restricted to the trace-form refinement. Since the trace form is the
canonical form of every primitive additive character on a finite field,
the trace-form proof handles the substantive case.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

/-- The unit in `kˣ` corresponding to a unit in `(ZMod ℓ)ˣ` via the
algebra map `ZMod ℓ → k`. -/
noncomputable def kUnitOfZModUnit (c : (ZMod ℓ)ˣ) : kˣ :=
  Units.map (algebraMap (ZMod ℓ) k).toMonoidHom c

omit [Fintype k] in
@[simp]
theorem kUnitOfZModUnit_val (c : (ZMod ℓ)ˣ) :
    ((kUnitOfZModUnit (k := k) c : kˣ) : k) =
      algebraMap (ZMod ℓ) k (c : ZMod ℓ) := rfl

end TraceFormStickelbergerSetup

namespace ConductorFlexibleTraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')

/-- Order of `S.zeta_ell` in `R'` equals `ℓ`, in the conductor-flexible
trace-form setup. -/
theorem orderOf_zeta_ell : orderOf S.zeta_ell = ℓ :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  S.hzeta_ell.eq_orderOf.symm

/-- Flexible trace-form psi-shift derivation.  For `σ : R' →+* R'` whose
action on `S.zeta_ell` is `ζ_ℓ ↦ ζ_ℓ^c.val`, the additive character is
shifted by the corresponding unit of `k`. -/
theorem psi_shift_of_zetaEll_action
    (σ : R' →+* R') (c : (ZMod ℓ)ˣ)
    (h_act : σ S.zeta_ell = S.zeta_ell ^ (c : ZMod ℓ).val) :
    σ.toMonoidHom.compAddChar S.psi =
      AddChar.mulShift S.psi
        (TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c) := by
  ext x
  change σ (S.psi x) =
    S.psi ((TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c : kˣ) * x)
  rw [ConductorFlexibleTraceFormStickelbergerSetup.psi_eq_zeta_ell_pow_trace,
    ConductorFlexibleTraceFormStickelbergerSetup.psi_eq_zeta_ell_pow_trace,
    map_pow, h_act, ← pow_mul]
  rw [← pow_mod_orderOf S.zeta_ell ((c : ZMod ℓ).val *
        (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val),
      ← pow_mod_orderOf S.zeta_ell
        ((Algebra.trace (ZMod ℓ) k
          ((S.traceScale : k) *
            (((TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c : kˣ)
              : k) * x))).val),
      S.orderOf_zeta_ell]
  congr 1
  have h_trace :
      Algebra.trace (ZMod ℓ) k
          ((S.traceScale : k) *
            (((TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c : kˣ) : k) * x)) =
        (c : ZMod ℓ) *
          Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x) := by
    rw [show
        (S.traceScale : k) *
            (((TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c : kˣ) : k) * x) =
          (c : ZMod ℓ) • ((S.traceScale : k) * x) from ?_]
    · rw [(Algebra.trace (ZMod ℓ) k).map_smul]
      rfl
    · rw [TraceFormStickelbergerSetup.kUnitOfZModUnit_val, Algebra.smul_def]
      ring
  rw [h_trace, ZMod.val_mul, Nat.mod_mod]


end ConductorFlexibleTraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular
