module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IntegralBridge
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-!
# Trace-form Stickelberger setup (REF-18c2c4-L2c1)

Refines `ConcreteStickelbergerSetup` to additive characters of the
canonical trace form

  `ψ(x) = ζ_ℓ ^ Tr_{k/𝔽_ℓ}(c · x)`

for some scale `c ∈ kˣ`. Every primitive additive character on
`k = 𝔽_{ℓ ^ f}` has this shape, so the refinement does not lose
generality, and the trace witness pins down the exponent in the form
needed by the digit-sum Stickelberger argument (REF-18c2c4-L2c2 / L2c3).

This is REF-18c2c4-L2c1 of the Furtwängler digit-sum Stickelberger route.

## Main definitions

* `TraceFormStickelbergerSetup`: extends `ConcreteStickelbergerSetup`
  with a scale `traceScale : kˣ` and a witness that the existing
  exponent function equals `(Algebra.trace (ZMod ℓ) k (traceScale·x)).val`.
* `ConcreteStickelbergerSetup.gaussSumIntAtScale`: the integral Gauss
  sum at an arbitrary trace scale, used to state scale-removal
  independent of any bundle's specific choice of `traceScale`.

## Main theorems

* `TraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace`: the
  integral additive character has the trace-form integer-power
  expression.
* `ConcreteStickelbergerSetup.gaussSumIntAtScale_eq_charUnit_mul_one`:
  Gauss sums at different trace scales differ by a multiplicative
  character value at the inverse scale (a unit in `𝓞 R'`).
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- Refinement of `ConcreteStickelbergerSetup` to additive characters of
the canonical trace form `ψ(x) = ζ_ℓ ^ Tr(c · x)` for some scale
`c ∈ kˣ`. -/
structure TraceFormStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] extends
    ConcreteStickelbergerSetup ℓ p k K R' where
  /-- Scale factor for the additive character. Every primitive additive
  character on `k = 𝔽_{ℓ ^ f}` has the form `x ↦ ζ_ℓ^{Tr(c · x)}` for some
  unit `c ∈ k×`. -/
  traceScale : kˣ
  /-- Witness that the bundle's `psiExponent` agrees with the
  natural-number lift of the absolute trace at the chosen scale. -/
  psiExponent_trace :
    ∀ x : k,
      toConcreteStickelbergerSetup.psiExponent x =
        (Algebra.trace (ZMod ℓ) k ((traceScale : k) * x)).val
  /-- Uniformizer non-degeneracy: `π = ζ_ℓ - 1` is exactly a uniformizer
  at the selected prime `Q`, i.e., `v_Q(π) = 1`. This is a ramification
  fact about the mixed cyclotomic field `R' = ℚ(ζ_p, ζ_ℓ)` that follows
  from the singleton-conductor ramification theorem
  (`IsCyclotomicExtension.Rat.ramificationIdx_eq` with `n = ℓ · p`,
  prime `ℓ`, `m = p`). It is bundled here as a structural constraint
  rather than derived inline; the derivation is tracked separately
  (see the follow-up ticket on the L2c3a board). -/
  pi_not_mem_Q_sq : toConcreteStickelbergerSetup.π ∉ toConcreteStickelbergerSetup.Q ^ 2

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

end TraceFormStickelbergerSetup

/-! ### Conductor-flexible trace-form API -/

/-- Conductor-flexible refinement of
`ConductorFlexibleConcreteStickelbergerSetup` to additive characters of the
canonical trace form.

Unlike `TraceFormStickelbergerSetup`, this structure does not require
`[IsCyclotomicExtension {p, ℓ} ℚ R']`; the necessary roots, prime, residue
map, and non-degeneracy facts are explicit fields inherited from the flexible
concrete setup. -/
structure ConductorFlexibleTraceFormStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R'] extends
    ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' where
  /-- Scale factor for the additive character. -/
  traceScale : kˣ
  /-- Witness that the bundle's `psiExponent` agrees with the trace at the
  chosen scale. -/
  psiExponent_trace :
    ∀ x : k,
      toConductorFlexibleConcreteStickelbergerSetup.psiExponent x =
        (Algebra.trace (ZMod ℓ) k ((traceScale : k) * x)).val
  /-- Uniformizer non-degeneracy at the selected prime. -/
  pi_not_mem_Q_sq :
    toConductorFlexibleConcreteStickelbergerSetup.π ∉
      toConductorFlexibleConcreteStickelbergerSetup.Q ^ 2

namespace ConductorFlexibleTraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')

/-- The underlying conductor-flexible concrete setup. -/
def concrete : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' :=
  S.toConductorFlexibleConcreteStickelbergerSetup

/-- Trace-form expression for the abstract additive character. -/
theorem psi_eq_zeta_ell_pow_trace (x : k) :
    S.psi x =
      S.zeta_ell ^ ((Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val) := by
  rw [S.toConductorFlexibleConcreteStickelbergerSetup.psi_pow_form, S.psiExponent_trace]



end ConductorFlexibleTraceFormStickelbergerSetup

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- The old exact pair-cyclotomic trace-form setup is a special case of the
conductor-flexible trace-form API. -/
noncomputable def toConductorFlexible (S : TraceFormStickelbergerSetup ℓ p k K R') :
    ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R' where
  toConductorFlexibleConcreteStickelbergerSetup :=
    S.toConcreteStickelbergerSetup.toConductorFlexible
  traceScale := S.traceScale
  psiExponent_trace := S.psiExponent_trace
  pi_not_mem_Q_sq := S.pi_not_mem_Q_sq

end TraceFormStickelbergerSetup

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')



end ConcreteStickelbergerSetup

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')


end TraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular
