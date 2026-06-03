module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import BernoulliRegular.GaussSum.SignInvariant.Operator

/-!
# Determinant-ready block decomposition for quadratic Gauss sums

This file packages the ambient `δ₀ +` character basis used to reorganize the
normalized finite Fourier transform into the trivial block, non-self-dual
character-pair blocks, and the surviving quadratic line.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

/-- The delta function supported at `0`. -/
def deltaZeroFunction : ZMod p → ℂ :=
  Pi.basisFun ℂ (ZMod p) (0 : ZMod p)

/-- Restrict a function on `ZMod p` to the unit group. -/
def restrictUnitsLinear : (ZMod p → ℂ) →ₗ[ℂ] ((ZMod p)ˣ → ℂ) where
  toFun Φ u := Φ u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- View a Dirichlet character as a monoid homomorphism on the unit group with
values in `ℂ`. -/
def dirichletCharacterUnitMonoidHom (χ : DirichletCharacter ℂ p) : (ZMod p)ˣ →* ℂ :=
  (Units.coeHom ℂ).comp χ.toUnitHom

theorem dirichletCharacterUnitMonoidHom_injective :
    Function.Injective (dirichletCharacterUnitMonoidHom (p := p)) := by
  intro χ ψ hχψ
  apply (DirichletCharacter.toUnitHom_inj (χ := χ) (ψ := ψ)).mp
  ext u
  have hcoe : ((χ.toUnitHom u : ℂˣ) : ℂ) = ((ψ.toUnitHom u : ℂˣ) : ℂ) :=
    DFunLike.congr_fun hχψ u
  exact hcoe

/-- Dirichlet characters are linearly independent on the unit group. -/
theorem linearIndependent_dirichletCharactersOnUnits :
    LinearIndependent ℂ (fun χ : DirichletCharacter ℂ p =>
      (dirichletCharacterUnitMonoidHom (p := p) χ : (ZMod p)ˣ → ℂ)) :=
  (linearIndependent_monoidHom ((ZMod p)ˣ) ℂ).comp
      (dirichletCharacterUnitMonoidHom (p := p))
      (dirichletCharacterUnitMonoidHom_injective (p := p))

/-- Evaluation at `0`. -/
def evalAtZeroLinear : (ZMod p → ℂ) →ₗ[ℂ] ℂ where
  toFun Φ := Φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem dirichletCharacter_apply_zero (χ : DirichletCharacter ℂ p) :
    χ (0 : ZMod p) = 0 := by
  simpa using MulChar.map_nonunit χ (a := (0 : ZMod p)) (by simp)

theorem normalizedDft_deltaZero :
    normalizedDft p (deltaZeroFunction (p := p)) =
      (Real.sqrt p : ℂ)⁻¹ • (fun _ : ZMod p => (1 : ℂ)) := by
  ext x
  rw [normalizedDft_apply, deltaZeroFunction, dft_deltaZero_eq_constOne]
  simp [smul_eq_mul]

theorem normalizedDft_constOne :
    normalizedDft p (fun _ : ZMod p => (1 : ℂ)) =
      (((Real.sqrt p : ℂ)⁻¹) * p) • deltaZeroFunction (p := p) := by
  ext x
  rw [normalizedDft_apply, congrFun (dft_constOne_eq_prime_smul_deltaZero (p := p)) x]
  simp [deltaZeroFunction, smul_eq_mul, mul_assoc]

end SignInvariant

end BernoulliRegular
