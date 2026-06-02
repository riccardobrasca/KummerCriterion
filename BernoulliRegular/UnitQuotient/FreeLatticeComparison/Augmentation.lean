module

public import BernoulliRegular.UnitQuotient.FreeCharacterProfile

/-!
# Unit quotients: augmentation comparison

This file defines the full logarithmic augmentation hyperplane, identifies it
with the deleted-coordinate logarithmic space, and records the equivariant
restricted embedding of the torsion-free unit quotient.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

open Finset

set_option linter.unusedSectionVars false

attribute [local instance] Fintype.ofFinite
attribute [local instance] NumberField.Units.instZLattice_unitLattice

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The summation map on the full logarithmic space.  The logarithmic image of
global units lies in its kernel by the product formula. -/
def cyclotomicFullLogAugmentationMap :
    CyclotomicFullLogSpace K →ₗ[ℝ] ℝ where
  toFun f := ∑ w : InfinitePlace K, f w
  map_add' f g := by
    simp [sum_add_distrib]
  map_smul' c f := by
    change ∑ w : InfinitePlace K, c * f w =
      c * ∑ w : InfinitePlace K, f w
    rw [Finset.mul_sum]

/-- The full logarithmic augmentation hyperplane. -/
def cyclotomicFullLogAugmentationSubmodule :
    Submodule ℝ (CyclotomicFullLogSpace K) :=
  LinearMap.ker (cyclotomicFullLogAugmentationMap K)

theorem cyclotomicFullLogEmbedding_mem_augmentation
    (u : CyclotomicUnitGroup K) :
    cyclotomicFullLogEmbedding K (Additive.ofMul u) ∈
      cyclotomicFullLogAugmentationSubmodule K := by
  rw [cyclotomicFullLogAugmentationSubmodule, LinearMap.mem_ker]
  exact NumberField.Units.sum_mult_mul_log u

theorem cyclotomicFullLogEmbeddingFreePart_mem_augmentation
    (x : CyclotomicUnitFreePart K) :
    cyclotomicFullLogEmbeddingFreePart K x ∈
      cyclotomicFullLogAugmentationSubmodule K := by
  induction x using Additive.rec with
  | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro u
      change cyclotomicFullLogEmbeddingFreePart K
          (Additive.ofMul (cyclotomicUnitFreeClass K u)) ∈
        cyclotomicFullLogAugmentationSubmodule K
      rw [cyclotomicFullLogEmbeddingFreePart_apply]
      exact cyclotomicFullLogEmbedding_mem_augmentation (K := K) u

/-- The full logarithmic embedding, with codomain restricted to the
augmentation hyperplane. -/
def cyclotomicFullLogEmbeddingFreePartAugmentation :
    CyclotomicUnitFreePart K →+
      cyclotomicFullLogAugmentationSubmodule K :=
  (cyclotomicFullLogEmbeddingFreePart K).codRestrict
    (cyclotomicFullLogAugmentationSubmodule K)
    (cyclotomicFullLogEmbeddingFreePart_mem_augmentation (K := K))


/-- Delete the distinguished coordinate from the full augmentation hyperplane.
The missing coordinate is recovered from the relation that the sum is zero. -/
noncomputable def cyclotomicFullLogAugmentationEquivDeleted :
    cyclotomicFullLogAugmentationSubmodule K ≃ₗ[ℝ]
      NumberField.Units.dirichletUnitTheorem.logSpace K := by
  classical
  refine
    { toFun := fun f w => f.1 w.1
      map_add' := by
        intro f g
        ext w
        rfl
      map_smul' := by
        intro c f
        ext w
        rfl
      invFun := fun g =>
        ⟨fun w =>
          if h : w = NumberField.Units.dirichletUnitTheorem.w₀ then
            -∑ v : {v : InfinitePlace K //
                v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, g v
          else
            g ⟨w, h⟩,
          by
            rw [cyclotomicFullLogAugmentationSubmodule, LinearMap.mem_ker]
            change ∑ w : InfinitePlace K,
                (if h : w = NumberField.Units.dirichletUnitTheorem.w₀ then
                  -∑ v : {v : InfinitePlace K //
                      v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, g v
                else
                  g ⟨w, h⟩) = 0
            rw [Fintype.sum_eq_add_sum_subtype_ne _
              NumberField.Units.dirichletUnitTheorem.w₀]
            rw [show
                (∑ x : {v : InfinitePlace K //
                    v ≠ NumberField.Units.dirichletUnitTheorem.w₀},
                  (if h : (x : InfinitePlace K) =
                      NumberField.Units.dirichletUnitTheorem.w₀ then
                    -∑ v : {v : InfinitePlace K //
                        v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, g v
                  else
                    g ⟨x, h⟩)) = ∑ x, g x by
              apply Finset.sum_congr rfl
              intro x _hx
              rw [dif_neg x.2]]
            simp
        ⟩
      left_inv := by
        intro f
        ext w
        by_cases hw : w = NumberField.Units.dirichletUnitTheorem.w₀
        · subst hw
          have hsum : ∑ v : InfinitePlace K, f.1 v = 0 := by
            have hf : f.1 ∈ LinearMap.ker (cyclotomicFullLogAugmentationMap K) := f.2
            rw [LinearMap.mem_ker] at hf
            exact hf
          rw [Fintype.sum_eq_add_sum_subtype_ne _
            NumberField.Units.dirichletUnitTheorem.w₀] at hsum
          change (if h : NumberField.Units.dirichletUnitTheorem.w₀ =
              NumberField.Units.dirichletUnitTheorem.w₀ then
            -∑ v : {v : InfinitePlace K //
                v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, f.1 v
          else
            f.1 NumberField.Units.dirichletUnitTheorem.w₀) =
            f.1 NumberField.Units.dirichletUnitTheorem.w₀
          rw [dif_pos rfl]
          linarith
        · change (if h : w = NumberField.Units.dirichletUnitTheorem.w₀ then
            -∑ v : {v : InfinitePlace K //
                v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, f.1 v
          else
            f.1 w) = f.1 w
          rw [dif_neg hw]
      right_inv := by
        intro g
        ext w
        change (if h : (w : InfinitePlace K) =
            NumberField.Units.dirichletUnitTheorem.w₀ then
          -∑ v : {v : InfinitePlace K //
              v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, g v
        else
          g ⟨w, h⟩) = g w
        rw [dif_neg w.2] }

@[simp]
theorem cyclotomicFullLogAugmentationEquivDeleted_apply
    (f : cyclotomicFullLogAugmentationSubmodule K)
    (w : {w : InfinitePlace K //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    cyclotomicFullLogAugmentationEquivDeleted K f w = f.1 w.1 :=
  rfl

theorem cyclotomicFullLogAugmentationEquivDeleted_apply_embedding
    (x : CyclotomicUnitFreePart K) :
    cyclotomicFullLogAugmentationEquivDeleted K
        (cyclotomicFullLogEmbeddingFreePartAugmentation K x) =
      NumberField.Units.logEmbeddingQuot K x := by
  induction x using Additive.rec with
  | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro u
      ext w
      rw [cyclotomicFullLogAugmentationEquivDeleted_apply]
      rw [NumberField.Units.logEmbeddingQuot_apply]
      rfl




/-- Equivariance of the logarithmic embedding after restricting its codomain
to the augmentation hyperplane. -/
theorem cyclotomicFullLogEmbeddingFreePartAugmentation_equivariant
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePart K) :
    cyclotomicFullLogEmbeddingFreePartAugmentation K
        (cyclotomicUnitFreePartDeltaAction (p := p) K a x) =
      ⟨cyclotomicFullLogSpaceDeltaAction (p := p) K a
          (cyclotomicFullLogEmbeddingFreePart K x),
        by
          rw [← cyclotomicFullLogEmbeddingFreePart_equivariant
            (p := p) (K := K) a x]
          exact cyclotomicFullLogEmbeddingFreePart_mem_augmentation (K := K)
            (cyclotomicUnitFreePartDeltaAction (p := p) K a x)⟩ := by
  ext w
  exact congrFun
    (cyclotomicFullLogEmbeddingFreePart_equivariant (p := p) (K := K) a x) w

end BernoulliRegular

end
