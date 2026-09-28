/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeStalkFlat

/-!
# Relative linearity of sections on open subschemes

This file records the base-ring linear maps and equivalences on sections induced by module
morphisms, module isomorphisms, and open pullback.  The actions are those attached to the
structure morphism, so the open-pullback equivalence is compatible with scalar restriction.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- The section map of a module morphism is linear over the base ring. -/
def baseSectionMapLinear (s : X ⟶ Spec R) {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) : baseSectionModule s U M →ₗ[R] baseSectionModule s U N where
  toFun := fun x => f.app U x
  map_add' := map_add (f.app U).hom
  map_smul' r m := by
    change f.app U ((baseToSections s U).hom r • m) =
      (baseToSections s U).hom r • f.app U m
    exact Scheme.Modules.Hom.app_smul f _ m

/-- A module isomorphism induces a base-linear equivalence on sections. -/
def baseSectionLinearEquiv (s : X ⟶ Spec R) {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) : baseSectionModule s U M ≃ₗ[R] baseSectionModule s U N :=
  LinearEquiv.ofBijective (baseSectionMapLinear s e.hom U)
    (ConcreteCategory.bijective_of_isIso (e.hom.app U))

/-- Restriction along an open immersion identifies sections with the sections on its image. -/
def restrictBaseSectionsLinearEquiv (s : Y ⟶ Spec R) (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : X.Opens) :
    baseSectionModule (f ≫ s) U (M.restrict f) ≃ₗ[R]
      baseSectionModule s (f ''ᵁ U) M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change (f.appIso U).inv ((baseToSections (f ≫ s) U).hom r) •
        (show Γ(M, f ''ᵁ U) from m) =
      (baseToSections s (f ''ᵁ U)).hom r • (show Γ(M, f ''ᵁ U) from m)
    have hr : (f.appIso U).inv ((baseToSections (f ≫ s) U).hom r) =
        (baseToSections s (f ''ᵁ U)).hom r :=
      congrArg (fun k => k r) (baseToSections_open s f U)
    rw [hr]

/-- Pullback along an open immersion identifies base-linear sections with sections on the image. -/
def openPullbackBaseSectionsLinearEquiv (s : Y ⟶ Spec R) (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens) :
    baseSectionModule (f ≫ s) U ((Scheme.Modules.pullback f).obj M) ≃ₗ[R]
      baseSectionModule s (f ''ᵁ U) M :=
  (baseSectionLinearEquiv (f ≫ s)
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm U).trans
    (restrictBaseSectionsLinearEquiv s f M U)

end GromovWitten.AlgebraicGeometry.Curves
