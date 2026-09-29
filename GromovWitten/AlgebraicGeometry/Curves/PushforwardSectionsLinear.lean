/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSectionsLinear

/-!
# Linear pushforward sections

The canonical base-ring action on sections is compatible with pushforward along a scheme morphism.
Consequently, sections over an open of the target and sections over its inverse image are
canonically equivalent as base-linear modules.
-/

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- The base-ring map on sections commutes with pushforward along a scheme morphism. -/
lemma baseToSections_pushforward (s : Y ⟶ Spec R) (f : X ⟶ Y) (U : Y.Opens) :
    baseToSections s U ≫ f.app U = baseToSections (f ≫ s) (f ⁻¹ᵁ U) := by
  simp only [baseToSections, Scheme.Hom.comp_appTop, Category.assoc]
  congr 1
  congr 1
  exact f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op

/-- Sections of a pushforward over an open are base-linearly equivalent to sections over its
inverse image. -/
def pushforwardOpenSectionsBaseLinearEquiv (s : Y ⟶ Spec R) (f : X ⟶ Y)
    (M : X.Modules) (U : Y.Opens) :
    baseSectionModule s U ((Scheme.Modules.pushforward f).obj M) ≃ₗ[R]
      baseSectionModule (f ≫ s) (f ⁻¹ᵁ U) M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change (f.app U ((baseToSections s U).hom r)) •
      (show Γ(M, f ⁻¹ᵁ U) from m) =
        (baseToSections (f ≫ s) (f ⁻¹ᵁ U)).hom r • (show Γ(M, f ⁻¹ᵁ U) from m)
    have hr : f.app U ((baseToSections s U).hom r) =
        (baseToSections (f ≫ s) (f ⁻¹ᵁ U)).hom r :=
      congrArg (fun k => k r) (baseToSections_pushforward s f U)
    rw [hr]

end GromovWitten.AlgebraicGeometry.Curves
