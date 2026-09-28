/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeStalkFlat
import GromovWitten.AlgebraicGeometry.Curves.AffineSectionsFlat

/-!
# Affine relative stalk comparison

The relative base-ring action on a stalk of a module over an affine scheme agrees with the
usual restricted-scalar affine stalk action induced by the corresponding algebra map.
-/

open CategoryTheory TopCat AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R S : CommRingCat.{u}} [Algebra R S]

local instance genericNativeStalkModule (X : Scheme.{u}) (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  let P := (Scheme.Modules.toPresheafOfModules X).obj M
  exact @PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    _ _ P x

local instance affineNativeStalkModule (M : (Spec S).Modules) (x : PrimeSpectrum.Top S) :
    Module ((structurePresheafInCommRingCat S).stalk x) (M.presheaf.stalk x) := by
  let P := (Scheme.Modules.toPresheafOfModules (Spec S)).obj M
  exact @PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    _ _ P x

local instance affineNativeStalkModule' (M : (Spec S).Modules) (x : PrimeSpectrum.Top S) :
    Module ((Spec S).presheaf.stalk x) (M.presheaf.stalk x) := by
  let P := (Scheme.Modules.toPresheafOfModules (Spec S)).obj M
  exact @PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    _ _ P x

local instance affineBaseStalkModule (M : (Spec S).Modules) (x : PrimeSpectrum.Top S) :
    Module S (M.presheaf.stalk x) :=
  Module.compHom (M.presheaf.stalk x) (StructureSheaf.toStalk (S : Type u) x).hom

/-- The relative scalar map on an affine scheme induced by `Spec.map (algebraMap R S)` is the
usual composite `R ⟶ S ⟶ 𝒪ₓ`. -/
lemma affineRelativeStalk_scalar (x : PrimeSpectrum.Top S) :
    ((Spec S).presheaf.Γgerm x).hom.comp
        (baseRingHom (R : Type u)
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))) =
      (StructureSheaf.toStalk (S : Type u) x).hom.comp (algebraMap R S) := by
  unfold baseRingHom
  rw [← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R S))]
  rfl

/-- The relative stalk module for `Spec.map (algebraMap R S)` is canonically the affine stalk
module obtained by restricting scalars from `S` to `R`. -/
def affineRelativeStalkLinearEquiv (M : (Spec S).Modules) (x : PrimeSpectrum.Top S) :
    (relativeStalkBase
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) M x : Type u) ≃ₗ[(R : Type u)]
      (affineStalkBase R M x : Type u) := by
  let e :
      (relativeStalkBase
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) M x : Type u) ≃ₗ[(R : Type u)]
        (affineStalkBase R M x : Type u) :=
    { toFun := id
      invFun := id
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl
      map_add' := by intro a b; rfl
      map_smul' := by
        intro r z
        change
          (((((Spec S).presheaf.Γgerm x).hom.comp
            (baseRingHom (R : Type u)
              (Spec.map (CommRingCat.ofHom (algebraMap R S))))) r) •
              (show M.presheaf.stalk x from z)) =
            (algebraMap R S r) • (show M.presheaf.stalk x from z)
        rw [affineRelativeStalk_scalar]
        rfl }
  exact e

end GromovWitten.AlgebraicGeometry.Curves
