/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.PushforwardSectionsLinear
import GromovWitten.AlgebraicGeometry.Curves.AffineBaseChangeIsomorphism
import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairBaseModule
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineCoverVanishing
import GromovWitten.AlgebraicGeometry.SheafCohomology.SheafHComparison

/-!
# Čech cohomology of an affine pushforward

For a pushforward along an affine morphism, the base-linear two-open Čech
complex on the target identifies with the corresponding complex on the
inverse-image opens. The resulting degree-zero and degree-one comparisons
are stated for an explicitly chosen affine cover of the target.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- The pair of pushforward section modules is base-linearly identified with the pair on
the inverse-image opens. -/
def pushforwardCechPairIso (s : Y ⟶ Spec R) (f : X ⟶ Y) (M : X.Modules)
    (U V : Y.Opens) :
    (ModuleCat.restrictScalars (baseRingHom R s)).obj
      (sectionsPairModule ((Scheme.Modules.pushforward f).obj M) U V) ≅
    (ModuleCat.restrictScalars (baseRingHom R (f ≫ s))).obj
      (sectionsPairModule M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)) :=
  ((pushforwardOpenSectionsBaseLinearEquiv s f M U).prodCongr
    (pushforwardOpenSectionsBaseLinearEquiv s f M V)).toModuleIso

/-- The pushforward overlap section module is base-linearly identified with the section module
on the inverse-image overlap. -/
def pushforwardCechOverlapIso (s : Y ⟶ Spec R) (f : X ⟶ Y) (M : X.Modules)
    (U V : Y.Opens) :
    (ModuleCat.restrictScalars (baseRingHom R s)).obj
      (sectionModuleCat ((Scheme.Modules.pushforward f).obj M) (U ⊓ V)) ≅
    (ModuleCat.restrictScalars (baseRingHom R (f ≫ s))).obj
      (sectionModuleCat M ((f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V))) :=
  (pushforwardOpenSectionsBaseLinearEquiv s f M (U ⊓ V)).toModuleIso

/-- The pushforward section identifications commute with the Čech differential. -/
lemma pushforwardCech_square (s : Y ⟶ Spec R) (f : X ⟶ Y) (M : X.Modules)
    (U V : Y.Opens) :
    baseCechPairMap s ((Scheme.Modules.pushforward f).obj M) U V ≫
      (pushforwardCechOverlapIso s f M U V).hom =
    (pushforwardCechPairIso s f M U V).hom ≫
      baseCechPairMap (f ≫ s) M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rfl

/-- Degree-zero cohomology of a pushforward is identified with degree-zero cohomology on the
inverse-image cover. -/
def pushforwardCohomologyZeroIso (s : Y ⟶ Spec R) (f : X ⟶ Y) (M : X.Modules)
    (U V : Y.Opens) (hcover : U ⊔ V = ⊤) :
    cohomologyModuleCat R s ((Scheme.Modules.pushforward f).obj M) 0 ≅
      cohomologyModuleCat R (f ≫ s) M 0 := by
  have hc : f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V = ⊤ := by
    change f ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  exact cohomologyZeroIsoBaseCechKernel s ((Scheme.Modules.pushforward f).obj M) U V hcover ≪≫
    kernel.mapIso (baseCechPairMap s ((Scheme.Modules.pushforward f).obj M) U V)
      (baseCechPairMap (f ≫ s) M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V))
      (pushforwardCechPairIso s f M U V) (pushforwardCechOverlapIso s f M U V)
      (pushforwardCech_square s f M U V) ≪≫
    (cohomologyZeroIsoBaseCechKernel (f ≫ s) M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hc).symm

/-- Under affine hypotheses, degree-one cohomology of a pushforward is identified with degree-one
cohomology on the inverse-image cover. -/
def affinePushforwardCohomologyOneIso [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (s : Y ⟶ Spec R) (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) :
    cohomologyModuleCat R s ((Scheme.Modules.pushforward f).obj M) 1 ≅
      cohomologyModuleCat R (f ≫ s) M 1 := by
  have hc : f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V = ⊤ := by
    change f ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  exact (baseCechCokernelIsoCohomology s ((Scheme.Modules.pushforward f).obj M)
      U V hU hV hcover).symm ≪≫
    cokernel.mapIso (baseCechPairMap s ((Scheme.Modules.pushforward f).obj M) U V)
      (baseCechPairMap (f ≫ s) M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V))
      (pushforwardCechPairIso s f M U V) (pushforwardCechOverlapIso s f M U V)
      (pushforwardCech_square s f M U V) ≪≫
    baseCechCokernelIsoCohomology (f ≫ s) M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
      (IsAffineHom.isAffine_preimage (f := f) U hU)
      (IsAffineHom.isAffine_preimage (f := f) V hV) hc

/-- A quasi-coherent module on an affine morphism has no cohomology above degree one when
the target has a chosen two-affine-open cover whose inverse images and intersection are affine. -/
theorem isZero_cohomology_succ_succ_of_affine_twoAffine
    [IsLocallyNoetherian X] (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    IsZero (cohomology X M (n + 2)) := by
  have hc : f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V = ⊤ := by
    change f ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  have hI' : IsAffineOpen ((f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V)) :=
    IsAffineHom.isAffine_preimage (f := f) (U ⊓ V) hI
  have hz := isZero_rightDerived_sections_sup ((moduleToSheafAb X).obj M)
    (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (n + 1)
    (isZero_rightDerived_sections_affineOpen_succ _
      (IsAffineHom.isAffine_preimage (f := f) U hU) M (n + 1))
    (isZero_rightDerived_sections_affineOpen_succ _
      (IsAffineHom.isAffine_preimage (f := f) V hV) M (n + 1))
    (isZero_rightDerived_sections_affineOpen_succ _ hI' M n)
  rw [hc] at hz
  exact isZero_sheafH_of_isZero_rightDerivedSections
    (F := (moduleToSheafAb X).obj M) (n + 1) hz

end GromovWitten.AlgebraicGeometry.Curves
