/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CechSectionsBaseChangeNaturality
import GromovWitten.AlgebraicGeometry.Curves.OpenSectionsBaseChangeNaturality
import GromovWitten.CategoryTheory.ScalarHomologyBaseChange
import GromovWitten.AlgebraicGeometry.Curves.OpenAffineSectionsFlat

/-!
# Base change for a two-affine cover

For a two-affine cover with affine overlap, this file compares the actual Ext cohomology
modules in degrees zero and one after a Cartesian base change.  The degree-one comparison
uses local Noetherianity on both schemes and quasicoherence.  The degree-zero comparison
uses relative stalk flatness and flatness of the actual degree-one cohomology module.

These are comparisons for the constructed two-affine Cech computation.  The degree-zero
comparison is identified with the canonical scalar-extension map on global sections by
`TwoAffineCohomologyZeroBaseChangeCanonical`; sheaf-level proper-family base change remains outside
this file's scope.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The Cech pair map commutes with the base-change maps on the pair and overlap sections. -/
lemma cechBaseChange_square (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) (U V : X.Opens) :
    (ModuleCat.extendScalars φ.hom).map (baseCechPairMap s M U V) ≫
      cechOverlapBaseChangeMap s φ p g h M U V =
    cechPairBaseChangeMap s φ p g h M U V ≫
      baseCechPairMap g ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  simp only [ConcreteCategory.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  rw [cechPairBaseChangeMap_one_tmul, cechOverlapBaseChangeMap_one_tmul]
  rcases z with ⟨x, y⟩
  let η := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  change η.app (U ⊓ V) (M.presheaf.map (homOfLE inf_le_left).op x -
    M.presheaf.map (homOfLE inf_le_right).op y) =
    ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE inf_le_left).op (η.app U x) -
    ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE inf_le_right).op (η.app V y)
  rw [map_sub]
  congr 1
  · exact ConcreteCategory.congr_hom (η.mapPresheaf.naturality (homOfLE inf_le_left).op) x
  · exact ConcreteCategory.congr_hom (η.mapPresheaf.naturality (homOfLE inf_le_right).op) y

set_option backward.isDefEq.respectTransparency false in
/-- Degree-one actual Ext cohomology commutes with a Cartesian base change of a two-affine cover.

The hypotheses require local Noetherianity on both schemes, a quasicoherent module, affine
cover pieces and overlap, and a cover by the two pieces. -/
def twoAffineCohomologyOneBaseChangeIso [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) :
    (ModuleCat.extendScalars φ.hom).obj (cohomologyModuleCat R s M 1) ≅
      cohomologyModuleCat T g ((Scheme.Modules.pullback p).obj M) 1 := by
  have : IsAffineHom p :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  have hUp : IsAffineOpen (p ⁻¹ᵁ U) := IsAffineHom.isAffine_preimage _ hU
  have hVp : IsAffineOpen (p ⁻¹ᵁ V) := IsAffineHom.isAffine_preimage _ hV
  have hc : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  have := cechPairBaseChangeMap_isIso s φ p g h M U V hU hV
  have := cechOverlapBaseChangeMap_isIso s φ p g h M U V hI
  exact (ModuleCat.extendScalars φ.hom).mapIso
      (baseCechCokernelIsoCohomology s M U V hU hV hcover).symm ≪≫
    PreservesCokernel.iso (ModuleCat.extendScalars φ.hom) (baseCechPairMap s M U V) ≪≫
    cokernel.mapIso ((ModuleCat.extendScalars φ.hom).map (baseCechPairMap s M U V))
      (baseCechPairMap g ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V))
      (asIso (cechPairBaseChangeMap s φ p g h M U V))
      (asIso (cechOverlapBaseChangeMap s φ p g h M U V))
      (cechBaseChange_square s φ p g h M U V) ≪≫
    baseCechCokernelIsoCohomology g ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hUp hVp hc

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero actual Ext cohomology commutes with base change under relative flatness.

The source is locally Noetherian, the module is quasicoherent, the two pieces and their
overlap are affine and cover the source, every relative stalk is flat over the base, and
the actual degree-one cohomology module is flat.  No Noetherianity hypothesis is imposed on
the target of the base change. -/
def twoAffineCohomologyZeroBaseChangeIso_of_flat [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Flat R (cohomologyModuleCat R s M 1)] :
    (ModuleCat.extendScalars φ.hom).obj (cohomologyModuleCat R s M 0) ≅
      cohomologyModuleCat T g ((Scheme.Modules.pullback p).obj M) 0 := by
  have hc : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  have : Module.Flat R (baseSectionModule s (U ⊓ V) M) :=
    baseSections_flat_of_relative_stalks s M (U ⊓ V) hI hflat
  have : Module.Flat R
      ((ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
        (sectionModuleCat M (U ⊓ V))) :=
    Module.Flat.of_linearEquiv (baseCechOverlapSectionsIso s M U V).toLinearEquiv.symm
  have : Module.Flat R ((cokernel (baseCechPairMap s M U V) : ModuleCat R) : Type u) :=
    Module.Flat.of_linearEquiv (baseCechCokernelIsoCohomology s M U V hU hV hcover).toLinearEquiv
  have := ModuleCat.preservesKernel_extendScalars_of_flat_cokernel φ.hom
    (baseCechPairMap s M U V)
  have := cechPairBaseChangeMap_isIso s φ p g h M U V hU hV
  have := cechOverlapBaseChangeMap_isIso s φ p g h M U V hI
  exact (ModuleCat.extendScalars φ.hom).mapIso
      (cohomologyZeroIsoBaseCechKernel s M U V hcover) ≪≫
    PreservesKernel.iso (ModuleCat.extendScalars φ.hom) (baseCechPairMap s M U V) ≪≫
    kernel.mapIso ((ModuleCat.extendScalars φ.hom).map (baseCechPairMap s M U V))
      (baseCechPairMap g ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V))
      (asIso (cechPairBaseChangeMap s φ p g h M U V))
      (asIso (cechOverlapBaseChangeMap s φ p g h M U V))
      (cechBaseChange_square s φ p g h M U V) ≪≫
    (cohomologyZeroIsoBaseCechKernel g ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hc).symm
end GromovWitten.AlgebraicGeometry.Curves
