/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Restriction between open pushforwards

For nested opens, this file packages restriction of a sheaf of modules as a morphism
between its two open pushforwards.  The component formula is stated using the image of
the inverse-image open; this keeps the canonical equality transports explicit.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.SheafCohomology
open Scheme.Modules
universe u
noncomputable section

variable {X : Scheme.{u}}

instance moduleRestrictFunctor_additive {Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (restrictFunctor j).Additive :=
  Functor.additive_of_iso (restrictFunctorIsoPullback j).symm

/- The image of the smaller open after intersecting with W lies in the corresponding
   image for the larger open. -/
lemma openRestrictionMap_image_le {U V : X.Opens} (h : V ≤ U) (W : X.Opens) :
    (Scheme.Hom.opensFunctor V.ι).obj (V.ι ⁻¹ᵁ W) ≤
      (Scheme.Hom.opensFunctor U.ι).obj (U.ι ⁻¹ᵁ W) := by
  let i : (V.toScheme) ⟶ (U.toScheme) := X.homOfLE h
  have hi : i ≫ U.ι = V.ι := X.homOfLE_ι h
  calc
    (Scheme.Hom.opensFunctor V.ι).obj (V.ι ⁻¹ᵁ W) =
        (Scheme.Hom.opensFunctor (i ≫ U.ι)).obj
          ((i ≫ U.ι) ⁻¹ᵁ W) := by simp only [hi]
    _ = (Scheme.Hom.opensFunctor U.ι).obj
          ((Scheme.Hom.opensFunctor i).obj (i ⁻¹ᵁ (U.ι ⁻¹ᵁ W))) := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_image]
    _ ≤ (Scheme.Hom.opensFunctor U.ι).obj (U.ι ⁻¹ᵁ W) := by
      apply Scheme.Hom.image_mono
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.opensRange_homOfLE]
      exact inf_le_right

set_option backward.isDefEq.respectTransparency false in
/-- The canonical restriction map between pushforwards from nested open subschemes. -/
def openRestrictionMap (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    (pushforward U.ι).obj ((restrictFunctor U.ι).obj M) ⟶
      (pushforward V.ι).obj ((restrictFunctor V.ι).obj M) := by
  let i : (V.toScheme) ⟶ (U.toScheme) := X.homOfLE h
  let hi : i ≫ U.ι = V.ι := X.homOfLE_ι h
  exact
    (pushforward U.ι).map ((restrictAdjunction i).unit.app ((restrictFunctor U.ι).obj M)) ≫
      (pushforwardComp i U.ι).hom.app ((restrictFunctor i).obj
        ((restrictFunctor U.ι).obj M)) ≫
      (pushforward (i ≫ U.ι)).map ((restrictFunctorComp i U.ι).inv.app M) ≫
      (pushforward (i ≫ U.ι)).map ((restrictFunctorCongr hi).hom.app M) ≫
      (pushforwardCongr hi).hom.app ((restrictFunctor V.ι).obj M)

set_option backward.isDefEq.respectTransparency false in
/-- After identifying restricted sections with sections on their images, restriction is the
presheaf map induced by the inclusion of the two image opens. -/
lemma openRestrictionMap_app (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (W : X.Opens) :
    (M.restrictAppIso U.ι (U.ι ⁻¹ᵁ W)).inv ≫
        (openRestrictionMap M h).app W ≫
      (M.restrictAppIso V.ι (V.ι ⁻¹ᵁ W)).hom =
      M.presheaf.map (homOfLE (openRestrictionMap_image_le h W)).op := by
  simp only [openRestrictionMap, Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, pushforwardComp_hom_app_app,
    restrictFunctorComp_inv_app_app]
  simp only [pushforward_obj_obj, Functor.comp_obj, homOfLE_leOfHom, Scheme.Hom.comp_base,
    Opens.map_comp_obj, Functor.op_obj, eqToHom_op, restrictFunctorCongr_hom_app_app,
    pushforwardCongr_hom_app_app, eqToHom_map_comp_assoc, Category.id_comp, Category.assoc,
    map_restrictAppIso_hom, restrictAppIso_inv_map_assoc]
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp]
  erw [Category.id_comp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The raw component of open restriction is the presheaf map on the image opens. -/
lemma openRestrictionMap_app_eq (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (W : X.Opens) :
    (openRestrictionMap M h).app W =
      M.presheaf.map (homOfLE (openRestrictionMap_image_le h W)).op := by
  have he := openRestrictionMap_app M h W
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_hom, Iso.refl_inv] at he
  erw [Category.id_comp, Category.comp_id] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
/-- The open restriction map is natural in the module. -/
lemma openRestrictionMap_naturality (M N : X.Modules) (f : M ⟶ N) {U V : X.Opens} (h : V ≤ U) :
    (pushforward U.ι).map ((restrictFunctor U.ι).map f) ≫ openRestrictionMap N h =
      openRestrictionMap M h ≫ (pushforward V.ι).map ((restrictFunctor V.ι).map f) := by
  apply Scheme.Modules.hom_ext
  intro W
  simp only [Hom.comp_app, pushforward_map_app, openRestrictionMap_app_eq]
  exact (f.mapPresheaf.naturality (homOfLE (openRestrictionMap_image_le h W)).op).symm

set_option backward.isDefEq.respectTransparency false in
/-- The open restriction map carries the larger-open adjunction unit to the smaller one. -/
lemma openRestrictionMap_unit (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    (restrictAdjunction U.ι).unit.app M ≫ openRestrictionMap M h =
      (restrictAdjunction V.ι).unit.app M := by
  apply Scheme.Modules.hom_ext
  intro W
  simp only [Hom.comp_app, openRestrictionMap_app_eq, restrictAdjunction_unit_app_app]
  rw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Restriction maps between three nested opens compose canonically. -/
lemma openRestrictionMap_trans (M : X.Modules)
    {U V W : X.Opens} (hUV : V ≤ U) (hVW : W ≤ V) :
    openRestrictionMap M hUV ≫ openRestrictionMap M hVW =
      openRestrictionMap M (hVW.trans hUV) := by
  apply Scheme.Modules.hom_ext
  intro Z
  simp only [Hom.comp_app, openRestrictionMap_app_eq]
  rw [← Functor.map_comp]
  congr 1

end

end GromovWitten.AlgebraicGeometry.SheafCohomology
