/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.BaseSectionsPresheaf
import GromovWitten.AlgebraicGeometry.Curves.OpenSectionsBaseChangeNaturality
import Mathlib.Algebra.Homology.Single

/-!
# Base change for section presheaves

Canonical affine-open base change is natural under restriction. Its degree-zero
complex map is a quasi-isomorphism on each affine open for quasi-coherent modules.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical base-change maps on open sections form a morphism of presheaves. -/
def baseSectionsPresheafBaseChange (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) :
    baseSectionsPresheaf s M ⋙ ModuleCat.extendScalars φ.hom ⟶
      (TopologicalSpace.Opens.map p.base).op ⋙
        baseSectionsPresheaf g ((Scheme.Modules.pullback p).obj M) where
  app U := openSectionsBaseChangeMap s φ p g h M U.unop
  naturality _ _ i := openSectionsBaseChangeMap_restriction s φ p g h M i.unop

lemma baseSectionsPresheafBaseChange_app_isIso (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (W : X.Opens) (hW : IsAffineOpen W) :
    IsIso ((baseSectionsPresheafBaseChange s φ p g h M).app (op W)) :=
  openSectionsBaseChangeMap_isIso s φ p g h M W hW

set_option backward.isDefEq.respectTransparency false in
private lemma evaluated_single_map_isIso
    {A B : X.Opensᵒᵖ ⥤ ModuleCat.{u} T} (f : A ⟶ B) (W : X.Opens)
    [IsIso (f.app (op W))] :
    IsIso ((((evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op W)).mapHomologicalComplex
      (.up ℤ)).map ((single (X.Opensᵒᵖ ⥤ ModuleCat T) (.up ℤ) 0).map f)) := by
  let H := (evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op W)
  let E := H.mapHomologicalComplex (.up ℤ)
  let S := single (X.Opensᵒᵖ ⥤ ModuleCat T) (.up ℤ) 0
  let e := singleMapHomologicalComplex H (.up ℤ) 0
  have hn := e.hom.naturality f
  have hq : IsIso ((single (ModuleCat T) (.up ℤ) 0).map (H.map f)) := by
    have : IsIso (H.map f) := inferInstanceAs (IsIso (f.app (op W)))
    infer_instance
  have heq : E.map (S.map f) ≫ e.hom.app B =
      e.hom.app A ≫ (single (ModuleCat T) (.up ℤ) 0).map (H.map f) := hn
  have : IsIso (E.map (S.map f) ≫ e.hom.app B) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app B)

lemma single_baseSectionsPresheafBaseChange_quasiIso_at
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (hW : IsAffineOpen W) :
    QuasiIso ((((evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op W)).mapHomologicalComplex
      (.up ℤ)).map ((single (X.Opensᵒᵖ ⥤ ModuleCat T) (.up ℤ) 0).map
        (baseSectionsPresheafBaseChange s φ p g h M))) := by
  have := baseSectionsPresheafBaseChange_app_isIso s φ p g h M W hW
  have := evaluated_single_map_isIso (baseSectionsPresheafBaseChange s φ p g h M) W
  infer_instance

end GromovWitten.AlgebraicGeometry.Curves
