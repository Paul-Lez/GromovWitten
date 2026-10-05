/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.BaseSectionsPresheaf
import GromovWitten.CategoryTheory.MapComplexExtension
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Section-presheaf augmentations of resolutions

Extending a resolution by zero gives a canonical augmentation of integer-indexed
section complexes. A quasi-isomorphism on sections remains one under this extension.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

universe u v

noncomputable section

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The section-presheaf augmentation obtained by extending a natural-number resolution
to an integer-indexed complex. -/
noncomputable def resolutionSectionsAugmentation (s : X ⟶ Spec R)
    {M : X.Modules} {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) :
    (HomologicalComplex.single (X.Opensᵒᵖ ⥤ ModuleCat R) (.up ℤ) 0).obj
        (baseSectionsPresheaf s M) ⟶
      ((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat) := by
  let F := baseSectionsPresheafFunctor s
  let e := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl
  exact (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M ≫
    (F.mapHomologicalComplex (.up ℤ)).map (e.inv ≫
      HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)

set_option backward.isDefEq.respectTransparency false in
lemma resolutionSectionsAugmentation_quasiIso_at (s : X ⟶ Spec R)
    {M : X.Modules} {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) (W : X.Opens)
    [QuasiIso (((baseSectionsFunctor s W).mapHomologicalComplex (.up ℕ)).map a)] :
    QuasiIso
      ((((evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op W)).mapHomologicalComplex (.up ℤ)).map
        (resolutionSectionsAugmentation s a)) := by
  let F := baseSectionsPresheafFunctor s
  let H := (evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op W)
  let E := H.mapHomologicalComplex (.up ℤ)
  let B := F.mapHomologicalComplex (.up ℤ)
  let e := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl
  have hq : QuasiIso (E.map (B.map (HomologicalComplex.extendMap a
      ComplexShape.embeddingUpNat))) := by
    change QuasiIso (((baseSectionsFunctor s W).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat))
    exact CategoryTheory.Functor.quasiIso_map_extendMap (baseSectionsFunctor s W)
      ComplexShape.embeddingUpNat _ a
  change QuasiIso (E.map
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M ≫
      B.map (e.inv ≫ HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)))
  rw [E.map_comp, B.map_comp, E.map_comp]
  infer_instance

end GromovWitten.AlgebraicGeometry.Curves
