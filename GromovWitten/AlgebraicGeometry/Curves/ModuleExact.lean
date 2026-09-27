/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyBaseChange
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Exactness of the scalar-forgetting functor

The underlying abelian sheaf functor from sheaves of modules preserves finite
limits by the standard sheaf-module API.  Its preservation of finite colimits
is proved here from the sheafification adjunction: sheafification is a left
adjoint, and forgetting a sheaf of modules is identified with sheafifying the
underlying abelian presheaf.  Thus the functor preserves homology as well.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open scoped AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X : Scheme.{u}}

abbrev moduleSheafify (X : Scheme.{u}) :
    X.PresheafOfModules ⥤ X.Modules :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

abbrev moduleForget (X : Scheme.{u}) : X.Modules ⥤ X.PresheafOfModules :=
  SheafOfModules.forget X.ringCatSheaf

noncomputable def moduleSheafificationAbIso :
    moduleSheafify X ⋙ moduleToSheafAb X ≅
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat := by
  exact PresheafOfModules.sheafificationCompToSheaf (𝟙 X.ringCatSheaf.obj)

noncomputable def moduleToSheafAbIso :
    moduleToSheafAb X ≅
      moduleForget X ⋙
        (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  exact
    (Functor.isoWhiskerRight (asIso adj.counit).symm (moduleToSheafAb X)) ≪≫
      Functor.isoWhiskerLeft (moduleForget X) (moduleSheafificationAbIso (X := X))

theorem moduleToSheafAb_preservesColimit (J : Type) [Category J]
    (D : J ⥤ X.Modules) : PreservesColimit D (moduleToSheafAb X) := by
  let G := moduleForget X
  let L := moduleSheafify X
  let U := moduleToSheafAb X
  let A := PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat
  let F := D ⋙ G
  let cF := colimit.cocone F
  let hF : IsColimit cF := colimit.isColimit F
  let cL := L.mapCocone cF
  let e : D ≅ F ⋙ L := by
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    exact Functor.isoWhiskerLeft D (asIso adj.counit).symm
  let cD := (Cocone.precompose e.hom).obj cL
  have hcL : IsColimit cL := by
    change IsColimit ((moduleSheafify X).mapCocone cF)
    let hpres : PreservesColimitsOfShape J (moduleSheafify X) := by
      change PreservesColimitsOfShape J
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      infer_instance
    let hp : PreservesColimit F (moduleSheafify X) := hpres.preservesColimit
    exact @isColimitOfPreserves
      X.PresheafOfModules inferInstance X.Modules inferInstance J inferInstance
      F L cF hF hp
  have hcD : IsColimit cD :=
    (IsColimit.precomposeHomEquiv e cL).symm hcL
  let hLU := moduleSheafificationAbIso (X := X)
  let η : D ⋙ U ≅ F ⋙ A := by
    exact Functor.isoWhiskerLeft D (moduleToSheafAbIso (X := X))
  have hcA : IsColimit (A.mapCocone cF) := by
    apply isColimitOfPreserves A hF
  let cAη := (Cocone.precompose η.hom).obj (A.mapCocone cF)
  have hcAη : IsColimit cAη :=
    (IsColimit.precomposeHomEquiv η (A.mapCocone cF)).symm hcA
  have hmap : IsColimit (U.mapCocone cD) := by
    let i : U.obj cD.pt ≅ cAη.pt := hLU.app cF.pt
    apply IsColimit.ofIsoColimit hcAη
    refine Cocone.ext i ?_
    intro j
    change U.map (cD.ι.app j) ≫ i.hom = cAη.ι.app j
    have hn := hLU.hom.naturality (cF.ι.app j)
    change U.map (e.hom.app j ≫ cL.ι.app j) ≫ hLU.hom.app cF.pt = _
    rw [Functor.map_comp, Category.assoc]
    change U.map (e.hom.app j) ≫
      U.map (L.map (cF.ι.app j)) ≫ hLU.hom.app cF.pt = _
    change U.map (e.hom.app j) ≫
      (L ⋙ U).map (cF.ι.app j) ≫ hLU.hom.app cF.pt = _
    change U.map (e.hom.app j) ≫
      (L ⋙ U).map (cF.ι.app j) ≫ hLU.hom.app cF.pt =
      U.map (e.hom.app j) ≫ hLU.hom.app (F.obj j) ≫ A.map (cF.ι.app j)
    have hn' : (L ⋙ U).map (cF.ι.app j) ≫ hLU.hom.app cF.pt =
        hLU.hom.app (F.obj j) ≫ A.map (cF.ι.app j) := by
      convert hn using 1
      · rfl
      · rfl
    rw [hn']
  exact preservesColimit_of_preserves_colimit_cocone hcD hmap

noncomputable instance moduleToSheafAb_preservesFiniteLimits :
    PreservesFiniteLimits (moduleToSheafAb X) := by
  change PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf)
  infer_instance

noncomputable instance moduleToSheafAb_preservesFiniteColimits :
    PreservesFiniteColimits (moduleToSheafAb X) where
  preservesFiniteColimits J _ _ := by
    exact ⟨fun {D} => moduleToSheafAb_preservesColimit J D⟩

noncomputable instance moduleToSheafAb_preservesHomology :
    (moduleToSheafAb X).PreservesHomology := by infer_instance

end
end GromovWitten.AlgebraicGeometry.Curves
