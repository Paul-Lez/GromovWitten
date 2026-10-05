/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteAffineCechComplex
import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechScalarEvaluation
import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechPreimage

/-!
# Scalar extension of geometric finite affine Čech complexes

The canonical base-change maps on affine-open sections induce a comparison from
the scalar extension of the finite Čech complex to the complex on the preimage
cover. It is a quasi-isomorphism for quasi-coherent coefficients on a separated
source, without flatness or Noetherian assumptions.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- Scalar extension identifies the source with the Čech complex of the extended
section presheaf. -/
noncomputable def finiteCechGeometricBaseChangeSourceIso
    (s : X ⟶ Spec R) (φ : R ⟶ T) (M : X.Modules)
    (U : List X.Opens) :
    ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (.up ℤ)).obj
        (baseFiniteCechComplex s M U) ≅
      ((finiteCechComplex
        ((HomologicalComplex.single (Presheaves X.toTopCat T) (.up ℤ) 0).obj
          ((mapPresheafFunctor (X := X.toTopCat)
            (ModuleCat.extendScalars φ.hom)).obj (baseSectionsPresheaf s M))) U).obj
    (op ⊤)) := by
  let E := ModuleCat.extendScalars φ.hom
  let H := mapPresheafFunctor (X := X.toTopCat) E
  let evT := (evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
  let evTHC := evT.mapHomologicalComplex (.up ℤ)
  letI : PreservesBinaryBiproducts E :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts E
  letI : E.Additive := Functor.additive_of_preservesBinaryBiproducts E
  letI : H.Additive := mapPresheafFunctor_additive (X := X.toTopCat) E
  let F := baseSectionsSingle s M
  let singleScalarIso := (singleMapHomologicalComplex H (.up ℤ) 0).app
    (baseSectionsPresheaf s M)
  change (E.mapHomologicalComplex (.up ℤ)).obj
      ((finiteCechComplex F U).obj (op ⊤)) ≅ _
  exact finiteCechScalarComparisonAt (X := X.toTopCat) E F U ⊤ ≪≫
    evTHC.mapIso ((finiteCechFunctor (X := X.toTopCat) (R := T) U).mapIso
      singleScalarIso)

private noncomputable def finiteCechGeometricBaseChangeMiddleMap
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules)
    (U : List X.Opens) :
    ((finiteCechComplex
      ((HomologicalComplex.single (Presheaves X.toTopCat T) (.up ℤ) 0).obj
        ((mapPresheafFunctor (X := X.toTopCat)
          (ModuleCat.extendScalars φ.hom)).obj (baseSectionsPresheaf s M))) U).obj
          (op ⊤)) ⟶
      ((finiteCechComplex
        ((HomologicalComplex.single (Presheaves X.toTopCat T) (.up ℤ) 0).obj
          ((TopologicalSpace.Opens.map p.base).op ⋙
            baseSectionsPresheaf g ((Scheme.Modules.pullback p).obj M))) U).obj
          (op ⊤)) :=
  (evaluatePresheafComplexMap
    (finiteCechMap
      ((HomologicalComplex.single (Presheaves X.toTopCat T) (.up ℤ) 0).map
        (baseSectionsPresheafBaseChange s φ p g h M)) U)).app (op ⊤)

/-- The reindexed target Čech complex is the geometric complex on the preimage list. -/
noncomputable def finiteCechGeometricBaseChangeTargetIso
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (M : X.Modules)
    (U : List X.Opens) :
    ((finiteCechComplex
      ((HomologicalComplex.single (Presheaves X.toTopCat T) (.up ℤ) 0).obj
        ((TopologicalSpace.Opens.map p.base).op ⋙
          baseSectionsPresheaf g ((Scheme.Modules.pullback p).obj M))) U).obj
          (op ⊤)) ≅
      baseFiniteCechComplex g ((Scheme.Modules.pullback p).obj M)
        (U.map (TopologicalSpace.Opens.map p.base).obj) := by
  let dstSheaf := baseSectionsPresheaf g ((Scheme.Modules.pullback p).obj M)
  let dstSingle := baseSectionsSingle g ((Scheme.Modules.pullback p).obj M)
  let preH := reindexPresheafFunctor (X := X.toTopCat) (Y := Y.toTopCat) (R := T) p.base
  let preHC := reindexPresheafComplexFunctor
    (X := X.toTopCat) (Y := Y.toTopCat) (R := T) p.base
  letI : preH.Additive := reindexPresheafFunctor_additive p.base
  let preU := U.map (TopologicalSpace.Opens.map p.base).obj
  let preimageData := finiteCechPreimageData p.base dstSingle U
  let singlePreimageIso := (singleMapHomologicalComplex preH (.up ℤ) 0).app dstSheaf
  let dataIso := preimageData.complexIso ≪≫
    (finiteCechFunctor (X := X.toTopCat) (R := T) U).mapIso singlePreimageIso
  let evX := ((evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)).mapHomologicalComplex
    (.up ℤ)
  let finalIso : evX.obj (preHC.obj
      ((finiteCechFunctor (X := Y.toTopCat) (R := T) preU).obj dstSingle)) ≅
        baseFiniteCechComplex g ((Scheme.Modules.pullback p).obj M) preU := by
    apply eqToIso
    exact reindex_evaluate_top_obj p.base
      ((finiteCechFunctor (X := Y.toTopCat) (R := T) preU).obj dstSingle)
  exact (evX.mapIso dataIso).symm ≪≫ finalIso

/-- The geometric base-change chain map, induced by canonical base change of open sections. -/
noncomputable def finiteCechGeometricBaseChangeMap
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules)
    (U : List X.Opens) :
    ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (.up ℤ)).obj
        (baseFiniteCechComplex s M U) ⟶
      baseFiniteCechComplex g ((Scheme.Modules.pullback p).obj M)
        (U.map (TopologicalSpace.Opens.map p.base).obj) :=
  (finiteCechGeometricBaseChangeSourceIso s φ M U).hom ≫
    finiteCechGeometricBaseChangeMiddleMap s φ p g h M U ≫
    (finiteCechGeometricBaseChangeTargetIso p g M U).hom

/-- Affine local base change makes the geometric finite Čech comparison a quasi-isomorphism. -/
lemma finiteCechGeometricBaseChangeMap_quasiIso
    [X.IsSeparated]
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W) :
    QuasiIso (finiteCechGeometricBaseChangeMap s φ p g h M U) := by
  let eLeft := finiteCechGeometricBaseChangeSourceIso s φ M U
  let fMiddle := finiteCechGeometricBaseChangeMiddleMap s φ p g h M U
  let eRight := finiteCechGeometricBaseChangeTargetIso p g M U
  have hf : QuasiIso fMiddle := by
    change QuasiIso ((evaluatePresheafComplexMap
      (finiteCechMap
        ((HomologicalComplex.single (Presheaves X.toTopCat T) (.up ℤ) 0).map
          (baseSectionsPresheafBaseChange s φ p g h M)) U)).app (op ⊤))
    exact finiteCech_single_baseChange_quasiIso_at s φ p g h M U hU
  have hRight : QuasiIso (fMiddle ≫ eRight.hom) :=
    (quasiIso_iff_comp_right fMiddle eRight.hom).2 hf
  change QuasiIso (eLeft.hom ≫ fMiddle ≫ eRight.hom)
  exact (quasiIso_iff_comp_left eLeft.hom (fMiddle ≫ eRight.hom)).2 hRight

end GromovWitten.AlgebraicGeometry.Curves
