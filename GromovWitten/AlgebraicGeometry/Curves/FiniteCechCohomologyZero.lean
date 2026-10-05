/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteAffineCechComplex
import GromovWitten.AlgebraicGeometry.Curves.FlasqueFiniteCechComparison
import GromovWitten.AlgebraicGeometry.Curves.BaseSectionsFlasqueCohomology
import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechQuasiIsoZero
/-!
# Degree-zero cohomology from an arbitrary finite open cover

The canonical finite Čech augmentation of a module sheaf induces an isomorphism
in degree zero on global sections. The proof compares with an injective
resolution, using left exactness of sections and the finite-cover comparison
for flasque complexes. No affine, Noetherian, or quasi-coherence hypothesis is
needed for this degree-zero statement.
-/
open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R : CommRingCat.{u}} {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- On global sections, the finite Čech augmentation of a module sheaf is a
quasi-isomorphism in degree zero whenever the finite list covers the scheme. -/
lemma finiteCechAugmentation_baseSectionsSingle_quasiIsoAt_zero
    (s : X ⟶ Spec R) (M : X.Modules)
    (U : List X.Opens) (hcover : coverUnion U = ⊤) :
    QuasiIsoAt ((finiteCechAugmentation (baseSectionsSingle s M) U).app (op ⊤)) (0 : ℤ) := by
  let K := (injectiveResolution M).cocomplex
  let a := (injectiveResolution M).ι
  have hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)) :=
    fun n => module_isFlasque_of_injective (K.X n)
  let KI := K.extend ComplexShape.embeddingUpNat
  let F := ((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj KI
  let f : baseSectionsSingle s M ⟶ F := resolutionSectionsAugmentation s a
  let E := ((evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op ⊤)).mapHomologicalComplex (.up ℤ)
  have ha0 : QuasiIsoAt (E.map f) (0 : ℤ) :=
    resolutionSectionsAugmentation_quasiIsoAt_zero s a ⊤
  have hf : QuasiIsoAt (E.map (finiteCechMap f U)) (0 : ℤ) := by
    apply finiteCechMap_quasiIsoAt_zero_of_pointwise f
    · intro i hi
      exact isZero_single_obj_X (.up ℤ) 0 (baseSectionsPresheaf s M) i (by omega)
    · intro i hi
      change IsZero ((baseSectionsPresheafFunctor s).obj (KI.X i))
      apply Functor.map_isZero
      exact K.isZero_extend_X ComplexShape.embeddingUpNat i (by
        intro n hn
        change (n : ℤ) = i at hn
        omega)
    · intro W
      exact resolutionSectionsAugmentation_quasiIsoAt_zero s a W
  have hg : QuasiIso (E.map (finiteCechData F U).augmentation) :=
    finiteCechAugmentation_baseSections_quasiIso s KI
      (moduleFlasque_extend_nat K hK) U ⊤ (by rw [hcover])
  have hsquare : E.map (finiteCechData (baseSectionsSingle s M) U).augmentation ≫
      E.map (finiteCechMap f U) = E.map f ≫ E.map (finiteCechData F U).augmentation := by
    simpa only [Functor.map_comp] using
      congrArg E.map (finiteCechMap_augmentation_natural f U)
  have : QuasiIsoAt (E.map (finiteCechData (baseSectionsSingle s M) U).augmentation ≫
      E.map (finiteCechMap f U)) (0 : ℤ) := by
    rw [hsquare]
    infer_instance
  exact (quasiIsoAt_iff_comp_right _ (E.map (finiteCechMap f U)) (0 : ℤ)).mp this

/-- The finite Čech augmentation with the global base-linear section module as source. -/
noncomputable def baseFiniteCechAugmentation
    (s : X ⟶ Spec R) (M : X.Modules) (U : List X.Opens) :
    (HomologicalComplex.single (ModuleCat R) (.up ℤ) 0).obj
        (baseSectionModule s ⊤ M) ⟶ baseFiniteCechComplex s M U := by
  let P := baseSectionsPresheaf s M
  let evR := (evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op ⊤)
  let toSingle := singleMapHomologicalComplex evR (.up ℤ) 0
  change (HomologicalComplex.single (ModuleCat R) (.up ℤ) 0).obj (evR.obj P) ⟶ _
  exact toSingle.inv.app P ≫
    (evaluatePresheafComplexMap (finiteCechData (baseSectionsSingle s M) U).augmentation).app
      (op ⊤)

set_option backward.isDefEq.respectTransparency false in
/-- A finite open cover computes global base-linear sections in degree zero. -/
lemma baseFiniteCechAugmentation_quasiIsoAt_zero
    (s : X ⟶ Spec R) (M : X.Modules)
    (U : List X.Opens) (hcover : coverUnion U = ⊤) :
    QuasiIsoAt (baseFiniteCechAugmentation s M U) (0 : ℤ) := by
  let P := baseSectionsPresheaf s M
  let evR := (evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op ⊤)
  let toSingle := singleMapHomologicalComplex evR (.up ℤ) 0
  change QuasiIsoAt (toSingle.inv.app P ≫
    (evaluatePresheafComplexMap
      (finiteCechData (baseSectionsSingle s M) U).augmentation).app (op ⊤)) (0 : ℤ)
  have hEval : QuasiIsoAt
      ((finiteCechAugmentation (baseSectionsSingle s M) U).app (op ⊤)) (0 : ℤ) :=
    finiteCechAugmentation_baseSectionsSingle_quasiIsoAt_zero s M U hcover
  rw [quasiIsoAt_iff_comp_left _ _ (0 : ℤ)]
  exact hEval


end GromovWitten.AlgebraicGeometry.Curves
