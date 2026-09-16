/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Line bundles on schemes

This file supplies the rank-one refinement of Mathlib's locally-free sheaf predicate that is
needed by the curve and stable-reduction layers.  A rank-one local trivialization is expressed by
local generator data whose basis type is equivalent to `PUnit`.  The definition therefore refers
to actual sheaves of modules and actual local trivializations, not merely to a numerical class.

The local trivializations are also pulled through the cartesian square associated to an open set.
This proves that arbitrary scheme pullback preserves invertibility, so pullback is an
unconditional operation on bundled line bundles.  The coherence isomorphism for an iterated
pullback is inherited from `Scheme.Modules.pullbackComp`.
-/

open CategoryTheory MonoidalCategory BraidedCategory
open _root_.AlgebraicGeometry
open TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X Y Z : Scheme.{u}}

namespace TopologicalSpace.Opens

/-- Inverse image on open subsets is a final functor.  For every open subset of the source,
the structured-arrow category has the object defined by its inclusion into the inverse image of
the top open as a terminal object. -/
instance mapFinal {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Functor.Final (Opens.map f) where
  out U := by
    let T : StructuredArrow U (Opens.map f) :=
      StructuredArrow.mk (Opens.leMapTop f U)
    apply isConnected_of_isTerminal _
      (Limits.IsTerminal.ofUniqueHom
        (Y := T)
        (fun A ↦ StructuredArrow.homMk (Opens.leTop A.right) (by subsingleton))
        (fun _ _ ↦ by subsingleton))

end TopologicalSpace.Opens

/-- The raw local-trivialization predicate: a cover on which the module is free on one
generator. -/
def HasRankOneTrivialization : ObjectProperty X.Modules := fun M ↦
  ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
    q.IsLocallyFreeData ∧ ∀ i, Nonempty ((q.generators i).I ≃ ULift.{u, 0} PUnit)

/-- An `O_X`-module is invertible when it is isomorphic to a module admitting a rank-one local
trivialization.  Taking the categorical isomorphism closure makes invariance under presentation
part of the definition. -/
def IsInvertible : ObjectProperty X.Modules :=
  ObjectProperty.isoClosure (HasRankOneTrivialization (X := X))

namespace IsInvertible

/-- The free module sheaf on one generator has a rank-one local trivialization. -/
theorem free_punit_hasRankOneTrivialization (X : Scheme.{u}) :
    HasRankOneTrivialization
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u, 0} PUnit)) := by
  let q :=
    (SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf) (ULift.{u, 0} PUnit)).localGeneratorsData
  refine ⟨q, inferInstance, ?_⟩
  intro i
  exact ⟨Equiv.refl (ULift.{u, 0} PUnit)⟩

/-- The free module sheaf on one generator is invertible. -/
theorem free_punit (X : Scheme.{u}) :
    IsInvertible (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u, 0} PUnit)) :=
  ⟨_, free_punit_hasRankOneTrivialization X, ⟨Iso.refl _⟩⟩

/-- An invertible module has an isomorphic representative which is locally free. -/
theorem exists_isLocallyFree_iso {M : X.Modules} (h : IsInvertible M) :
    ∃ N : X.Modules, SheafOfModules.IsLocallyFree (R := X.ringCatSheaf) N ∧
      Nonempty (M ≅ N) := by
  obtain ⟨N, ⟨q, hq, -⟩, e⟩ := h
  let _ : q.IsLocallyFreeData := hq
  exact ⟨N, q.isLocallyFree, e⟩

/-- Invertibility is invariant under isomorphism of sheaves of modules. -/
theorem of_iso {M N : X.Modules} (e : M ≅ N) (hM : IsInvertible M) :
    IsInvertible N := by
  obtain ⟨A, hA, ⟨i⟩⟩ := hM
  exact ⟨A, hA, ⟨e.symm.trans i⟩⟩

end IsInvertible

/-! ## Tensor products of module sheaves

The tensor product of two sheaves of modules is not in general computed objectwise on opens.
We first form the objectwise tensor product as a presheaf of modules and then sheafify it.  This
is the genuine sheaf tensor product; `moduleTensorHomEquiv` records its universal property with
respect to the sheafification adjunction.
-/

/-- The objectwise tensor product of the underlying presheaves of two module sheaves. -/
def moduleTensorPresheaf (M N : X.Modules) : X.PresheafOfModules :=
  PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M.val N.val

/-- The tensor product of two `O_X`-modules, obtained by sheafifying their presheaf tensor
product. -/
def moduleTensor (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (moduleTensorPresheaf M N)

/-! ### Restriction of arbitrary module sheafifications -/

/-- Restrict a module presheaf to the over-site of an open subset. -/
def modulePresheafOver (P : X.PresheafOfModules) (U : X.Opens) :
    PresheafOfModules.{u} (X.ringCatSheaf.over U).obj :=
  (PresheafOfModules.pushforward
    (F := Over.forget U) (𝟙 (X.ringCatSheaf.over U).obj)).obj P

set_option maxHeartbeats 400000 in
-- Unfolding the module structures on the over-site is elaboration-intensive.
/-- Restriction of the sheafification unit for an arbitrary module presheaf. -/
def moduleSheafificationRestrictedUnit (P : X.PresheafOfModules) (U : X.Opens) :
    modulePresheafOver P U ⟶
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U |>.val where
  app A := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app P).app (Opposite.op A.unop.left)
  naturality {A B} f := by
    exact ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P).naturality ((Over.forget U).op.map f)

/-- The universal comparison from sheafifying on an open over-site to restricting the global
sheafification. -/
def moduleSheafificationOverComparison (P : X.PresheafOfModules) (U : X.Opens) :
    (PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over U).obj)).obj (modulePresheafOver P U) ⟶
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (X.ringCatSheaf.over U).obj)).symm
      (moduleSheafificationRestrictedUnit P U)

lemma moduleSheafificationOverComparison_fac (P : X.PresheafOfModules) (U : X.Opens) :
    CategoryTheory.toSheafify ((Opens.grothendieckTopology X).over U)
        (modulePresheafOver P U).presheaf ≫
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleSheafificationOverComparison P U).val =
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleSheafificationRestrictedUnit P U) := by
  let moduleEquiv := PresheafOfModules.sheafificationHomEquiv
    (P := modulePresheafOver P U)
    (F := ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U)
    (𝟙 (X.ringCatSheaf.over U).obj)
  have hc : (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (X.ringCatSheaf.over U).obj)) (moduleSheafificationOverComparison P U) =
      moduleSheafificationRestrictedUnit P U := by
    change moduleEquiv (moduleEquiv.symm (moduleSheafificationRestrictedUnit P U)) = _
    exact moduleEquiv.apply_symm_apply _
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 (X.ringCatSheaf.over U).obj) (moduleSheafificationOverComparison P U)
  rw [hc] at h
  exact h.symm

set_option maxHeartbeats 400000 in
-- Unfolding the restricted module map to its additive presheaf is elaboration-intensive.
instance moduleSheafificationRestrictedUnit_isLocallyInjective
    (P : X.PresheafOfModules) (U : X.Opens) :
    Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
      ((PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleSheafificationRestrictedUnit P U)) := by
  change Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
    (Functor.whiskerLeft (Over.forget U).op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))
  exact Presheaf.isLocallyInjective_whisker
    (J := (Opens.grothendieckTopology X).over U)
    (K := Opens.grothendieckTopology X) (A := AddCommGrpCat.{u})
    (Over.forget U) _

set_option maxHeartbeats 400000 in
-- Unfolding the restricted module map to its additive presheaf is elaboration-intensive.
instance moduleSheafificationRestrictedUnit_isLocallySurjective
    (P : X.PresheafOfModules) (U : X.Opens) :
    Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      ((PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleSheafificationRestrictedUnit P U)) := by
  change Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
    (Functor.whiskerLeft (Over.forget U).op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))
  exact Presheaf.isLocallySurjective_whisker
    (J := (Opens.grothendieckTopology X).over U)
    (K := Opens.grothendieckTopology X) (A := AddCommGrpCat.{u})
    (Over.forget U) _

set_option maxHeartbeats 400000 in
-- Comparing the module and additive sheafification adjunctions is elaboration-intensive.
set_option linter.style.haveILetI false in
instance moduleSheafificationOverComparison_isIso
    (P : X.PresheafOfModules) (U : X.Opens) :
    IsIso (moduleSheafificationOverComparison P U) := by
  letI : ((Opens.grothendieckTopology X).over U).HasSheafCompose
      (forget AddCommGrpCat.{u}) := by
    apply CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.toSheaf (X.ringCatSheaf.over U))]
  apply (Sheaf.isLocallyBijective_iff_isIso
    (J := (Opens.grothendieckTopology X).over U)
    (A := AddCommGrpCat.{u})
    ((SheafOfModules.toSheaf (X.ringCatSheaf.over U)).map
      (moduleSheafificationOverComparison P U))).mp
  let f := CategoryTheory.toSheafify ((Opens.grothendieckTopology X).over U)
    (modulePresheafOver P U).presheaf
  let g := (PresheafOfModules.toPresheaf
    (X.ringCatSheaf.over U).obj).map (moduleSheafificationOverComparison P U).val
  have fac : f ≫ g =
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleSheafificationRestrictedUnit P U) :=
    moduleSheafificationOverComparison_fac P U
  haveI : Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
      (f ≫ g) :=
    fac.symm ▸ moduleSheafificationRestrictedUnit_isLocallyInjective P U
  haveI : Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      (f ≫ g) :=
    fac.symm ▸ moduleSheafificationRestrictedUnit_isLocallySurjective P U
  haveI : Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U) f :=
    inferInstance
  constructor
  · change Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U) g
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective _ f g
  · change Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U) g
    exact Presheaf.isLocallySurjective_of_isLocallySurjective _ f g

/-- Sheafification of an arbitrary module presheaf commutes with restriction to an open
over-site. -/
def moduleSheafificationOverIso (P : X.PresheafOfModules) (U : X.Opens) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U ≅
      (PresheafOfModules.sheafification
        (𝟙 (X.ringCatSheaf.over U).obj)).obj (modulePresheafOver P U) :=
  (asIso (moduleSheafificationOverComparison P U)).symm

set_option maxHeartbeats 1200000 in
-- Unfolding both pushforward module structures to recognize the identity is expensive.
/-- Restriction of module presheaves commutes definitionally with their objectwise tensor
product. -/
def modulePresheafOverTensorIso (P Q : X.PresheafOfModules) (U : X.Opens) :
    modulePresheafOver
        (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) P Q) U ≅
      PresheafOfModules.Monoidal.tensorObj
        (R := (X.sheaf.over U).obj) (modulePresheafOver P U) (modulePresheafOver Q U) :=
  Iso.refl _

/-- The presheaf tensor product on the over-site of an open subset.  This auxiliary object is
used to compare the global sheaf tensor product with tensor product after restriction. -/
def moduleTensorOverPresheaf (U : X.Opens)
    (M N : SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
  PresheafOfModules.Monoidal.tensorObj
    (R := (X.sheaf.over U).obj) M.val N.val

/-- The genuine tensor product of two module sheaves on the over-site of an open subset. -/
def moduleTensorOver (U : X.Opens)
    (M N : SheafOfModules.{u} (X.ringCatSheaf.over U)) :
    SheafOfModules.{u} (X.ringCatSheaf.over U) :=
  (PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)).obj
    (moduleTensorOverPresheaf U M N)

set_option maxHeartbeats 400000 in
-- Unfolding the module structures on the over-site is elaboration-intensive.
/-- Restriction of the global tensor sheafification unit to an open subset. -/
def moduleTensorRestrictedUnit (M N : X.Modules) (U : X.Opens) :
    moduleTensorOverPresheaf U (M.over U) (N.over U) ⟶
      ((moduleTensor M N).over U).val where
  app A := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (moduleTensorPresheaf M N)).app
      (Opposite.op A.unop.left)
  naturality {A B} f := by
    exact ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app
        (moduleTensorPresheaf M N)).naturality ((Over.forget U).op.map f)

/-- The sheafification universal property supplies the comparison from tensoring on an open
subset to restricting the global tensor product. -/
def moduleTensorOverComparison (M N : X.Modules) (U : X.Opens) :
    moduleTensorOver U (M.over U) (N.over U) ⟶ (moduleTensor M N).over U :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (X.ringCatSheaf.over U).obj)).symm
      (moduleTensorRestrictedUnit M N U)

lemma moduleTensorOverComparison_fac (M N : X.Modules) (U : X.Opens) :
    CategoryTheory.toSheafify ((Opens.grothendieckTopology X).over U)
        (moduleTensorOverPresheaf U (M.over U) (N.over U)).presheaf ≫
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleTensorOverComparison M N U).val =
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleTensorRestrictedUnit M N U) := by
  let moduleEquiv := PresheafOfModules.sheafificationHomEquiv
    (P := moduleTensorOverPresheaf U (M.over U) (N.over U))
    (F := (moduleTensor M N).over U)
    (𝟙 (X.ringCatSheaf.over U).obj)
  have hc : (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (X.ringCatSheaf.over U).obj)) (moduleTensorOverComparison M N U) =
      moduleTensorRestrictedUnit M N U := by
    change moduleEquiv (moduleEquiv.symm (moduleTensorRestrictedUnit M N U)) = _
    exact moduleEquiv.apply_symm_apply _
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 (X.ringCatSheaf.over U).obj) (moduleTensorOverComparison M N U)
  rw [hc] at h
  exact h.symm

set_option maxHeartbeats 400000 in
-- Unfolding the restricted module map to its additive presheaf is elaboration-intensive.
instance moduleTensorRestrictedUnit_isLocallyInjective
    (M N : X.Modules) (U : X.Opens) :
    Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
      ((PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleTensorRestrictedUnit M N U)) := by
  change Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
    (Functor.whiskerLeft (Over.forget U).op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (moduleTensorPresheaf M N).presheaf))
  exact Presheaf.isLocallyInjective_whisker
    (J := (Opens.grothendieckTopology X).over U)
    (K := Opens.grothendieckTopology X) (A := AddCommGrpCat.{u})
    (Over.forget U) _

set_option maxHeartbeats 400000 in
-- Unfolding the restricted module map to its additive presheaf is elaboration-intensive.
instance moduleTensorRestrictedUnit_isLocallySurjective
    (M N : X.Modules) (U : X.Opens) :
    Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      ((PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleTensorRestrictedUnit M N U)) := by
  change Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
    (Functor.whiskerLeft (Over.forget U).op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (moduleTensorPresheaf M N).presheaf))
  exact Presheaf.isLocallySurjective_whisker
    (J := (Opens.grothendieckTopology X).over U)
    (K := Opens.grothendieckTopology X) (A := AddCommGrpCat.{u})
    (Over.forget U) _

set_option maxHeartbeats 400000 in
-- Comparing the module and additive sheafification adjunctions is elaboration-intensive.
set_option linter.style.haveILetI false in
instance moduleTensorOverComparison_isIso (M N : X.Modules) (U : X.Opens) :
    IsIso (moduleTensorOverComparison M N U) := by
  letI : ((Opens.grothendieckTopology X).over U).HasSheafCompose
      (forget AddCommGrpCat.{u}) := by
    apply CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.toSheaf (X.ringCatSheaf.over U))]
  apply (Sheaf.isLocallyBijective_iff_isIso
    (J := (Opens.grothendieckTopology X).over U)
    (A := AddCommGrpCat.{u})
    ((SheafOfModules.toSheaf (X.ringCatSheaf.over U)).map
      (moduleTensorOverComparison M N U))).mp
  let f := CategoryTheory.toSheafify ((Opens.grothendieckTopology X).over U)
    (moduleTensorOverPresheaf U (M.over U) (N.over U)).presheaf
  let g := (PresheafOfModules.toPresheaf
    (X.ringCatSheaf.over U).obj).map (moduleTensorOverComparison M N U).val
  have fac : f ≫ g =
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleTensorRestrictedUnit M N U) :=
    moduleTensorOverComparison_fac M N U
  haveI : Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
      (f ≫ g) :=
    fac.symm ▸ moduleTensorRestrictedUnit_isLocallyInjective M N U
  haveI : Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      (f ≫ g) :=
    fac.symm ▸ moduleTensorRestrictedUnit_isLocallySurjective M N U
  haveI : Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U) f :=
    inferInstance
  constructor
  · change Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U) g
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective _ f g
  · change Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U) g
    exact Presheaf.isLocallySurjective_of_isLocallySurjective _ f g

/-- Restriction to an open subset commutes with the genuine sheaf tensor product. -/
def moduleTensorOverIso (M N : X.Modules) (U : X.Opens) :
    (moduleTensor M N).over U ≅ moduleTensorOver U (M.over U) (N.over U) :=
  (asIso (moduleTensorOverComparison M N U)).symm

/-! ### Tensor products after restriction to an open subscheme -/

set_option linter.style.haveILetI false in
/-- Restriction of scalars along a ring equivalence preserves tensor products. -/
lemma moduleCatRestrictScalarsTensorMap_isIso {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M N : ModuleCat S) :
    IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  letI : Module R M := Module.compHom M e.toRingHom
  letI : Module R N := Module.compHom N e.toRingHom
  letI : Module S ((ModuleCat.restrictScalars e.toRingHom).obj M) :=
    inferInstanceAs (Module S M)
  letI : Module S ((ModuleCat.restrictScalars e.toRingHom).obj N) :=
    inferInstanceAs (Module S N)
  letI : SMulCommClass S R M := {
    smul_comm s r m := by
      change s • (e r • m) = e r • (s • m)
      rw [smul_smul, smul_smul, mul_comm] }
  letI : SMulCommClass S R N := {
    smul_comm s r n := by
      change s • (e r • n) = e r • (s • n)
      rw [smul_smul, smul_smul, mul_comm] }
  letI : TensorProduct.CompatibleSMul S R M N := {
    smul_tmul r m n := by
      change (e r • m) ⊗ₜ[S] n = m ⊗ₜ[S] (e r • n)
      exact TensorProduct.smul_tmul (R := S) (e r) m n }
  letI : TensorProduct.CompatibleSMul R S M N := {
    smul_tmul s m n := by
      rw [← e.apply_symm_apply s]
      change ((e.symm s : R) • m) ⊗ₜ[R] n =
        m ⊗ₜ[R] ((e.symm s : R) • n)
      exact TensorProduct.smul_tmul (R := R) (e.symm s) m n }
  let E := TensorProduct.equivOfCompatibleSMul S R R M N
  have hmap :
      (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N).hom =
        E.toLinearMap := by
    apply TensorProduct.ext
    ext m n
    change (Functor.LaxMonoidal.μ
      (ModuleCat.restrictScalars e.toRingHom) M N).hom (m ⊗ₜ[R] n) =
        E (m ⊗ₜ[R] n)
    erw [ModuleCat.restrictScalars_μ_tmul]
    rfl
  have hfun :
      (ConcreteCategory.hom
        (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) :
          (TensorProduct R M N → TensorProduct S M N)) = E := by
    exact funext (DFunLike.congr_fun hmap)
  rw [hfun]
  exact E.bijective

/-- The morphism of ring presheaves which realizes restriction to an open subscheme. -/
def moduleRestrictRingHom (U : X.Opens) :
    (U : Scheme.{u}).ringCatSheaf.obj ⟶
      U.ι.opensFunctor.op ⋙ X.ringCatSheaf.obj where
  app A := (forget₂ CommRingCat RingCat).map (U.ι.appIso A.unop).inv
  naturality {A B} g := by
    exact congr_arg (fun k => (forget₂ CommRingCat RingCat).map k)
      (U.ι.appIso_inv_naturality g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Unfolding the pointwise tensor and restriction-of-scalars structures is expensive.
/-- The pointwise tensor comparison for restricting module presheaves to an open subscheme. -/
def modulePresheafRestrictTensorMap (U : X.Opens) (M N : X.PresheafOfModules) :
    PresheafOfModules.Monoidal.tensorObj
        ((PresheafOfModules.pushforward (moduleRestrictRingHom U)).obj M)
        ((PresheafOfModules.pushforward (moduleRestrictRingHom U)).obj N) ⟶
      (PresheafOfModules.pushforward (moduleRestrictRingHom U)).obj
        (PresheafOfModules.Monoidal.tensorObj M N) where
  app A := Functor.LaxMonoidal.μ
    (ModuleCat.restrictScalars ((moduleRestrictRingHom U).app A).hom)
      (M.obj _) (N.obj _)
  naturality {A B} g := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    dsimp
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
    erw [ModuleCat.restrictScalars_μ_tmul]
    erw [ModuleCat.restrictScalars_μ_tmul]
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
lemma modulePresheafRestrictTensorMap_toPresheaf_isIso
    (U : X.Opens) (M N : X.PresheafOfModules) :
    IsIso ((PresheafOfModules.toPresheaf
      ((U : Scheme.{u}).ringCatSheaf.obj)).map
        (modulePresheafRestrictTensorMap U M N)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  dsimp only [modulePresheafRestrictTensorMap, moduleRestrictRingHom]
  letI : IsIso (Functor.LaxMonoidal.μ
      (ModuleCat.restrictScalars (U.ι.appIso A.unop).inv.hom)
        (M.obj (Opposite.op (U.ι ''ᵁ A.unop)))
        (N.obj (Opposite.op (U.ι ''ᵁ A.unop)))) :=
    moduleCatRestrictScalarsTensorMap_isIso
      (U.ι.appIso A.unop).symm.commRingCatIsoToRingEquiv (M.obj _) (N.obj _)
  have hb := (ConcreteCategory.isIso_iff_bijective (f :=
    Functor.LaxMonoidal.μ
      (ModuleCat.restrictScalars (U.ι.appIso A.unop).inv.hom)
        (M.obj (Opposite.op (U.ι ''ᵁ A.unop)))
        (N.obj (Opposite.op (U.ι ''ᵁ A.unop))))).mp (by infer_instance)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hb

set_option backward.isDefEq.respectTransparency false in
instance modulePresheafRestrictTensorMap_isIso
    (U : X.Opens) (M N : X.PresheafOfModules) :
    IsIso (modulePresheafRestrictTensorMap U M N) := by
  rw [← isIso_iff_of_reflects_iso _
    (PresheafOfModules.toPresheaf
      ((U : Scheme.{u}).ringCatSheaf.obj))]
  exact modulePresheafRestrictTensorMap_toPresheaf_isIso U M N

/-- The restricted tensor sheafification unit, including the pointwise tensor comparison. -/
def moduleTensorRestrictUnit (U : X.Opens) (M N : X.Modules) :
    moduleTensorPresheaf
        ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N) ⟶
      ((Scheme.Modules.restrictFunctor U.ι).obj (moduleTensor M N)).val :=
  modulePresheafRestrictTensorMap U M.val N.val ≫
    (PresheafOfModules.pushforward (moduleRestrictRingHom U)).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app (moduleTensorPresheaf M N))

/-- The canonical comparison from tensoring restricted modules to restricting their tensor. -/
def moduleTensorRestrictComparison (U : X.Opens) (M N : X.Modules) :
    moduleTensor
        ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj (moduleTensor M N) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).symm (moduleTensorRestrictUnit U M N)

set_option maxHeartbeats 800000 in
-- Unfolding restriction and the sheafification unit simultaneously is expensive.
set_option linter.style.haveILetI false in
instance moduleTensorRestrictUnit_isLocallyInjective
    (U : X.Opens) (M N : X.Modules) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (U : Scheme.{u}))
      ((PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        (moduleTensorRestrictUnit U M N)) := by
  change Presheaf.IsLocallyInjective (Opens.grothendieckTopology (U : Scheme.{u}))
    ((PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        (modulePresheafRestrictTensorMap U M.val N.val) ≫
      (PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        ((PresheafOfModules.pushforward (moduleRestrictRingHom U)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app (moduleTensorPresheaf M N))))
  haveI : IsIso ((PresheafOfModules.toPresheaf
      (U : Scheme.{u}).ringCatSheaf.obj).map
        (modulePresheafRestrictTensorMap U M.val N.val)) :=
    modulePresheafRestrictTensorMap_toPresheaf_isIso U M.val N.val
  haveI ha : Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology (U : Scheme.{u}))
      ((PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        (modulePresheafRestrictTensorMap U M.val N.val)) := inferInstance
  have hb : Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology (U : Scheme.{u}))
      ((PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        ((PresheafOfModules.pushforward (moduleRestrictRingHom U)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app (moduleTensorPresheaf M N)))) := by
    change Presheaf.IsLocallyInjective (Opens.grothendieckTopology (U : Scheme.{u}))
      (Functor.whiskerLeft U.ι.opensFunctor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (moduleTensorPresheaf M N).presheaf))
    exact Presheaf.isLocallyInjective_whisker
      (J := Opens.grothendieckTopology (U : Scheme.{u}))
      (K := Opens.grothendieckTopology X) (A := AddCommGrpCat.{u})
      U.ι.opensFunctor _
  haveI hbInst : Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology (U : Scheme.{u}))
      ((PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        ((PresheafOfModules.pushforward (moduleRestrictRingHom U)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app (moduleTensorPresheaf M N)))) := hb
  exact @Presheaf.isLocallyInjective_comp
    _ _ _ _ _ _ _ _
    (Opens.grothendieckTopology (U : Scheme.{u})) _ _ _ _ _ ha hb

set_option maxHeartbeats 800000 in
-- Unfolding restriction and the sheafification unit simultaneously is expensive.
set_option linter.style.haveILetI false in
instance moduleTensorRestrictUnit_isLocallySurjective
    (U : X.Opens) (M N : X.Modules) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (U : Scheme.{u}))
      ((PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        (moduleTensorRestrictUnit U M N)) := by
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology (U : Scheme.{u}))
    ((PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        (modulePresheafRestrictTensorMap U M.val N.val) ≫
      (PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        ((PresheafOfModules.pushforward (moduleRestrictRingHom U)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app (moduleTensorPresheaf M N))))
  haveI : IsIso ((PresheafOfModules.toPresheaf
      (U : Scheme.{u}).ringCatSheaf.obj).map
        (modulePresheafRestrictTensorMap U M.val N.val)) :=
    modulePresheafRestrictTensorMap_toPresheaf_isIso U M.val N.val
  haveI ha : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (U : Scheme.{u}))
      ((PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        (modulePresheafRestrictTensorMap U M.val N.val)) :=
    Presheaf.isLocallySurjective_of_iso _ _
  have hb : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (U : Scheme.{u}))
      ((PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        ((PresheafOfModules.pushforward (moduleRestrictRingHom U)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app (moduleTensorPresheaf M N)))) := by
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology (U : Scheme.{u}))
      (Functor.whiskerLeft U.ι.opensFunctor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (moduleTensorPresheaf M N).presheaf))
    exact Presheaf.isLocallySurjective_whisker
      (J := Opens.grothendieckTopology (U : Scheme.{u}))
      (K := Opens.grothendieckTopology X) (A := AddCommGrpCat.{u})
      U.ι.opensFunctor _
  haveI hbInst : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (U : Scheme.{u}))
      ((PresheafOfModules.toPresheaf (U : Scheme.{u}).ringCatSheaf.obj).map
        ((PresheafOfModules.pushforward (moduleRestrictRingHom U)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app (moduleTensorPresheaf M N)))) := hb
  exact @Presheaf.isLocallySurjective_comp
    _ _ (Opens.grothendieckTopology (U : Scheme.{u}))
    _ _ _ _ _ _ _ _ _ _ _ ha hb

lemma moduleTensorRestrictComparison_fac (U : X.Opens) (M N : X.Modules) :
    CategoryTheory.toSheafify (Opens.grothendieckTopology (U : Scheme.{u}))
        (moduleTensorPresheaf
          ((Scheme.Modules.restrictFunctor U.ι).obj M)
          ((Scheme.Modules.restrictFunctor U.ι).obj N)).presheaf ≫
      (PresheafOfModules.toPresheaf
        (U : Scheme.{u}).ringCatSheaf.obj).map
          (moduleTensorRestrictComparison U M N).val =
      (PresheafOfModules.toPresheaf
        (U : Scheme.{u}).ringCatSheaf.obj).map
          (moduleTensorRestrictUnit U M N) := by
  let moduleEquiv := PresheafOfModules.sheafificationHomEquiv
    (P := moduleTensorPresheaf
      ((Scheme.Modules.restrictFunctor U.ι).obj M)
      ((Scheme.Modules.restrictFunctor U.ι).obj N))
    (F := (Scheme.Modules.restrictFunctor U.ι).obj (moduleTensor M N))
    (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)
  have hc : (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (U : Scheme.{u}).ringCatSheaf.obj))
        (moduleTensorRestrictComparison U M N) =
      moduleTensorRestrictUnit U M N := by
    change moduleEquiv (moduleEquiv.symm (moduleTensorRestrictUnit U M N)) = _
    exact moduleEquiv.apply_symm_apply _
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)
      (moduleTensorRestrictComparison U M N)
  rw [hc] at h
  exact h.symm

set_option maxHeartbeats 800000 in
-- Comparing the module and additive sheafification adjunctions is elaboration-intensive.
set_option linter.style.haveILetI false in
instance moduleTensorRestrictComparison_isIso
    (U : X.Opens) (M N : X.Modules) :
    IsIso (moduleTensorRestrictComparison U M N) := by
  letI : (Opens.grothendieckTopology (U : Scheme.{u})).HasSheafCompose
      (forget AddCommGrpCat.{u}) := by
    apply CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
  haveI hsheaf : IsIso
      ((SheafOfModules.toSheaf (U : Scheme.{u}).ringCatSheaf).map
        (moduleTensorRestrictComparison U M N)) := by
    apply (Sheaf.isLocallyBijective_iff_isIso
      (J := Opens.grothendieckTopology (U : Scheme.{u}))
      (A := AddCommGrpCat.{u})
      ((SheafOfModules.toSheaf (U : Scheme.{u}).ringCatSheaf).map
        (moduleTensorRestrictComparison U M N))).mp
    let f := CategoryTheory.toSheafify
      (Opens.grothendieckTopology (U : Scheme.{u}))
      (moduleTensorPresheaf
        ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N)).presheaf
    let g := (PresheafOfModules.toPresheaf
      (U : Scheme.{u}).ringCatSheaf.obj).map
        (moduleTensorRestrictComparison U M N).val
    have fac : f ≫ g = (PresheafOfModules.toPresheaf
        (U : Scheme.{u}).ringCatSheaf.obj).map
          (moduleTensorRestrictUnit U M N) :=
      moduleTensorRestrictComparison_fac U M N
    haveI : Presheaf.IsLocallyInjective
        (Opens.grothendieckTopology (U : Scheme.{u})) (f ≫ g) :=
      fac.symm ▸ moduleTensorRestrictUnit_isLocallyInjective U M N
    haveI : Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology (U : Scheme.{u})) (f ≫ g) :=
      fac.symm ▸ moduleTensorRestrictUnit_isLocallySurjective U M N
    haveI : Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology (U : Scheme.{u})) f := inferInstance
    constructor
    · change Presheaf.IsLocallyInjective
        (Opens.grothendieckTopology (U : Scheme.{u})) g
      exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective _ f g
    · change Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology (U : Scheme.{u})) g
      exact Presheaf.isLocallySurjective_of_isLocallySurjective _ f g
  haveI hforget : IsIso
      ((Scheme.Modules.toPresheafOfModules (U : Scheme.{u})).map
        (moduleTensorRestrictComparison U M N)) := by
    haveI hpresheaf : IsIso (((sheafToPresheaf
        (Opens.grothendieckTopology (U : Scheme.{u})) AddCommGrpCat).map
      ((SheafOfModules.toSheaf (U : Scheme.{u}).ringCatSheaf).map
        (moduleTensorRestrictComparison U M N)))) := inferInstance
    let inst (V : (Opens (U : Scheme.{u}))ᵒᵖ) :
        IsIso ((moduleTensorRestrictComparison U M N).val.app V) := by
      rw [← isIso_iff_of_reflects_iso
        ((moduleTensorRestrictComparison U M N).val.app V) (forget₂ _ AddCommGrpCat)]
      exact (NatTrans.isIso_iff_isIso_app
        ((SheafOfModules.toSheaf (U : Scheme.{u}).ringCatSheaf).map
          (moduleTensorRestrictComparison U M N)).hom).mp hpresheaf V
    letI (V : (Opens (U : Scheme.{u}))ᵒᵖ) :
        IsIso ((moduleTensorRestrictComparison U M N).val.app V) := inst V
    let e : (moduleTensor
          ((Scheme.Modules.restrictFunctor U.ι).obj M)
          ((Scheme.Modules.restrictFunctor U.ι).obj N)).val ≅
        ((Scheme.Modules.restrictFunctor U.ι).obj (moduleTensor M N)).val :=
      PresheafOfModules.isoMk
        (fun V ↦ asIso ((moduleTensorRestrictComparison U M N).val.app V))
    have he : e.hom = (moduleTensorRestrictComparison U M N).val := by ext V; rfl
    change IsIso (moduleTensorRestrictComparison U M N).val
    rw [← he]
    infer_instance
  exact Functor.ReflectsIsomorphisms.reflects
    (Scheme.Modules.toPresheafOfModules (U : Scheme.{u}))
      (moduleTensorRestrictComparison U M N)

/-- Restriction to an open subscheme commutes with the genuine sheaf tensor product. -/
def moduleTensorRestrictIso (U : X.Opens) (M N : X.Modules) :
    moduleTensor
        ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj (moduleTensor M N) :=
  asIso (moduleTensorRestrictComparison U M N)

set_option linter.style.haveILetI false in
/-- A morphism of module sheaves is an isomorphism if it is an isomorphism after restriction to
every member of an open cover.  This is the module-sheaf form of
`Sheaf.isIso_of_coversTop`; the proof explicitly reflects the resulting additive-sheaf
isomorphism back through the module structures. -/
theorem moduleHom_isIso_of_coversTop {M N : X.Modules} (f : M ⟶ N) {I : Type u}
    (U : I → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    (h : ∀ i, IsIso (f.over (U i))) : IsIso f := by
  haveI hsheaf : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    change IsIso ((SheafOfModules.toSheaf (X.ringCatSheaf.over (U i))).map
      (f.over (U i)))
    exact Functor.map_isIso _ _
  letI : (SheafOfModules.forget.{u} X.ringCatSheaf).ReflectsIsomorphisms :=
    (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).reflectsIsomorphisms
  haveI hforget : IsIso ((SheafOfModules.forget.{u} X.ringCatSheaf).map f) := by
    haveI hpresheaf : IsIso (((sheafToPresheaf
        (Opens.grothendieckTopology X) AddCommGrpCat).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f))) := inferInstance
    let inst (V : (Opens X)ᵒᵖ) : IsIso (f.val.app V) := by
      rw [← isIso_iff_of_reflects_iso (f.val.app V) (forget₂ _ AddCommGrpCat)]
      exact (NatTrans.isIso_iff_isIso_app
        ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom).mp hpresheaf V
    letI (V : (Opens X)ᵒᵖ) : IsIso (f.val.app V) := inst V
    let e : M.val ≅ N.val := PresheafOfModules.isoMk (fun V ↦ asIso (f.val.app V))
    have he : e.hom = f.val := by ext V; rfl
    change IsIso f.val
    rw [← he]
    infer_instance
  exact Functor.ReflectsIsomorphisms.reflects
    (SheafOfModules.forget.{u} X.ringCatSheaf) f

/-- Tensoring morphisms of module sheaves induces a morphism of their sheaf tensor products. -/
def moduleTensorMap {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    moduleTensor M N ⟶ moduleTensor M' N' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModules.Monoidal.tensorHom (R := X.sheaf.obj) f.val g.val)

/-! ### Tensoring a sheafification -/

/-- Sheafify the objectwise tensor of an arbitrary module presheaf with a module sheaf. -/
def moduleTensorPresheafSheafification
    (P : X.PresheafOfModules) (N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) P N.val)

/-- The canonical comparison from sheafifying `P ⊗ N` to tensoring the sheafification of
`P` with `N`.  It is induced by tensoring the sheafification unit of `P` with the identity of
`N`. -/
def moduleTensorSheafificationRightComparison
    (P : X.PresheafOfModules) (N : X.Modules) :
    moduleTensorPresheafSheafification P N ⟶
      moduleTensor
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) N := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P) ⊗ₘ 𝟙 N.val)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- The comparison for tensoring a sheafification is invariant under replacing the sheaf factor
by an isomorphic one. -/
theorem moduleTensorSheafificationRightComparison_isIso_of_iso
    (P : X.PresheafOfModules) {N N' : X.Modules} (e : N ≅ N')
    [IsIso (moduleTensorSheafificationRightComparison P N')] :
    IsIso (moduleTensorSheafificationRightComparison P N) := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app P
  let rightMap := L.map (𝟙 (L.obj P).val ⊗ₘ e.hom.val)
  let leftMap := L.map (𝟙 P ⊗ₘ e.hom.val)
  have hfac : moduleTensorSheafificationRightComparison P N ≫ rightMap =
      leftMap ≫ moduleTensorSheafificationRightComparison P N' := by
    dsimp [moduleTensorSheafificationRightComparison, rightMap, leftMap,
      moduleTensorPresheafSheafification, moduleTensor]
    change L.map (η ⊗ₘ 𝟙 N.val) ≫
      L.map (𝟙 (L.obj P).val ⊗ₘ e.hom.val) =
      L.map (𝟙 P ⊗ₘ e.hom.val) ≫ L.map (η ⊗ₘ 𝟙 N'.val)
    conv_lhs => rw [← L.map_comp]
    conv_rhs => rw [← L.map_comp]
    congr 1
    exact (MonoidalCategory.whisker_exchange η e.hom.val).symm
  letI : IsIso e.hom.val := by
    change IsIso ((SheafOfModules.forget X.ringCatSheaf).map e.hom)
    infer_instance
  letI : IsIso rightMap := by
    dsimp only [rightMap]
    change IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (𝟙 (L.obj P).val ⊗ₘ e.hom.val))
    infer_instance
  letI : IsIso leftMap := by
    dsimp only [leftMap]
    change IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (𝟙 P ⊗ₘ e.hom.val))
    infer_instance
  haveI : IsIso (leftMap ≫ moduleTensorSheafificationRightComparison P N') :=
    inferInstance
  exact IsIso.of_isIso_fac_right hfac

/-- The sheaf tensor product is symmetric. -/
def moduleTensorCommIso (M N : X.Modules) : moduleTensor M N ≅ moduleTensor N M := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  letI : SymmetricCategory X.PresheafOfModules :=
    PresheafOfModules.symmetricCategory (R := X.sheaf.obj)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (braiding M.val N.val)

/-- Maps from a sheaf tensor product are exactly maps from the underlying presheaf tensor
product into the underlying presheaf of the target sheaf. -/
def moduleTensorHomEquiv (M N P : X.Modules) :
    (moduleTensor M N ⟶ P) ≃ (moduleTensorPresheaf M N ⟶ P.val) :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)

/-- Precomposition by a tensor product map under the tensor universal property. -/
lemma moduleTensorHomEquiv_moduleTensorMap_comp
    {M M' N N' P : X.Modules} (a : M ⟶ M') (b : N ⟶ N')
    (h : moduleTensor M' N' ⟶ P) :
    moduleTensorHomEquiv M N P (moduleTensorMap a b ≫ h) =
      PresheafOfModules.Monoidal.tensorHom a.val b.val ≫
        moduleTensorHomEquiv M' N' P h := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  change adj.homEquiv _ _
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom a.val b.val) ≫ h) = _
  exact adj.homEquiv_naturality_left _ _

/-- Postcomposition under the tensor universal property. -/
lemma moduleTensorHomEquiv_comp
    {M N P Q : X.Modules} (h : moduleTensor M N ⟶ P) (k : P ⟶ Q) :
    moduleTensorHomEquiv M N Q (h ≫ k) =
      moduleTensorHomEquiv M N P h ≫ k.val := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  change adj.homEquiv _ _ (h ≫ k) = _
  exact adj.homEquiv_naturality_right _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- Tensoring module morphisms respects composition in both variables. -/
lemma moduleTensorMap_comp
    {M₁ M₂ M₃ N₁ N₂ N₃ : X.Modules}
    (a : M₁ ⟶ M₂) (a' : M₂ ⟶ M₃) (b : N₁ ⟶ N₂) (b' : N₂ ⟶ N₃) :
    moduleTensorMap a b ≫ moduleTensorMap a' b' =
      moduleTensorMap (a ≫ a') (b ≫ b') := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  dsimp [moduleTensorMap]
  rw [← Functor.map_comp]
  congr 1
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- Sheafifying the underlying presheaf of a module sheaf recovers the original sheaf. -/
def moduleSheafificationCounitIso (M : X.Modules) :
    (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).obj M.val ≅ M := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
  let _ : IsIso adj.counit := by
    dsimp only [adj]
    infer_instance
  exact
    { hom := adj.counit.app M
      inv := (inv adj.counit).app M
      hom_inv_id := congr_app (IsIso.hom_inv_id adj.counit) M
      inv_hom_id := congr_app (IsIso.inv_hom_id_assoc adj.counit (𝟙 _)) M }

/-- Tensor products carry isomorphisms in both variables to isomorphisms. -/
def moduleTensorMapIso {M M' N N' : X.Modules}
    (e : M ≅ M') (e' : N ≅ N') : moduleTensor M N ≅ moduleTensor M' N' := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (tensorIso ((SheafOfModules.forget X.ringCatSheaf).mapIso e)
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e'))

/-- Tensoring two isomorphisms of module sheaves gives an isomorphism. -/
lemma moduleTensorMap_isIso {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') [IsIso f] [IsIso g] :
    IsIso (moduleTensorMap f g) := by
  change IsIso (moduleTensorMapIso (asIso f) (asIso g)).hom
  infer_instance

/-- The structure sheaf is a left unit for the sheaf tensor product. -/
def moduleTensorLeftUnitIso (M : X.Modules) :
    moduleTensor (SheafOfModules.unit X.ringCatSheaf) M ≅ M := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  exact ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (leftUnitor M.val)).trans (moduleSheafificationCounitIso M)

/-- The structure sheaf is a right unit for the sheaf tensor product. -/
def moduleTensorRightUnitIso (M : X.Modules) :
    moduleTensor M (SheafOfModules.unit X.ringCatSheaf) ≅ M := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  exact ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (rightUnitor M.val)).trans (moduleSheafificationCounitIso M)

/-- A free module sheaf on one generator is the tensor unit. -/
def freePUnitIsoUnit (X : Scheme.{u}) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u, 0} PUnit) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  Limits.coproductUniqueIso _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- Tensoring the sheafification unit with the tensor unit becomes an isomorphism after
sheafification.  The proof is the left triangle identity for the sheafification adjunction,
conjugated by the presheaf and sheaf tensor unitors. -/
theorem moduleTensorSheafificationRightComparison_unit_isIso
    (P : X.PresheafOfModules) :
    IsIso (moduleTensorSheafificationRightComparison P
      (SheafOfModules.unit X.ringCatSheaf)) := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
  let η := adj.unit.app P
  have hnat : (η ⊗ₘ 𝟙 (SheafOfModules.unit X.ringCatSheaf).val) ≫
      (rightUnitor (L.obj P).val).hom =
      (rightUnitor P).hom ≫ η := rightUnitor_naturality η
  have hfac : moduleTensorSheafificationRightComparison P
      (SheafOfModules.unit X.ringCatSheaf) ≫
        (moduleTensorRightUnitIso (L.obj P)).hom =
      L.map (rightUnitor P).hom := by
    dsimp [moduleTensorSheafificationRightComparison,
      moduleTensorPresheafSheafification, moduleTensor,
      moduleTensorRightUnitIso, moduleSheafificationCounitIso]
    change L.map (η ⊗ₘ 𝟙 (SheafOfModules.unit X.ringCatSheaf).val) ≫
      L.map (rightUnitor (L.obj P).val).hom ≫
        adj.counit.app (L.obj P) = L.map (rightUnitor P).hom
    have hmaps : L.map (η ⊗ₘ 𝟙 (SheafOfModules.unit X.ringCatSheaf).val) ≫
        L.map (rightUnitor (L.obj P).val).hom =
        L.map (rightUnitor P).hom ≫ L.map η := by
      conv_lhs => rw [← L.map_comp]
      rw [hnat, L.map_comp]
    conv_lhs => rw [← Category.assoc]
    rw [hmaps, Category.assoc, adj.left_triangle_components, Category.comp_id]
  letI : IsIso (moduleTensorRightUnitIso (L.obj P)).hom :=
    (moduleTensorRightUnitIso (L.obj P)).isIso_hom
  letI : IsIso (L.map (rightUnitor P).hom) := by
    change IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (rightUnitor P).hom)
    infer_instance
  exact IsIso.of_isIso_fac_right hfac

/-- The comparison for tensoring a sheafification is an isomorphism when the sheaf factor is the
standard free rank-one module. -/
theorem moduleTensorSheafificationRightComparison_freePUnit_isIso
    (P : X.PresheafOfModules) :
    IsIso (moduleTensorSheafificationRightComparison P
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u, 0} PUnit))) := by
  let _ := moduleTensorSheafificationRightComparison_unit_isIso P
  exact moduleTensorSheafificationRightComparison_isIso_of_iso P (freePUnitIsoUnit X)

/-! ### Tensoring sheafifications by locally trivial rank-one factors -/

namespace TensorSheafificationComparison

/-! The rank-one calculation is valid on any site.  We use it below on the over-site of each
open subset in a trivializing cover. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- The underlying sheaf of rings of a sheaf of commutative rings. -/
abbrev ringSheaf (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

/-- Sheafification of the tensor of a module presheaf with a module sheaf on an arbitrary
site. -/
def tensorSheafification (R : Sheaf J CommRingCat.{u})
    (P : PresheafOfModules.{u} (ringSheaf R).obj)
    (N : SheafOfModules.{u} (ringSheaf R)) : SheafOfModules.{u} (ringSheaf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj
    (PresheafOfModules.Monoidal.tensorObj (R := R.obj) P N.val)

/-- The corresponding genuine sheaf tensor product on an arbitrary site. -/
def tensorSheaf (R : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules.{u} (ringSheaf R)) : SheafOfModules.{u} (ringSheaf R) :=
  tensorSheafification R M.val N

/-- The site-generic comparison induced by tensoring a sheafification unit with an identity. -/
def comparison (R : Sheaf J CommRingCat.{u})
    (P : PresheafOfModules.{u} (ringSheaf R).obj)
    (N : SheafOfModules.{u} (ringSheaf R)) :
    tensorSheafification R P N ⟶
      tensorSheaf R
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P) N := by
  letI : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
    PresheafOfModules.monoidalCategory (R := R.obj)
  exact (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf R).obj)).unit.app P) ⊗ₘ 𝟙 N.val)

/-- Sheafifying the underlying presheaf of a module sheaf recovers it, on an arbitrary site. -/
def counitIso (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (ringSheaf R)) :
    (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj M.val ≅ M := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  let _ : IsIso adj.counit := by
    dsimp only [adj]
    infer_instance
  exact
    { hom := adj.counit.app M
      inv := (inv adj.counit).app M
      hom_inv_id := congr_app (IsIso.hom_inv_id adj.counit) M
      inv_hom_id := congr_app (IsIso.inv_hom_id_assoc adj.counit (𝟙 _)) M }

/-- The tensor unit is a right unit for the site-generic sheaf tensor. -/
def rightUnitIso (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (ringSheaf R)) :
    tensorSheaf R M (SheafOfModules.unit (ringSheaf R)) ≅ M := by
  letI : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
    PresheafOfModules.monoidalCategory (R := R.obj)
  exact ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).mapIso
    (rightUnitor M.val)).trans (counitIso R M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- On an arbitrary site, the comparison is invertible when the sheaf factor is the tensor
unit. -/
theorem comparison_unit_isIso (R : Sheaf J CommRingCat.{u})
    (P : PresheafOfModules.{u} (ringSheaf R).obj) :
    IsIso (comparison R P (SheafOfModules.unit (ringSheaf R))) := by
  letI : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
    PresheafOfModules.monoidalCategory (R := R.obj)
  let L := PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  let η := adj.unit.app P
  have hnat : (η ⊗ₘ 𝟙 (SheafOfModules.unit (ringSheaf R)).val) ≫
      (rightUnitor (L.obj P).val).hom = (rightUnitor P).hom ≫ η :=
    rightUnitor_naturality η
  have hfac : comparison R P (SheafOfModules.unit (ringSheaf R)) ≫
        (rightUnitIso R (L.obj P)).hom = L.map (rightUnitor P).hom := by
    dsimp [comparison, tensorSheaf, tensorSheafification, rightUnitIso, counitIso]
    change L.map (η ⊗ₘ 𝟙 (SheafOfModules.unit (ringSheaf R)).val) ≫
      L.map (rightUnitor (L.obj P).val).hom ≫ adj.counit.app (L.obj P) =
        L.map (rightUnitor P).hom
    have hmaps : L.map (η ⊗ₘ 𝟙 (SheafOfModules.unit (ringSheaf R)).val) ≫
        L.map (rightUnitor (L.obj P).val).hom =
          L.map (rightUnitor P).hom ≫ L.map η := by
      conv_lhs => rw [← L.map_comp]
      rw [hnat, L.map_comp]
    conv_lhs => rw [← Category.assoc]
    rw [hmaps, Category.assoc, adj.left_triangle_components, Category.comp_id]
  letI : IsIso (rightUnitIso R (L.obj P)).hom := (rightUnitIso R (L.obj P)).isIso_hom
  letI : IsIso (L.map (rightUnitor P).hom) := by
    change IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringSheaf R).obj)).map (rightUnitor P).hom)
    infer_instance
  exact IsIso.of_isIso_fac_right hfac

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- The site-generic comparison is invariant under replacing its sheaf factor by an isomorphic
one. -/
theorem comparison_isIso_of_iso (R : Sheaf J CommRingCat.{u})
    (P : PresheafOfModules.{u} (ringSheaf R).obj)
    {N N' : SheafOfModules.{u} (ringSheaf R)} (e : N ≅ N')
    [IsIso (comparison R P N')] : IsIso (comparison R P N) := by
  letI : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
    PresheafOfModules.monoidalCategory (R := R.obj)
  let L := PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheaf R).obj)).unit.app P
  let rightMap := L.map (𝟙 (L.obj P).val ⊗ₘ e.hom.val)
  let leftMap := L.map (𝟙 P ⊗ₘ e.hom.val)
  have hfac : comparison R P N ≫ rightMap = leftMap ≫ comparison R P N' := by
    dsimp [comparison, tensorSheaf, tensorSheafification, rightMap, leftMap]
    change L.map (η ⊗ₘ 𝟙 N.val) ≫
      L.map (𝟙 (L.obj P).val ⊗ₘ e.hom.val) =
        L.map (𝟙 P ⊗ₘ e.hom.val) ≫ L.map (η ⊗ₘ 𝟙 N'.val)
    conv_lhs => rw [← L.map_comp]
    conv_rhs => rw [← L.map_comp]
    congr 1
    exact (MonoidalCategory.whisker_exchange η e.hom.val).symm
  letI : IsIso e.hom.val := by
    change IsIso ((SheafOfModules.forget (ringSheaf R)).map e.hom)
    infer_instance
  letI : IsIso rightMap := by
    dsimp only [rightMap, L]
    infer_instance
  letI : IsIso leftMap := by
    dsimp only [leftMap, L]
    infer_instance
  haveI : IsIso (leftMap ≫ comparison R P N') := inferInstance
  exact IsIso.of_isIso_fac_right hfac

/-- The standard free rank-one sheaf is the tensor unit on an arbitrary site. -/
def freePUnitIsoUnit (R : Sheaf J CommRingCat.{u}) :
    SheafOfModules.free (R := ringSheaf R) (ULift.{u, 0} PUnit) ≅
      SheafOfModules.unit (ringSheaf R) :=
  Limits.coproductUniqueIso _

/-- On an arbitrary site, the comparison is invertible for the standard free rank-one
factor. -/
theorem comparison_freePUnit_isIso (R : Sheaf J CommRingCat.{u})
    (P : PresheafOfModules.{u} (ringSheaf R).obj) :
    IsIso (comparison R P
      (SheafOfModules.free (R := ringSheaf R) (ULift.{u, 0} PUnit))) := by
  let _ := comparison_unit_isIso R P
  exact comparison_isIso_of_iso R P (freePUnitIsoUnit R)

end TensorSheafificationComparison

namespace TensorSheafificationComparison

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of sheafification with respect to a map of module presheaves on an open
over-site. -/
lemma sheafification_map_fac_over (U : X.Opens)
    {P Q : PresheafOfModules.{u} (X.ringCatSheaf.over U).obj} (f : P ⟶ Q) :
    CategoryTheory.toSheafify ((Opens.grothendieckTopology X).over U) P.presheaf ≫
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        ((PresheafOfModules.sheafification
          (𝟙 (X.ringCatSheaf.over U).obj)).map f).val =
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map f ≫
        CategoryTheory.toSheafify ((Opens.grothendieckTopology X).over U) Q.presheaf := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (X.ringCatSheaf.over U).obj)
  have h := adj.unit.naturality f
  have hm := congrArg
    (fun g ↦ (PresheafOfModules.toPresheaf
      (X.ringCatSheaf.over U).obj).map g) h
  dsimp only [adj] at hm
  exact hm.symm

/-- Restrict a morphism of module presheaves to an open over-site. -/
def presheafOverMap {P Q : X.PresheafOfModules} (f : P ⟶ Q) (U : X.Opens) :
    modulePresheafOver P U ⟶ modulePresheafOver Q U :=
  (PresheafOfModules.pushforward
    (F := Over.forget U) (𝟙 (X.ringCatSheaf.over U).obj)).map f

set_option maxHeartbeats 400000 in
-- Unfolding restriction of the global sheafification unit is elaboration-intensive.
/-- The restricted global sheafification unit is natural in the module presheaf. -/
lemma restrictedUnit_naturality
    {P Q : X.PresheafOfModules} (f : P ⟶ Q) (U : X.Opens) :
    moduleSheafificationRestrictedUnit P U ≫
        (((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map f).over U).val =
      presheafOverMap f U ≫ moduleSheafificationRestrictedUnit Q U := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let O := PresheafOfModules.pushforward
    (F := Over.forget U) (𝟙 (X.ringCatSheaf.over U).obj)
  have h := congrArg (fun g ↦ O.map g) (adj.unit.naturality f)
  exact h.symm

/-- Additive-presheaf form of `restrictedUnit_naturality`. -/
lemma restrictedUnit_naturality_additive
    {P Q : X.PresheafOfModules} (f : P ⟶ Q) (U : X.Opens) :
    (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (moduleSheafificationRestrictedUnit P U) ≫
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map f).over U).val =
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
          (presheafOverMap f U) ≫
        (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
          (moduleSheafificationRestrictedUnit Q U) := by
  have h := congrArg
    (fun g ↦ (PresheafOfModules.toPresheaf
      (X.ringCatSheaf.over U).obj).map g)
    (restrictedUnit_naturality f U)
  simpa only [Functor.map_comp] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Module-presheaf form of the factorization defining the comparison between local and global
sheafification. -/
lemma overComparison_fac_module (P : X.PresheafOfModules) (U : X.Opens) :
    (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).unit.app (modulePresheafOver P U) ≫
      (moduleSheafificationOverComparison P U).val =
        moduleSheafificationRestrictedUnit P U := by
  apply (PresheafOfModules.toPresheaf
    (X.ringCatSheaf.over U).obj).map_injective
  rw [Functor.map_comp,
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact moduleSheafificationOverComparison_fac P U

/-- The presheaf map whose sheafification is the global comparison. -/
def globalPresheafMap (P : X.PresheafOfModules) (N : X.Modules) :
    PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) P N.val ⟶
      PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).obj P).val N.val :=
  PresheafOfModules.Monoidal.tensorHom
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P) (𝟙 N.val)

/-- The analogous presheaf map after restriction to an open over-site. -/
def localPresheafMap (P : X.PresheafOfModules) (N : X.Modules) (U : X.Opens) :
    PresheafOfModules.Monoidal.tensorObj (R := (X.sheaf.over U).obj)
        (modulePresheafOver P U) (N.over U).val ⟶
      PresheafOfModules.Monoidal.tensorObj (R := (X.sheaf.over U).obj)
        ((PresheafOfModules.sheafification
          (𝟙 (X.ringCatSheaf.over U).obj)).obj (modulePresheafOver P U)).val
        (N.over U).val :=
  PresheafOfModules.Monoidal.tensorHom
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).unit.app (modulePresheafOver P U))
    (𝟙 (N.over U).val)

/-- The source of the comparison after local sheafification agrees with the restriction of its
global source. -/
def sourceOverIso (P : X.PresheafOfModules) (N : X.Modules) (U : X.Opens) :
    tensorSheafification (X.sheaf.over U) (modulePresheafOver P U) (N.over U) ≅
      (moduleTensorPresheafSheafification P N).over U := by
  let LU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let Q := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) P N.val
  letI : IsIso (moduleSheafificationOverComparison (X := X) Q U) :=
    moduleSheafificationOverComparison_isIso (X := X) Q U
  have hQ : IsIso (moduleSheafificationOverComparison (X := X) Q U) := inferInstance
  exact (LU.mapIso (modulePresheafOverTensorIso P N.val U).symm).trans
    (@asIso _ _ _ _ (moduleSheafificationOverComparison (X := X) Q U) hQ)

/-- Presheaf-level identification of the local and restricted global targets of the
comparison. -/
def targetOverPresheafIso
    (P : X.PresheafOfModules) (N : X.Modules) (U : X.Opens) :
    PresheafOfModules.Monoidal.tensorObj
        (R := (X.sheaf.over U).obj)
        ((PresheafOfModules.sheafification
          (𝟙 (X.ringCatSheaf.over U).obj)).obj (modulePresheafOver P U)).val
        (N.over U).val ≅
      modulePresheafOver
        (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
          ((PresheafOfModules.sheafification
            (𝟙 X.ringCatSheaf.obj)).obj P).val N.val) U := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let eP := moduleSheafificationOverIso P U
  let ePval := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso eP.symm
  letI : MonoidalCategory
      (PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  exact (tensorIso ePval (Iso.refl (N.over U).val)).trans
    (modulePresheafOverTensorIso (L.obj P).val N.val U).symm

set_option maxHeartbeats 1200000 in
-- Normalizing tensor maps across the two presentations of an open over-site is expensive.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- The presheaf map defining the comparison commutes with restriction to an open. -/
lemma presheafOver_naturality
    (P : X.PresheafOfModules) (N : X.Modules) (U : X.Opens) :
    localPresheafMap P N U ≫ (targetOverPresheafIso P N U).hom =
      (modulePresheafOverTensorIso P N.val U).inv ≫
        presheafOverMap (globalPresheafMap P N) U := by
  letI : MonoidalCategory
      (PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  rw [show (targetOverPresheafIso P N U).hom =
      (PresheafOfModules.Monoidal.tensorHom
        (moduleSheafificationOverComparison P U).val (𝟙 (N.over U).val)) ≫
      (modulePresheafOverTensorIso
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).obj P).val N.val U).inv from rfl]
  dsimp only [localPresheafMap, globalPresheafMap]
  rw [← Category.assoc]
  let A₀ := (PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)).obj (modulePresheafOver P U)
  let a : modulePresheafOver P U ⟶ A₀.val :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).unit.app (modulePresheafOver P U)
  let b : A₀.val ⟶
      (((PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).obj P).over U).val :=
    (moduleSheafificationOverComparison P U).val
  let k := 𝟙 (N.over U).val
  let ab : modulePresheafOver P U ⟶
      (((PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).obj P).over U).val := a ≫ b
  have htensor :
      PresheafOfModules.Monoidal.tensorHom
          (R := (X.sheaf.over U).obj) a k ≫
        PresheafOfModules.Monoidal.tensorHom
          (R := (X.sheaf.over U).obj) b k =
      PresheafOfModules.Monoidal.tensorHom
        (R := (X.sheaf.over U).obj) ab k := by
    ext A x
    exact congrArg (fun g ↦ g.hom x)
      (MonoidalCategory.tensorHom_comp_tensorHom
        (a.app A) (k.app A) (b.app A) (k.app A))
  change ((PresheafOfModules.Monoidal.tensorHom
      (R := (X.sheaf.over U).obj) a k ≫
      PresheafOfModules.Monoidal.tensorHom
        (R := (X.sheaf.over U).obj) b k) ≫ _) = _
  rw [htensor]
  dsimp only [ab, a, b]
  rw [overComparison_fac_module]
  rfl

/-- The target of the locally defined comparison agrees with the restriction of its global
target. -/
def targetOverIso (P : X.PresheafOfModules) (N : X.Modules) (U : X.Opens) :
    tensorSheaf (X.sheaf.over U)
        ((PresheafOfModules.sheafification
          (𝟙 (X.ringCatSheaf.over U).obj)).obj (modulePresheafOver P U))
        (N.over U) ≅
      (moduleTensor
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) N).over U := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let LU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let e := targetOverPresheafIso P N U
  let Q := PresheafOfModules.Monoidal.tensorObj
    (R := X.sheaf.obj) (L.obj P).val N.val
  letI : IsIso (moduleSheafificationOverComparison (X := X) Q U) :=
    moduleSheafificationOverComparison_isIso (X := X) Q U
  have hQ : IsIso (moduleSheafificationOverComparison (X := X) Q U) := inferInstance
  exact (LU.mapIso e).trans
    (@asIso _ _ _ _ (moduleSheafificationOverComparison (X := X) Q U) hQ)

set_option maxHeartbeats 1200000 in
-- Matching the restricted tensor presheaf with the global presentation is expensive.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Factorization of the source comparison isomorphism through the restricted global
sheafification unit. -/
lemma sourceOverIso_fac (P : X.PresheafOfModules) (N : X.Modules) (U : X.Opens) :
    CategoryTheory.toSheafify ((Opens.grothendieckTopology X).over U)
        (PresheafOfModules.Monoidal.tensorObj
          (R := (X.sheaf.over U).obj) (modulePresheafOver P U) (N.over U).val).presheaf ≫
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (sourceOverIso P N U).hom.val =
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
          (modulePresheafOverTensorIso P N.val U).inv ≫
        (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
          (moduleSheafificationRestrictedUnit
            (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) P N.val) U) := by
  let Q := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) P N.val
  let e : modulePresheafOver Q U ≅
      PresheafOfModules.Monoidal.tensorObj
        (R := (X.sheaf.over U).obj) (modulePresheafOver P U) (N.over U).val :=
    modulePresheafOverTensorIso P N.val U
  rw [show (sourceOverIso P N U).hom =
      (PresheafOfModules.sheafification
          (𝟙 (X.ringCatSheaf.over U).obj)).map e.inv ≫
        moduleSheafificationOverComparison Q U from rfl]
  rw [SheafOfModules.comp_val, Functor.map_comp, ← Category.assoc]
  have hmap := sheafification_map_fac_over U e.inv
  rw [hmap]
  rw [Category.assoc]
  erw [moduleSheafificationOverComparison_fac]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Factorization of the site-generic comparison on an open over-site. -/
lemma comparison_over_fac (P : X.PresheafOfModules) (N : X.Modules) (U : X.Opens) :
    CategoryTheory.toSheafify ((Opens.grothendieckTopology X).over U)
        (PresheafOfModules.Monoidal.tensorObj
          (R := (X.sheaf.over U).obj) (modulePresheafOver P U) (N.over U).val).presheaf ≫
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (comparison (X.sheaf.over U) (modulePresheafOver P U) (N.over U)).val =
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (PresheafOfModules.Monoidal.tensorHom
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (X.ringCatSheaf.over U).obj)).unit.app (modulePresheafOver P U))
            (𝟙 (N.over U).val) ≫
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 (X.ringCatSheaf.over U).obj)).unit.app
              (PresheafOfModules.Monoidal.tensorObj
                (R := (X.sheaf.over U).obj)
                ((PresheafOfModules.sheafification
                  (𝟙 (X.ringCatSheaf.over U).obj)).obj
                    (modulePresheafOver P U)).val (N.over U).val)) := by
  exact sheafification_map_fac_over U _

set_option maxHeartbeats 1200000 in
-- Matching the target tensor presheaf with its restricted global presentation is expensive.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Factorization of the target comparison isomorphism through the restricted global
sheafification unit. -/
lemma targetOverIso_fac (P : X.PresheafOfModules) (N : X.Modules) (U : X.Opens) :
    CategoryTheory.toSheafify ((Opens.grothendieckTopology X).over U)
        (PresheafOfModules.Monoidal.tensorObj
          (R := (X.sheaf.over U).obj)
          ((PresheafOfModules.sheafification
            (𝟙 (X.ringCatSheaf.over U).obj)).obj (modulePresheafOver P U)).val
          (N.over U).val).presheaf ≫
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (targetOverIso P N U).hom.val =
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
          (targetOverPresheafIso P N U).hom ≫
        (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
          (moduleSheafificationRestrictedUnit
            (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
              ((PresheafOfModules.sheafification
                (𝟙 X.ringCatSheaf.obj)).obj P).val N.val) U) := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let e := targetOverPresheafIso P N U
  let Q := PresheafOfModules.Monoidal.tensorObj
    (R := X.sheaf.obj) (L.obj P).val N.val
  rw [show (targetOverIso P N U).hom =
      (PresheafOfModules.sheafification
          (𝟙 (X.ringCatSheaf.over U).obj)).map e.hom ≫
        moduleSheafificationOverComparison Q U from rfl]
  rw [SheafOfModules.comp_val, Functor.map_comp, ← Category.assoc]
  have hmap := sheafification_map_fac_over U e.hom
  rw [hmap]
  rw [Category.assoc]
  erw [moduleSheafificationOverComparison_fac]

set_option maxHeartbeats 1200000 in
-- The coherence square unfolds both local and global sheafification adjunctions.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting the global comparison to an open agrees with the site-generic comparison formed
on that open. -/
lemma comparison_over_naturality (P : X.PresheafOfModules) (N : X.Modules)
    (U : X.Opens) :
    comparison (X.sheaf.over U) (modulePresheafOver P U) (N.over U) ≫
        (targetOverIso P N U).hom =
      (sourceOverIso P N U).hom ≫
        (moduleTensorSheafificationRightComparison P N).over U := by
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (X.ringCatSheaf.over U).obj)).injective
  apply (PresheafOfModules.toPresheaf
    (X.ringCatSheaf.over U).obj).map_injective
  erw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def,
    PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  rw [SheafOfModules.comp_val, SheafOfModules.comp_val,
    Functor.map_comp, Functor.map_comp]
  rw [← Category.assoc]
  have hlocal := comparison_over_fac P N U
  rw [hlocal]
  rw [Functor.map_comp, Category.assoc]
  erw [targetOverIso_fac]
  rw [← Category.assoc]
  have hsource := sourceOverIso_fac P N U
  conv_rhs =>
    rw [← Category.assoc, hsource]
  rw [Category.assoc]
  let f : PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) P N.val ⟶
      PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).obj P).val N.val :=
    PresheafOfModules.Monoidal.tensorHom
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P) (𝟙 N.val)
  have hglobal := restrictedUnit_naturality_additive f U
  rw [show (moduleTensorSheafificationRightComparison P N).over U =
      ((PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map f).over U from rfl]
  conv_rhs =>
    rw [Category.assoc, hglobal]
  have hsquare := congrArg
    (fun g ↦ (PresheafOfModules.toPresheaf
      (X.ringCatSheaf.over U).obj).map g)
    (presheafOver_naturality P N U)
  simp only [Functor.map_comp] at hsquare
  dsimp only [localPresheafMap, globalPresheafMap, f] at hsquare ⊢
  rw [← Category.assoc, hsquare, Category.assoc]

end TensorSheafificationComparison

/-- The tensor product of two globally trivial rank-one module sheaves is globally trivial. -/
def moduleTensorFreePUnitIso (X : Scheme.{u}) :
    moduleTensor
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u, 0} PUnit))
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u, 0} PUnit)) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u, 0} PUnit) :=
  moduleTensorMapIso (freePUnitIsoUnit X) (freePUnitIsoUnit X) ≪≫
    moduleTensorLeftUnitIso (SheafOfModules.unit X.ringCatSheaf) ≪≫
      (freePUnitIsoUnit X).symm

/-- In particular, tensoring the two standard trivial line modules remains invertible. -/
theorem moduleTensor_free_punit_isInvertible (X : Scheme.{u}) :
    IsInvertible (moduleTensor
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u, 0} PUnit))
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u, 0} PUnit))) :=
  IsInvertible.of_iso (moduleTensorFreePUnitIso X).symm (IsInvertible.free_punit X)

/-! ### Tensor products of locally trivial rank-one sheaves -/

/-- Restrict a local free presentation to a smaller open subset. -/
def restrictLocalGeneratorsIso {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData]
    (i : q.I) {W : X.Opens} (f : W ⟶ q.X i) :
    SheafOfModules.free (R := X.ringCatSheaf.over W) (q.generators i).I ≅ M.over W := by
  letI : IsIso (q.generators i).π :=
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso i
  exact SheafOfModules.mapFreeIso
      (SheafOfModules.overMap X.ringCatSheaf f) (q.generators i).I
      (SheafOfModules.overMapUnitIso f).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf f).mapIso
      (asIso (q.generators i).π) ≪≫
    (SheafOfModules.overFunctorMap X.ringCatSheaf f).app M

/-- Equivalent basis types give isomorphic free module sheaves on an open subset. -/
def freeOverEquivIso {U : X.Opens} {I J : Type u} (e : I ≃ J) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) J :=
  (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over U)).mapIso e.toIso

/-- An isomorphism from a free sheaf determines a family of generating sections. -/
def generatingSectionsOfFreeIso {U : X.Opens}
    {M : SheafOfModules.{u} (X.ringCatSheaf.over U)} {I : Type u}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M) :
    M.GeneratingSections where
  I := I
  s := M.freeHomEquiv e.hom
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

/-- The projection associated to generators obtained from a free isomorphism is that
isomorphism itself. -/
@[simp]
lemma generatingSectionsOfFreeIso_π {U : X.Opens}
    {M : SheafOfModules.{u} (X.ringCatSheaf.over U)} {I : Type u}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M) :
    (generatingSectionsOfFreeIso e).π = e.hom :=
  Equiv.symm_apply_apply _ _

/-- Tensor products on an over-site carry isomorphisms in both variables to isomorphisms. -/
def moduleTensorOverMapIso {U : X.Opens}
    {M M' N N' : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    (e : M ≅ M') (e' : N ≅ N') :
    moduleTensorOver U M N ≅ moduleTensorOver U M' N' := by
  letI : MonoidalCategory (PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  exact (PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)).mapIso
      (tensorIso ((SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso e)
        ((SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso e'))

/-- Sheafifying the underlying module presheaf on an over-site recovers the module sheaf. -/
def moduleSheafificationCounitOverIso {U : X.Opens}
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) :
    (PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over U).obj)).obj M.val ≅ M := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf.over U) (𝟙 (X.ringCatSheaf.over U).obj)
  let _ : IsIso adj.counit := by
    dsimp only [adj]
    infer_instance
  exact
    { hom := adj.counit.app M
      inv := (inv adj.counit).app M
      hom_inv_id := congr_app (IsIso.hom_inv_id adj.counit) M
      inv_hom_id := congr_app (IsIso.inv_hom_id_assoc adj.counit (𝟙 _)) M }

/-- The structure sheaf is a left unit for tensor product on an over-site. -/
def moduleTensorOverLeftUnitIso {U : X.Opens}
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) :
    moduleTensorOver U (SheafOfModules.unit (X.ringCatSheaf.over U)) M ≅ M := by
  letI : MonoidalCategory (PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  exact ((PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)).mapIso (leftUnitor M.val)).trans
      (moduleSheafificationCounitOverIso M)

/-- The free rank-one module sheaf on an over-site is its tensor unit. -/
def freePUnitOverIsoUnit (U : X.Opens) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} PUnit) ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) :=
  Limits.coproductUniqueIso _

/-- The tensor of two free rank-one module sheaves on an open subset is free of rank one. -/
def moduleTensorOverFreePUnitIso (U : X.Opens) :
    moduleTensorOver U
        (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} PUnit))
        (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} PUnit)) ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} PUnit) :=
  moduleTensorOverMapIso (freePUnitOverIsoUnit U) (freePUnitOverIsoUnit U) ≪≫
    moduleTensorOverLeftUnitIso (SheafOfModules.unit (X.ringCatSheaf.over U)) ≪≫
      (freePUnitOverIsoUnit U).symm

/-- On the intersection of two rank-one trivializing opens, the tensor product is free of rank
one. -/
def tensorLocalIso {M N : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData]
    (hq : ∀ i, Nonempty ((q.generators i).I ≃ ULift.{u, 0} PUnit))
    (r : SheafOfModules.LocalGeneratorsData.{u} N) [r.IsLocallyFreeData]
    (hr : ∀ i, Nonempty ((r.generators i).I ≃ ULift.{u, 0} PUnit))
    (i : q.I) (j : r.I) :
    SheafOfModules.free
        (R := X.ringCatSheaf.over (q.X i ⊓ r.X j)) (ULift.{u, 0} PUnit) ≅
      (moduleTensor M N).over (q.X i ⊓ r.X j) := by
  let eM : SheafOfModules.free
      (R := X.ringCatSheaf.over (q.X i ⊓ r.X j)) (ULift.{u, 0} PUnit) ≅
      M.over (q.X i ⊓ r.X j) :=
    freeOverEquivIso (hq i).some.symm ≪≫
      restrictLocalGeneratorsIso q i (homOfLE inf_le_left)
  let eN : SheafOfModules.free
      (R := X.ringCatSheaf.over (q.X i ⊓ r.X j)) (ULift.{u, 0} PUnit) ≅
      N.over (q.X i ⊓ r.X j) :=
    freeOverEquivIso (hr j).some.symm ≪≫
      restrictLocalGeneratorsIso r j (homOfLE inf_le_right)
  exact (moduleTensorOverFreePUnitIso (q.X i ⊓ r.X j)).symm ≪≫
    moduleTensorOverMapIso eM eN ≪≫
      (moduleTensorOverIso M N (q.X i ⊓ r.X j)).symm

/-- Local generator data built from a cover carrying explicit free rank-one isomorphisms. -/
def localGeneratorsDataOfFreePUnitIso {M : X.Modules} {ι : Type u}
    (Y : ι → X.Opens) (hY : (Opens.grothendieckTopology X).CoversTop Y)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (Y i))
      (ULift.{u, 0} PUnit) ≅ M.over (Y i)) :
    SheafOfModules.LocalGeneratorsData.{u} M where
  I := ι
  X := Y
  coversTop := hY
  generators i := generatingSectionsOfFreeIso (e i)

/-- The generator projection in `localGeneratorsDataOfFreePUnitIso` is the supplied local
trivialization. -/
@[simp]
lemma localGeneratorsDataOfFreePUnitIso_generators_π {M : X.Modules} {ι : Type u}
    (Y : ι → X.Opens) (hY : (Opens.grothendieckTopology X).CoversTop Y)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (Y i))
      (ULift.{u, 0} PUnit) ≅ M.over (Y i)) (i : ι) :
    ((localGeneratorsDataOfFreePUnitIso Y hY e).generators i).π = (e i).hom :=
  Equiv.symm_apply_apply _ _

namespace HasRankOneTrivialization

/-- A covering by explicit free rank-one module sheaves gives a rank-one trivialization. -/
theorem of_freePUnitIso {M : X.Modules} {ι : Type u}
    (Y : ι → X.Opens) (hY : (Opens.grothendieckTopology X).CoversTop Y)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (Y i))
      (ULift.{u, 0} PUnit) ≅ M.over (Y i)) : HasRankOneTrivialization M := by
  let q := localGeneratorsDataOfFreePUnitIso Y hY e
  have hfree : q.IsLocallyFreeData := by
    constructor
    intro i
    change IsIso (generatingSectionsOfFreeIso (e i)).π
    rw [generatingSectionsOfFreeIso_π]
    exact (e i).isIso_hom
  refine ⟨q, hfree, ?_⟩
  intro i
  exact ⟨Equiv.refl (ULift.{u, 0} PUnit)⟩

end HasRankOneTrivialization

/-- Pairwise intersections of two open covers again cover the whole space. -/
lemma intersections_coversTop {ι κ : Type u}
    (Y : ι → X.Opens) (Z : κ → X.Opens)
    (hY : (Opens.grothendieckTopology X).CoversTop Y)
    (hZ : (Opens.grothendieckTopology X).CoversTop Z) :
    (Opens.grothendieckTopology X).CoversTop (fun ij : ι × κ ↦ Y ij.1 ⊓ Z ij.2) := by
  rw [Opens.coversTop_iff]
  have hYtop : iSup Y = ⊤ := (Opens.coversTop_iff X Y).mp hY
  have hZtop : iSup Z = ⊤ := (Opens.coversTop_iff X Z).mp hZ
  rw [TopologicalSpace.IsOpenCover, iSup_prod]
  calc
    (⨆ i, ⨆ j, Y i ⊓ Z j) = ⨆ i, Y i ⊓ (⨆ j, Z j) := by
      congr 1
      funext i
      rw [inf_comm, iSup_inf_eq]
      simp only [inf_comm]
    _ = (⨆ i, Y i) ⊓ (⨆ j, Z j) := iSup_inf_eq _ _ |>.symm
    _ = ⊤ := by rw [hYtop, hZtop]; simp

namespace HasRankOneTrivialization

set_option linter.style.haveILetI false in
/-- The genuine sheaf tensor product preserves rank-one local triviality. -/
theorem tensor {M N : X.Modules}
    (hM : HasRankOneTrivialization M) (hN : HasRankOneTrivialization N) :
    HasRankOneTrivialization (moduleTensor M N) := by
  obtain ⟨q, hqfree, hqrank⟩ := hM
  obtain ⟨r, hrfree, hrrank⟩ := hN
  letI : q.IsLocallyFreeData := hqfree
  letI : r.IsLocallyFreeData := hrfree
  exact of_freePUnitIso
    (fun ij : q.I × r.I ↦ q.X ij.1 ⊓ r.X ij.2)
    (intersections_coversTop q.X r.X q.coversTop r.coversTop)
    (fun ij ↦ tensorLocalIso q hqrank r hrrank ij.1 ij.2)

end HasRankOneTrivialization

set_option maxHeartbeats 1200000 in
-- Localizing the comparison over every member of the trivializing cover is expensive.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- Sheafification commutes with tensoring on the right by a module with a rank-one local
trivialization. -/
theorem moduleTensorSheafificationRightComparison_isIso_of_hasRankOneTrivialization
    (P : X.PresheafOfModules) {N : X.Modules}
    (hN : HasRankOneTrivialization N) :
    IsIso (moduleTensorSheafificationRightComparison P N) := by
  obtain ⟨q, hqfree, hqrank⟩ := hN
  letI : q.IsLocallyFreeData := hqfree
  apply moduleHom_isIso_of_coversTop _ q.X q.coversTop
  intro i
  let eFree : SheafOfModules.free
      (R := X.ringCatSheaf.over (q.X i)) (ULift.{u, 0} PUnit) ≅
      N.over (q.X i) :=
    (freeOverEquivIso (hqrank i).some.symm).trans
      (restrictLocalGeneratorsIso q i (homOfLE le_rfl))
  let _ : IsIso (TensorSheafificationComparison.comparison
      (X.sheaf.over (q.X i)) (modulePresheafOver P (q.X i))
      (SheafOfModules.free (R := X.ringCatSheaf.over (q.X i))
        (ULift.{u, 0} PUnit))) :=
    TensorSheafificationComparison.comparison_freePUnit_isIso _ _
  letI : IsIso (TensorSheafificationComparison.comparison
      (X.sheaf.over (q.X i)) (modulePresheafOver P (q.X i)) (N.over (q.X i))) :=
    TensorSheafificationComparison.comparison_isIso_of_iso _ _ eFree.symm
  exact IsIso.of_isIso_fac_left
    (TensorSheafificationComparison.comparison_over_naturality
      P N (q.X i)).symm

/-- Sheafification commutes with tensoring on the right by any invertible module sheaf. -/
theorem moduleTensorSheafificationRightComparison_isIso_of_isInvertible
    (P : X.PresheafOfModules) {N : X.Modules} (hN : IsInvertible N) :
    IsIso (moduleTensorSheafificationRightComparison P N) := by
  obtain ⟨A, hA, ⟨e⟩⟩ := hN
  let _ :=
    moduleTensorSheafificationRightComparison_isIso_of_hasRankOneTrivialization P hA
  exact moduleTensorSheafificationRightComparison_isIso_of_iso P e

namespace IsInvertible

/-- The genuine sheaf tensor product of two invertible module sheaves is invertible. -/
theorem tensor {M N : X.Modules} (hM : IsInvertible M) (hN : IsInvertible N) :
    IsInvertible (moduleTensor M N) := by
  obtain ⟨A, hA, ⟨eM⟩⟩ := hM
  obtain ⟨B, hB, ⟨eN⟩⟩ := hN
  exact ⟨moduleTensor A B, HasRankOneTrivialization.tensor hA hB,
    ⟨moduleTensorMapIso eM eN⟩⟩

end IsInvertible

/-! ### Tensor products and arbitrary scheme pullback -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The objectwise restriction-of-scalars map from the tensor of two pushed-forward module
presheaves to the pushforward of their tensor. -/
def schemePresheafPushforwardTensorMap (f : Y ⟶ X)
    (M N : Y.PresheafOfModules) :
    PresheafOfModules.Monoidal.tensorObj
        ((PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj M)
        ((PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj N) ⟶
      (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
        (PresheafOfModules.Monoidal.tensorObj M N) where
  app U := Functor.LaxMonoidal.μ
    (ModuleCat.restrictScalars (f.toRingCatSheafHom.hom.app U).hom)
      (M.obj _) (N.obj _)
  naturality {U V} g := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    dsimp
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
    erw [ModuleCat.restrictScalars_μ_tmul]
    erw [ModuleCat.restrictScalars_μ_tmul]
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the presheaf pushforward tensor map. -/
lemma schemePresheafPushforwardTensorMap_naturality (f : Y ⟶ X)
    {M M' N N' : Y.PresheafOfModules} (a : M ⟶ M') (b : N ⟶ N') :
    PresheafOfModules.Monoidal.tensorHom
        ((PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map a)
        ((PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map b) ≫
      schemePresheafPushforwardTensorMap f M' N' =
    schemePresheafPushforwardTensorMap f M N ≫
      (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
        (PresheafOfModules.Monoidal.tensorHom a b) := by
  ext1 U
  exact Functor.LaxMonoidal.μ_natural
    (ModuleCat.restrictScalars (f.toRingCatSheafHom.hom.app U).hom)
      (a.app _) (b.app _)

/-- The unit from the raw objectwise tensor presheaf to the genuine sheaf tensor product. -/
def moduleTensorUnit (M N : X.Modules) :
    moduleTensorPresheaf M N ⟶ (moduleTensor M N).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (moduleTensorPresheaf M N)

/-- Naturality of the unit from objectwise tensor to genuine sheaf tensor. -/
lemma moduleTensorUnit_naturality
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    PresheafOfModules.Monoidal.tensorHom a.val b.val ≫
        moduleTensorUnit M' N' =
      moduleTensorUnit M N ≫ (moduleTensorMap a b).val := by
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (PresheafOfModules.Monoidal.tensorHom a.val b.val)

set_option maxHeartbeats 800000 in
-- Elaborating the composite through presheaf pushforward unfolds several module structures.
/-- The presheaf map underlying the lax tensor comparison for module pushforward. -/
def modulePushforwardTensorPresheafMap (f : Y ⟶ X) (M N : Y.Modules) :
    moduleTensorPresheaf ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N) ⟶
      ((Scheme.Modules.pushforward f).obj (moduleTensor M N)).val :=
  schemePresheafPushforwardTensorMap f M.val N.val ≫
    (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
      (moduleTensorUnit M N)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the presheaf map underlying the pushforward tensor comparison. -/
lemma modulePushforwardTensorPresheafMap_naturality (f : Y ⟶ X)
    {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    PresheafOfModules.Monoidal.tensorHom
        ((Scheme.Modules.pushforward f).map a).val
        ((Scheme.Modules.pushforward f).map b).val ≫
      modulePushforwardTensorPresheafMap f M' N' =
    modulePushforwardTensorPresheafMap f M N ≫
      ((Scheme.Modules.pushforward f).map (moduleTensorMap a b)).val := by
  dsimp [modulePushforwardTensorPresheafMap]
  change
    (PresheafOfModules.Monoidal.tensorHom
          ((PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map a.val)
          ((PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map b.val) ≫
        schemePresheafPushforwardTensorMap f M'.val N'.val) ≫
      (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
        (moduleTensorUnit M' N') = _
  rw [schemePresheafPushforwardTensorMap_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [moduleTensorUnit_naturality, Functor.map_comp]
  rfl

set_option maxHeartbeats 800000 in
-- The tensor universal property unfolds both the sheafification and pushforward adjunctions.
/-- The canonical lax tensor comparison for module pushforward. -/
def modulePushforwardTensorMap (f : Y ⟶ X) (M N : Y.Modules) :
    moduleTensor ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward f).obj (moduleTensor M N) :=
  (moduleTensorHomEquiv _ _ _).symm
    (modulePushforwardTensorPresheafMap f M N)

/-- Naturality of the canonical tensor comparison for module pushforward. -/
lemma modulePushforwardTensorMap_naturality (f : Y ⟶ X)
    {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    moduleTensorMap ((Scheme.Modules.pushforward f).map a)
        ((Scheme.Modules.pushforward f).map b) ≫
      modulePushforwardTensorMap f M' N' =
    modulePushforwardTensorMap f M N ≫
      (Scheme.Modules.pushforward f).map (moduleTensorMap a b) := by
  apply (moduleTensorHomEquiv _ _ _).injective
  rw [moduleTensorHomEquiv_moduleTensorMap_comp, moduleTensorHomEquiv_comp]
  simp only [modulePushforwardTensorMap, Equiv.apply_symm_apply]
  change
    PresheafOfModules.Monoidal.tensorHom
        ((Scheme.Modules.pushforward f).map a).val
        ((Scheme.Modules.pushforward f).map b).val ≫
      modulePushforwardTensorPresheafMap f M' N' =
    modulePushforwardTensorPresheafMap f M N ≫
      ((Scheme.Modules.pushforward f).map (moduleTensorMap a b)).val
  exact modulePushforwardTensorPresheafMap_naturality f a b

/-- The adjoint of the canonical tensor comparison for module pullback. -/
def modulePullbackTensorAdjointMap (f : Y ⟶ X) (M N : X.Modules) :
    moduleTensor M N ⟶
      (Scheme.Modules.pushforward f).obj
        (moduleTensor ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N)) :=
  moduleTensorMap
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
    modulePushforwardTensorMap f
      ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)

set_option maxHeartbeats 800000 in
-- Elaborating the adjoint tensor map traverses the scheme-module adjunction twice.
/-- The canonical oplax tensor comparison for module pullback. -/
def modulePullbackTensorMap (f : Y ⟶ X) (M N : X.Modules) :
    (Scheme.Modules.pullback f).obj (moduleTensor M N) ⟶
      moduleTensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (modulePullbackTensorAdjointMap f M N)

/-- Naturality of the adjoint form of the pullback tensor comparison. -/
lemma modulePullbackTensorAdjointMap_naturality (f : Y ⟶ X)
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    moduleTensorMap a b ≫ modulePullbackTensorAdjointMap f M' N' =
      modulePullbackTensorAdjointMap f M N ≫
        (Scheme.Modules.pushforward f).map
          (moduleTensorMap ((Scheme.Modules.pullback f).map a)
            ((Scheme.Modules.pullback f).map b)) := by
  dsimp [modulePullbackTensorAdjointMap]
  rw [← Category.assoc, moduleTensorMap_comp]
  have ha := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a
  have hb := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality b
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at ha hb
  rw [ha, hb]
  rw [← moduleTensorMap_comp, Category.assoc,
    modulePushforwardTensorMap_naturality]
  exact (Category.assoc _ _ _).symm

/-- The canonical pullback tensor comparison is natural in both module variables. -/
lemma modulePullbackTensorMap_naturality (f : Y ⟶ X)
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (moduleTensorMap a b) ≫
        modulePullbackTensorMap f M' N' =
      modulePullbackTensorMap f M N ≫
        moduleTensorMap ((Scheme.Modules.pullback f).map a)
          ((Scheme.Modules.pullback f).map b) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  dsimp only [modulePullbackTensorMap, adj]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact modulePullbackTensorAdjointMap_naturality f a b

/-! ### The pullback tensor comparison for open immersions -/

/-- The adjoint tensor comparison for restriction to an open subscheme. -/
def moduleRestrictTensorAdjointMap (U : X.Opens) (M N : X.Modules) :
    moduleTensor M N ⟶
      (Scheme.Modules.pushforward U.ι).obj
        (moduleTensor
          ((Scheme.Modules.restrictFunctor U.ι).obj M)
          ((Scheme.Modules.restrictFunctor U.ι).obj N)) :=
  moduleTensorMap
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app N) ≫
    modulePushforwardTensorMap U.ι
      ((Scheme.Modules.restrictFunctor U.ι).obj M)
      ((Scheme.Modules.restrictFunctor U.ι).obj N)

/-- The oplax tensor comparison induced by the restriction-pushforward adjunction. -/
def moduleRestrictTensorMap (U : X.Opens) (M N : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj (moduleTensor M N) ⟶
      moduleTensor
        ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N) :=
  ((Scheme.Modules.restrictAdjunction U.ι).homEquiv _ _).symm
    (moduleRestrictTensorAdjointMap U M N)

set_option maxHeartbeats 800000 in
-- The mate calculation traverses both left adjoints of open-immersion pushforward.
set_option linter.style.haveILetI false in
/-- Transporting the restriction tensor map across the canonical uniqueness isomorphism of
left adjoints gives the pullback tensor map. -/
lemma modulePullbackTensorMap_open_eq (U : X.Opens) (M N : X.Modules) :
    modulePullbackTensorMap U.ι M N =
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app (moduleTensor M N) ≫
        moduleRestrictTensorMap U M N ≫
          moduleTensorMap
            ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M)
            ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app N) := by
  let adjR := Scheme.Modules.restrictAdjunction U.ι
  let adjP := Scheme.Modules.pullbackPushforwardAdjunction U.ι
  let e := Scheme.Modules.restrictFunctorIsoPullback U.ι
  apply (adjP.homEquiv _ _).injective
  rw [adjP.homEquiv_naturality_right]
  rw [Functor.map_comp]
  dsimp only [modulePullbackTensorMap, moduleRestrictTensorMap, adjP]
  rw [Equiv.apply_symm_apply]
  change modulePullbackTensorAdjointMap U.ι M N =
    adjP.homEquiv _ _ (e.inv.app (moduleTensor M N)) ≫
      (Scheme.Modules.pushforward U.ι).map
        (moduleRestrictTensorMap U M N) ≫
      (Scheme.Modules.pushforward U.ι).map
        (moduleTensorMap (e.hom.app M) (e.hom.app N))
  dsimp only [e, Scheme.Modules.restrictFunctorIsoPullback]
  rw [Adjunction.leftAdjointUniq_inv_app]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change modulePullbackTensorAdjointMap U.ι M N =
    adjR.unit.app (moduleTensor M N) ≫
      (Scheme.Modules.pushforward U.ι).map
        (moduleRestrictTensorMap U M N) ≫
      (Scheme.Modules.pushforward U.ι).map
        (moduleTensorMap (e.hom.app M) (e.hom.app N))
  rw [← Category.assoc]
  rw [← adjR.homEquiv_apply (moduleTensor M N) _
    (moduleRestrictTensorMap U M N)]
  dsimp only [moduleRestrictTensorMap]
  rw [Equiv.apply_symm_apply]
  dsimp only [moduleRestrictTensorAdjointMap]
  rw [Category.assoc]
  rw [← modulePushforwardTensorMap_naturality]
  rw [← Category.assoc, moduleTensorMap_comp]
  dsimp only [modulePullbackTensorAdjointMap]
  dsimp only [e, Scheme.Modules.restrictFunctorIsoPullback]
  rw [Adjunction.unit_leftAdjointUniq_hom_app adjR adjP]
  rw [Adjunction.unit_leftAdjointUniq_hom_app adjR adjP]

/-- The restriction tensor comparison has the defining factorization through the tensor
sheafification unit. -/
lemma moduleTensorRestrictComparison_unit (U : X.Opens) (M N : X.Modules) :
    moduleTensorUnit
        ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N) ≫
      (moduleTensorRestrictComparison U M N).val =
    moduleTensorRestrictUnit U M N := by
  change moduleTensorHomEquiv
      ((Scheme.Modules.restrictFunctor U.ι).obj M)
      ((Scheme.Modules.restrictFunctor U.ι).obj N)
      ((Scheme.Modules.restrictFunctor U.ι).obj (moduleTensor M N))
      (moduleTensorRestrictComparison U M N) = _
  exact (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).apply_symm_apply _

set_option maxHeartbeats 800000 in
-- Evaluating the two restriction-of-scalars tensor maps requires all transported ring instances.
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private lemma moduleRestrictTensorPresheaf_fac
    (U : X.Opens) (M N : X.Modules) :
    PresheafOfModules.Monoidal.tensorHom
        ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val
        ((Scheme.Modules.restrictAdjunction U.ι).unit.app N).val ≫
      schemePresheafPushforwardTensorMap U.ι
        ((Scheme.Modules.restrictFunctor U.ι).obj M).val
        ((Scheme.Modules.restrictFunctor U.ι).obj N).val ≫
      (PresheafOfModules.pushforward U.ι.toRingCatSheafHom.hom).map
        (moduleTensorRestrictUnit U M N) =
    moduleTensorUnit M N ≫
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app
        (moduleTensor M N)).val := by
  ext1 V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  letI : CommRing (X.ringCatSheaf.obj.obj V) :=
    inferInstanceAs (CommRing (X.sheaf.obj.obj V))
  let W := (Opens.map U.ι.base).op.obj V
  letI : CommRing ((U : Scheme.{u}).ringCatSheaf.obj.obj W) :=
    inferInstanceAs (CommRing ((U : Scheme.{u}).sheaf.obj.obj W))
  let Z := U.ι.opensFunctor.op.obj W
  letI : CommRing ((U.ι.opensFunctor.op ⋙ X.ringCatSheaf.obj).obj W) :=
    inferInstanceAs (CommRing (X.sheaf.obj.obj Z))
  letI : CommRing ↑(
      (((Opens.map U.ι.base).sheafPushforwardContinuous
        RingCat (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (U : Scheme.{u}))).obj
            (U : Scheme.{u}).ringCatSheaf).obj.obj V) :=
    inferInstanceAs (CommRing ((U : Scheme.{u}).sheaf.obj.obj W))
  change
    ((PresheafOfModules.pushforward U.ι.toRingCatSheafHom.hom).map
        (moduleTensorRestrictUnit U M N)).app V
      ((schemePresheafPushforwardTensorMap U.ι
          ((Scheme.Modules.restrictFunctor U.ι).obj M).val
          ((Scheme.Modules.restrictFunctor U.ι).obj N).val).app V
        ((PresheafOfModules.Monoidal.tensorHom
            ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val
            ((Scheme.Modules.restrictAdjunction U.ι).unit.app N).val).app V
          (m ⊗ₜ[X.sheaf.obj.obj V] n))) =
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app
        (moduleTensor M N)).val.app V
        ((moduleTensorUnit M N).app V (m ⊗ₜ[X.sheaf.obj.obj V] n))
  let unitM := (Scheme.Modules.restrictAdjunction U.ι).unit.app M
  let unitN := (Scheme.Modules.restrictAdjunction U.ι).unit.app N
  have hTensor := ModuleCat.MonoidalCategory.tensorHom_tmul
    (unitM.val.app V) (unitN.val.app V) m n
  change (PresheafOfModules.Monoidal.tensorHom unitM.val unitN.val).app V
      (m ⊗ₜ[X.sheaf.obj.obj V] n) = _ at hTensor
  rw [hTensor]
  erw [ModuleCat.restrictScalars_μ_tmul]
  change (moduleTensorRestrictUnit U M N).app W
      ((unitM.val.app V m) ⊗ₜ[(U : Scheme.{u}).sheaf.obj.obj W]
        (unitN.val.app V n)) = _
  change ((PresheafOfModules.pushforward (moduleRestrictRingHom U)).map
      (moduleTensorUnit M N)).app W
        ((modulePresheafRestrictTensorMap U M.val N.val).app W
          ((unitM.val.app V m) ⊗ₜ[(U : Scheme.{u}).sheaf.obj.obj W]
            (unitN.val.app V n))) = _
  erw [ModuleCat.restrictScalars_μ_tmul]
  let g : V ⟶ Z :=
    (homOfLE (U.ι.image_preimage_le V.unop)).op
  change (moduleTensorUnit M N).app Z
      (((M.val.map g).hom m) ⊗ₜ[X.sheaf.obj.obj Z]
        ((N.val.map g).hom n)) =
    ((moduleTensor M N).val.map g).hom
      ((moduleTensorUnit M N).app V (m ⊗ₜ[X.sheaf.obj.obj V] n))
  have h := congr_arg
    (fun k => k.hom (m ⊗ₜ[X.sheaf.obj.obj V] n))
    ((moduleTensorUnit M N).naturality g)
  change (moduleTensorUnit M N).app Z
      ((moduleTensorPresheaf M N).map g
        (m ⊗ₜ[X.sheaf.obj.obj V] n)) =
    (moduleTensor M N).val.map g
      ((moduleTensorUnit M N).app V
        (m ⊗ₜ[X.sheaf.obj.obj V] n)) at h
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at h
  exact h

private lemma moduleTensorHomEquiv_pushforwardTensorMap_restrict
    (U : X.Opens) (M N : X.Modules) :
    moduleTensorHomEquiv
        ((Scheme.Modules.restrictFunctor U.ι ⋙
          Scheme.Modules.pushforward U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι ⋙
          Scheme.Modules.pushforward U.ι).obj N)
        ((Scheme.Modules.pushforward U.ι).obj
          (moduleTensor
            ((Scheme.Modules.restrictFunctor U.ι).obj M)
            ((Scheme.Modules.restrictFunctor U.ι).obj N)))
        (modulePushforwardTensorMap U.ι
          ((Scheme.Modules.restrictFunctor U.ι).obj M)
          ((Scheme.Modules.restrictFunctor U.ι).obj N)) =
      modulePushforwardTensorPresheafMap U.ι
        ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N) := by
  dsimp only [modulePushforwardTensorMap]
  exact Equiv.apply_symm_apply _ _

/-- The tensor universal-property equivalence is concretely precomposition by the
sheafification unit. -/
lemma moduleTensorHomEquiv_eq_unit_comp
    (M N P : X.Modules) (h : moduleTensor M N ⟶ P) :
    moduleTensorHomEquiv M N P h = moduleTensorUnit M N ≫ h.val := by
  rfl

set_option maxHeartbeats 800000 in
-- The objectwise calculation passes through three restriction-of-scalars structures.
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private lemma modulePushforwardTensorPresheafMap_comp
    (f : Y ⟶ X) (g : Z ⟶ Y) (A B : Z.Modules) :
    modulePushforwardTensorPresheafMap (g ≫ f) A B ≫
        ((Scheme.Modules.pushforwardComp g f).inv.app (moduleTensor A B)).val =
      PresheafOfModules.Monoidal.tensorHom
          ((Scheme.Modules.pushforwardComp g f).inv.app A).val
          ((Scheme.Modules.pushforwardComp g f).inv.app B).val ≫
        modulePushforwardTensorPresheafMap f
          ((Scheme.Modules.pushforward g).obj A)
          ((Scheme.Modules.pushforward g).obj B) ≫
        ((Scheme.Modules.pushforward f).map
          (modulePushforwardTensorMap g A B)).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  letI : CommRing (X.ringCatSheaf.obj.obj U) :=
    inferInstanceAs (CommRing (X.sheaf.obj.obj U))
  let V := (Opens.map f.base).op.obj U
  letI : CommRing (Y.ringCatSheaf.obj.obj V) :=
    inferInstanceAs (CommRing (Y.sheaf.obj.obj V))
  let W := (Opens.map g.base).op.obj V
  letI : CommRing (Z.ringCatSheaf.obj.obj W) :=
    inferInstanceAs (CommRing (Z.sheaf.obj.obj W))
  let W' := (Opens.map (g ≫ f).base).op.obj U
  letI : CommRing (Z.ringCatSheaf.obj.obj W') :=
    inferInstanceAs (CommRing (Z.sheaf.obj.obj W'))
  letI : CommRing ↑(
      (((Opens.map f.base).sheafPushforwardContinuous
        RingCat (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf).obj.obj U) :=
    inferInstanceAs (CommRing (Y.sheaf.obj.obj V))
  letI : CommRing ↑(
      (((Opens.map g.base).sheafPushforwardContinuous
        RingCat (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology Z)).obj Z.ringCatSheaf).obj.obj V) :=
    inferInstanceAs (CommRing (Z.sheaf.obj.obj W))
  letI : CommRing ↑(
      (((Opens.map (g ≫ f).base).sheafPushforwardContinuous
        RingCat (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology Z)).obj Z.ringCatSheaf).obj.obj U) :=
    inferInstanceAs (CommRing (Z.sheaf.obj.obj W'))
  dsimp [modulePushforwardTensorPresheafMap]
  let cGF := schemePresheafPushforwardTensorMap (g ≫ f) A.val B.val
  let uGF := (PresheafOfModules.pushforward
    (g ≫ f).toRingCatSheafHom.hom).map (moduleTensorUnit A B)
  let pT := (Scheme.Modules.pushforwardComp g f).inv.app (moduleTensor A B)
  let pA := (Scheme.Modules.pushforwardComp g f).inv.app A
  let pB := (Scheme.Modules.pushforwardComp g f).inv.app B
  let t := PresheafOfModules.Monoidal.tensorHom pA.val pB.val
  let cF := schemePresheafPushforwardTensorMap f
    ((Scheme.Modules.pushforward g).obj A).val
    ((Scheme.Modules.pushforward g).obj B).val
  let uF := (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
    (moduleTensorUnit
      ((Scheme.Modules.pushforward g).obj A)
      ((Scheme.Modules.pushforward g).obj B))
  let rG := (Scheme.Modules.pushforward f).map
    (modulePushforwardTensorMap g A B)
  change
    pT.val.app U (uGF.app U (cGF.app U
      (a ⊗ₜ[X.sheaf.obj.obj U] b))) =
    rG.val.app U (uF.app U (cF.app U (t.app U
      (a ⊗ₜ[X.sheaf.obj.obj U] b))))
  have hTensor := ModuleCat.MonoidalCategory.tensorHom_tmul
    (pA.val.app U) (pB.val.app U) a b
  change t.app U (a ⊗ₜ[X.sheaf.obj.obj U] b) = _ at hTensor
  rw [hTensor]
  erw [ModuleCat.restrictScalars_μ_tmul]
  erw [ModuleCat.restrictScalars_μ_tmul]
  change uGF.app U
      (a ⊗ₜ[↑((((Opens.map (g ≫ f).base).sheafPushforwardContinuous
        RingCat (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology Z)).obj Z.ringCatSheaf).obj.obj U)] b) =
    rG.val.app U (uF.app U
      (a ⊗ₜ[↑((((Opens.map f.base).sheafPushforwardContinuous
        RingCat (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf).obj.obj U)] b))
  have hdef :
      moduleTensorUnit ((Scheme.Modules.pushforward g).obj A)
          ((Scheme.Modules.pushforward g).obj B) ≫
        (modulePushforwardTensorMap g A B).val =
      modulePushforwardTensorPresheafMap g A B := by
    rw [← moduleTensorHomEquiv_eq_unit_comp]
    dsimp only [modulePushforwardTensorMap]
    exact Equiv.apply_symm_apply _ _
  have hdefV := congr_arg (fun k => k.app V) hdef
  have hdefVab := congr_arg
    (fun k => k.hom (a ⊗ₜ[Y.sheaf.obj.obj V] b)) hdefV
  change
    (modulePushforwardTensorMap g A B).val.app V
        ((moduleTensorUnit ((Scheme.Modules.pushforward g).obj A)
          ((Scheme.Modules.pushforward g).obj B)).app V
            (a ⊗ₜ[Y.sheaf.obj.obj V] b)) =
      ((PresheafOfModules.pushforward g.toRingCatSheafHom.hom).map
        (moduleTensorUnit A B)).app V
          ((schemePresheafPushforwardTensorMap g A.val B.val).app V
            (a ⊗ₜ[Y.sheaf.obj.obj V] b)) at hdefVab
  erw [ModuleCat.restrictScalars_μ_tmul] at hdefVab
  exact hdefVab.symm

set_option linter.style.haveILetI false in
/-- The tensor comparison for module pullback is compatible with composition of
scheme morphisms. -/
theorem modulePullbackTensorMap_comp
    (f : Y ⟶ X) (g : Z ⟶ Y) (M N : X.Modules) :
    (Scheme.Modules.pullbackComp g f).hom.app (moduleTensor M N) ≫
        modulePullbackTensorMap (g ≫ f) M N ≫
          moduleTensorMap
            ((Scheme.Modules.pullbackComp g f).inv.app M)
            ((Scheme.Modules.pullbackComp g f).inv.app N) =
      (Scheme.Modules.pullback g).map (modulePullbackTensorMap f M N) ≫
        modulePullbackTensorMap g
          ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N) := by
  let adjf := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjg := Scheme.Modules.pullbackPushforwardAdjunction g
  apply ((adjf.comp adjg).homEquiv _ _).injective
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [adjg.homEquiv_naturality_right]
  rw [adjf.homEquiv_naturality_right]
  rw [adjg.homEquiv_naturality_left]
  have hg : adjg.homEquiv _ _
      (modulePullbackTensorMap g
        ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)) =
      modulePullbackTensorAdjointMap g
        ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) := by
    dsimp only [adjg, modulePullbackTensorMap]
    exact Equiv.apply_symm_apply _ _
  have hg' : adjg.homEquiv _
      (moduleTensor
        ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g).obj N))
      (modulePullbackTensorMap g
        ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)) =
      modulePullbackTensorAdjointMap g
        ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) := by
    simpa only [Functor.comp_obj] using hg
  rw [hg']
  rw [adjf.homEquiv_naturality_right]
  have hf : adjf.homEquiv _ _ (modulePullbackTensorMap f M N) =
      modulePullbackTensorAdjointMap f M N := by
    dsimp only [adjf, modulePullbackTensorMap]
    exact Equiv.apply_symm_apply _ _
  rw [hf]
  let adjc := Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)
  let e := Scheme.Modules.pullbackComp g f
  let p := Scheme.Modules.pushforwardComp g f
  have heInv : conjugateEquiv (adjf.comp adjg) adjc e.inv = p.hom := by
    dsimp only [adjf, adjg, adjc, e, p]
    exact Scheme.Modules.conjugateEquiv_pullbackComp_inv g f
  have heConj : conjugateEquiv adjc (adjf.comp adjg) e.hom = p.inv := by
    rw [← cancel_epi p.hom]
    rw [← heInv]
    rw [conjugateEquiv_comp]
    simp only [Iso.hom_inv_id, conjugateEquiv_id]
    rw [heInv]
    simp
  have heMate :
      adjf.homEquiv _ _ (adjg.homEquiv _ _ (e.hom.app (moduleTensor M N))) =
        adjc.unit.app (moduleTensor M N) ≫
          p.inv.app ((Scheme.Modules.pullback (g ≫ f)).obj (moduleTensor M N)) := by
    have hu := unit_conjugateEquiv adjc (adjf.comp adjg) e.hom (moduleTensor M N)
    rw [heConj] at hu
    calc
      _ = (adjf.comp adjg).homEquiv _ _
          (e.hom.app (moduleTensor M N)) := by
            rw [Adjunction.comp_homEquiv]
            rfl
      _ = (adjf.comp adjg).unit.app (moduleTensor M N) ≫
          (Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward f).map
            (e.hom.app (moduleTensor M N)) :=
        by
          simpa only [Functor.id_obj] using
            (adjf.comp adjg).homEquiv_unit
              (moduleTensor M N)
              ((Scheme.Modules.pullback (g ≫ f)).obj (moduleTensor M N))
              (e.hom.app (moduleTensor M N))
      _ = _ := hu.symm
  have hunit (A : X.Modules) :
      adjc.unit.app A ≫
          (Scheme.Modules.pushforward (g ≫ f)).map (e.inv.app A) ≫
          p.inv.app ((Scheme.Modules.pullback f ⋙
            Scheme.Modules.pullback g).obj A) =
        adjf.unit.app A ≫
          (Scheme.Modules.pushforward f).map
            (adjg.unit.app ((Scheme.Modules.pullback f).obj A)) := by
    have hu := unit_conjugateEquiv (adjf.comp adjg) adjc e.inv A
    rw [heInv] at hu
    rw [← Category.assoc, ← hu, Category.assoc, Iso.hom_inv_id_app]
    change (adjf.comp adjg).unit.app A = _
    rfl
  rw [heMate]
  rw [Category.assoc]
  change adjc.unit.app (moduleTensor M N) ≫
      p.inv.app ((Scheme.Modules.pullback (g ≫ f)).obj (moduleTensor M N)) ≫
        (Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward f).map
          (modulePullbackTensorMap (g ≫ f) M N ≫
            moduleTensorMap
              ((Scheme.Modules.pullbackComp g f).inv.app M)
              ((Scheme.Modules.pullbackComp g f).inv.app N)) = _
  rw [← p.inv.naturality]
  simp only [Functor.id_obj]
  rw [← Category.assoc]
  rw [← adjc.homEquiv_unit]
  rw [adjc.homEquiv_naturality_right]
  dsimp only [modulePullbackTensorMap, adjc]
  rw [Equiv.apply_symm_apply]
  apply (moduleTensorHomEquiv M N _).injective
  rw [moduleTensorHomEquiv_comp]
  rw [moduleTensorHomEquiv_comp]
  rw [moduleTensorHomEquiv_comp]
  dsimp only [modulePullbackTensorAdjointMap]
  rw [moduleTensorHomEquiv_moduleTensorMap_comp]
  rw [moduleTensorHomEquiv_moduleTensorMap_comp]
  have hpush {T W : Scheme.{u}} (h : T ⟶ W) (A B : T.Modules) :
      moduleTensorHomEquiv
          ((Scheme.Modules.pushforward h).obj A)
          ((Scheme.Modules.pushforward h).obj B)
          ((Scheme.Modules.pushforward h).obj (moduleTensor A B))
          (modulePushforwardTensorMap h A B) =
        modulePushforwardTensorPresheafMap h A B := by
    dsimp only [modulePushforwardTensorMap]
    exact Equiv.apply_symm_apply _ _
  simp only [Functor.comp_obj]
  rw [hpush, hpush]
  rw [Functor.map_comp]
  let a := PresheafOfModules.Monoidal.tensorHom
    (adjc.unit.app M).val (adjc.unit.app N).val
  let b := modulePushforwardTensorPresheafMap (g ≫ f)
    ((Scheme.Modules.pullback (g ≫ f)).obj M)
    ((Scheme.Modules.pullback (g ≫ f)).obj N)
  let c := ((Scheme.Modules.pushforward (g ≫ f)).map
    (moduleTensorMap (e.inv.app M) (e.inv.app N))).val
  let d := (p.inv.app
    (moduleTensor
      ((Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pullback f).obj M))
      ((Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pullback f).obj N)))).val
  let q := PresheafOfModules.Monoidal.tensorHom
    (adjf.unit.app M).val (adjf.unit.app N).val
  let r₀ := modulePushforwardTensorPresheafMap f
    ((Scheme.Modules.pullback f).obj M)
    ((Scheme.Modules.pullback f).obj N)
  let s := ((Scheme.Modules.pushforward f).map
    (moduleTensorMap
      (adjg.unit.app ((Scheme.Modules.pullback f).obj M))
      (adjg.unit.app ((Scheme.Modules.pullback f).obj N)))).val
  let t := ((Scheme.Modules.pushforward f).map
    (modulePushforwardTensorMap g
      ((Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pullback f).obj M))
      ((Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pullback f).obj N)))).val
  change ((a ≫ b) ≫ c) ≫ d = (q ≫ r₀) ≫ (s ≫ t)
  let A := (Scheme.Modules.pullback g).obj
    ((Scheme.Modules.pullback f).obj M)
  let B := (Scheme.Modules.pullback g).obj
    ((Scheme.Modules.pullback f).obj N)
  let e₀ := PresheafOfModules.Monoidal.tensorHom
    ((Scheme.Modules.pushforward (g ≫ f)).map (e.inv.app M)).val
    ((Scheme.Modules.pushforward (g ≫ f)).map (e.inv.app N)).val
  let b₁ := modulePushforwardTensorPresheafMap (g ≫ f) A B
  let p₀ := PresheafOfModules.Monoidal.tensorHom
    (p.inv.app A).val (p.inv.app B).val
  let r := modulePushforwardTensorPresheafMap f
    ((Scheme.Modules.pushforward g).obj A)
    ((Scheme.Modules.pushforward g).obj B)
  let u := PresheafOfModules.Monoidal.tensorHom
    ((Scheme.Modules.pushforward f).map
      (adjg.unit.app ((Scheme.Modules.pullback f).obj M))).val
    ((Scheme.Modules.pushforward f).map
      (adjg.unit.app ((Scheme.Modules.pullback f).obj N))).val
  have hnatC : e₀ ≫ b₁ = b ≫ c := by
    dsimp only [e₀, b₁, b, c, A, B]
    exact modulePushforwardTensorPresheafMap_naturality (g ≫ f)
      (e.inv.app M) (e.inv.app N)
  have hcomp : b₁ ≫ d = (p₀ ≫ r) ≫ t := by
    dsimp only [b₁, d, p₀, r, t, A, B]
    exact modulePushforwardTensorPresheafMap_comp f g _ _
  have hnatF : u ≫ r = r₀ ≫ s := by
    dsimp only [u, r, r₀, s, A, B]
    exact modulePushforwardTensorPresheafMap_naturality f
      (adjg.unit.app ((Scheme.Modules.pullback f).obj M))
      (adjg.unit.app ((Scheme.Modules.pullback f).obj N))
  have hunitM := congr_arg (fun k => k.val) (hunit M)
  have hunitN := congr_arg (fun k => k.val) (hunit N)
  change
    (((adjc.unit.app M).val ≫
      ((Scheme.Modules.pushforward (g ≫ f)).map (e.inv.app M)).val) ≫
        (p.inv.app A).val) =
      (adjf.unit.app M).val ≫
        ((Scheme.Modules.pushforward f).map
          (adjg.unit.app ((Scheme.Modules.pullback f).obj M))).val at hunitM
  change
    (((adjc.unit.app N).val ≫
      ((Scheme.Modules.pushforward (g ≫ f)).map (e.inv.app N)).val) ≫
        (p.inv.app B).val) =
      (adjf.unit.app N).val ≫
        ((Scheme.Modules.pushforward f).map
          (adjg.unit.app ((Scheme.Modules.pullback f).obj N))).val at hunitN
  have hunitTensor : (a ≫ e₀) ≫ p₀ = q ≫ u := by
    ext1 U
    letI : CommRing (X.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (X.sheaf.obj.obj U))
    change
      (((adjc.unit.app M).val.app U ⊗ₘ (adjc.unit.app N).val.app U) ≫
        (((Scheme.Modules.pushforward (g ≫ f)).map
          (e.inv.app M)).val.app U ⊗ₘ
        ((Scheme.Modules.pushforward (g ≫ f)).map
          (e.inv.app N)).val.app U)) ≫
        ((p.inv.app A).val.app U ⊗ₘ (p.inv.app B).val.app U) =
      ((adjf.unit.app M).val.app U ⊗ₘ (adjf.unit.app N).val.app U) ≫
        (((Scheme.Modules.pushforward f).map
          (adjg.unit.app ((Scheme.Modules.pullback f).obj M))).val.app U ⊗ₘ
        ((Scheme.Modules.pushforward f).map
          (adjg.unit.app ((Scheme.Modules.pullback f).obj N))).val.app U)
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    have hunitMU := congr_arg (fun k => k.app U) hunitM
    have hunitNU := congr_arg (fun k => k.app U) hunitN
    change
      (((adjc.unit.app M).val.app U ≫
        ((Scheme.Modules.pushforward (g ≫ f)).map
          (e.inv.app M)).val.app U) ≫
        (p.inv.app A).val.app U) =
      (adjf.unit.app M).val.app U ≫
        ((Scheme.Modules.pushforward f).map
          (adjg.unit.app ((Scheme.Modules.pullback f).obj M))).val.app U at hunitMU
    change
      (((adjc.unit.app N).val.app U ≫
        ((Scheme.Modules.pushforward (g ≫ f)).map
          (e.inv.app N)).val.app U) ≫
        (p.inv.app B).val.app U) =
      (adjf.unit.app N).val.app U ≫
        ((Scheme.Modules.pushforward f).map
          (adjg.unit.app ((Scheme.Modules.pullback f).obj N))).val.app U at hunitNU
    rw [hunitMU, hunitNU]
  calc
    ((a ≫ b) ≫ c) ≫ d = (a ≫ (b ≫ c)) ≫ d :=
      congr_arg (fun k => k ≫ d) (Category.assoc a b c)
    _ = (a ≫ (e₀ ≫ b₁)) ≫ d :=
      congr_arg (fun k => (a ≫ k) ≫ d) hnatC.symm
    _ = ((a ≫ e₀) ≫ b₁) ≫ d :=
      congr_arg (fun k => k ≫ d) (Category.assoc a e₀ b₁).symm
    _ = (a ≫ e₀) ≫ (b₁ ≫ d) := Category.assoc _ _ _
    _ = (a ≫ e₀) ≫ ((p₀ ≫ r) ≫ t) :=
      congr_arg (fun k => (a ≫ e₀) ≫ k) hcomp
    _ = ((a ≫ e₀) ≫ (p₀ ≫ r)) ≫ t :=
      (Category.assoc (a ≫ e₀) (p₀ ≫ r) t).symm
    _ = (((a ≫ e₀) ≫ p₀) ≫ r) ≫ t :=
      congr_arg (fun k => k ≫ t)
        (Category.assoc (a ≫ e₀) p₀ r).symm
    _ = ((q ≫ u) ≫ r) ≫ t :=
      congr_arg (fun k => (k ≫ r) ≫ t) hunitTensor
    _ = (q ≫ (u ≫ r)) ≫ t :=
      congr_arg (fun k => k ≫ t) (Category.assoc q u r)
    _ = (q ≫ (r₀ ≫ s)) ≫ t :=
      congr_arg (fun k => (q ≫ k) ≫ t) hnatF
    _ = ((q ≫ r₀) ≫ s) ≫ t :=
      congr_arg (fun k => k ≫ t) (Category.assoc q r₀ s).symm
    _ = (q ≫ r₀) ≫ (s ≫ t) := Category.assoc _ _ _

set_option maxHeartbeats 800000 in
-- The factorization passes through both tensor and restriction adjunctions.
private lemma moduleRestrictTensorAdjointMap_fac
    (U : X.Opens) (M N : X.Modules) :
    moduleRestrictTensorAdjointMap U M N ≫
      (Scheme.Modules.pushforward U.ι).map
        (moduleTensorRestrictComparison U M N) =
    (Scheme.Modules.restrictAdjunction U.ι).unit.app (moduleTensor M N) := by
  apply (moduleTensorHomEquiv M N _).injective
  rw [moduleTensorHomEquiv_comp]
  dsimp only [moduleRestrictTensorAdjointMap]
  rw [moduleTensorHomEquiv_moduleTensorMap_comp]
  rw [moduleTensorHomEquiv_pushforwardTensorMap_restrict]
  rw [moduleTensorHomEquiv_eq_unit_comp]
  dsimp only [modulePushforwardTensorPresheafMap]
  change
    (PresheafOfModules.Monoidal.tensorHom
          ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val
          ((Scheme.Modules.restrictAdjunction U.ι).unit.app N).val ≫
        schemePresheafPushforwardTensorMap U.ι
          ((Scheme.Modules.restrictFunctor U.ι).obj M).val
          ((Scheme.Modules.restrictFunctor U.ι).obj N).val ≫
        (PresheafOfModules.pushforward U.ι.toRingCatSheafHom.hom).map
          (moduleTensorUnit
            ((Scheme.Modules.restrictFunctor U.ι).obj M)
            ((Scheme.Modules.restrictFunctor U.ι).obj N))) ≫
      (PresheafOfModules.pushforward U.ι.toRingCatSheafHom.hom).map
        (moduleTensorRestrictComparison U M N).val =
    moduleTensorUnit M N ≫
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app
        (moduleTensor M N)).val
  have hpush :
      (PresheafOfModules.pushforward U.ι.toRingCatSheafHom.hom).map
          (moduleTensorUnit
            ((Scheme.Modules.restrictFunctor U.ι).obj M)
            ((Scheme.Modules.restrictFunctor U.ι).obj N)) ≫
        (PresheafOfModules.pushforward U.ι.toRingCatSheafHom.hom).map
          (moduleTensorRestrictComparison U M N).val =
      (PresheafOfModules.pushforward U.ι.toRingCatSheafHom.hom).map
        (moduleTensorRestrictUnit U M N) := by
    rw [← Functor.map_comp, moduleTensorRestrictComparison_unit]
  let a := PresheafOfModules.Monoidal.tensorHom
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app N).val
  let b := schemePresheafPushforwardTensorMap U.ι
    ((Scheme.Modules.restrictFunctor U.ι).obj M).val
    ((Scheme.Modules.restrictFunctor U.ι).obj N).val
  let c := (PresheafOfModules.pushforward U.ι.toRingCatSheafHom.hom).map
    (moduleTensorUnit
      ((Scheme.Modules.restrictFunctor U.ι).obj M)
      ((Scheme.Modules.restrictFunctor U.ι).obj N))
  let d := (PresheafOfModules.pushforward U.ι.toRingCatSheafHom.hom).map
    (moduleTensorRestrictComparison U M N).val
  let q := (PresheafOfModules.pushforward U.ι.toRingCatSheafHom.hom).map
    (moduleTensorRestrictUnit U M N)
  change (a ≫ b ≫ c) ≫ d = _
  change c ≫ d = q at hpush
  have h₁ : (a ≫ b ≫ c) ≫ d = a ≫ ((b ≫ c) ≫ d) :=
    Category.assoc _ _ _
  have h₂ : a ≫ ((b ≫ c) ≫ d) = a ≫ (b ≫ c ≫ d) :=
    congrArg (a ≫ ·) (Category.assoc b c d)
  have h₃ : a ≫ (b ≫ c ≫ d) = a ≫ b ≫ q :=
    congrArg (fun k ↦ a ≫ b ≫ k) hpush
  have h₄ : a ≫ b ≫ q = moduleTensorUnit M N ≫
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app
        (moduleTensor M N)).val := by
    dsimp only [a, b, q]
    convert moduleRestrictTensorPresheaf_fac U M N using 1
    rfl
  exact h₁.trans (h₂.trans (h₃.trans h₄))

set_option maxHeartbeats 800000 in
-- Applying the restriction adjunction reduces this to the preceding mate factorization.
/-- The restriction-adjunction tensor map is a left inverse to the canonical restriction
comparison. -/
lemma moduleRestrictTensorMap_comp_comparison (U : X.Opens) (M N : X.Modules) :
    moduleRestrictTensorMap U M N ≫ moduleTensorRestrictComparison U M N =
      𝟙 ((Scheme.Modules.restrictFunctor U.ι).obj (moduleTensor M N)) := by
  let adjR := Scheme.Modules.restrictAdjunction U.ι
  apply (adjR.homEquiv _ _).injective
  rw [adjR.homEquiv_naturality_right]
  dsimp only [moduleRestrictTensorMap, adjR]
  rw [Equiv.apply_symm_apply]
  rw [moduleRestrictTensorAdjointMap_fac]
  rw [Adjunction.homEquiv_apply]
  rfl

/-- The restriction-adjunction tensor map is the inverse of the canonical restriction
comparison. -/
lemma moduleRestrictTensorMap_eq_inv_comparison (U : X.Opens) (M N : X.Modules) :
    moduleRestrictTensorMap U M N = inv (moduleTensorRestrictComparison U M N) := by
  exact IsIso.eq_inv_of_inv_hom_id
    (moduleRestrictTensorMap_comp_comparison U M N)

set_option linter.style.haveILetI false in
/-- The canonical pullback tensor comparison along the inclusion of an open subscheme is an
isomorphism for arbitrary module sheaves. -/
theorem modulePullbackTensorMap_open_ι_isIso (U : X.Opens) (M N : X.Modules) :
    IsIso (modulePullbackTensorMap U.ι M N) := by
  let r := moduleRestrictTensorMap U M N
  letI : IsIso r := by
    rw [show r = inv (moduleTensorRestrictComparison U M N) from
      moduleRestrictTensorMap_eq_inv_comparison U M N]
    infer_instance
  let e := Scheme.Modules.restrictFunctorIsoPullback U.ι
  letI : IsIso (moduleTensorMap (e.hom.app M) (e.hom.app N)) :=
    moduleTensorMap_isIso _ _
  rw [modulePullbackTensorMap_open_eq]
  change IsIso (e.inv.app (moduleTensor M N) ≫ r ≫
    moduleTensorMap (e.hom.app M) (e.hom.app N))
  infer_instance

private def modulePresheafRightUnitor (M : X.Modules) :
    moduleTensorPresheaf M (SheafOfModules.unit X.ringCatSheaf) ⟶ M.val := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  exact (rightUnitor M.val).hom

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private lemma modulePresheafRightUnitor_tmul (M : X.Modules)
    (U : (Opens X)ᵒᵖ) (m : M.val.obj U) (r : X.sheaf.obj.obj U) :
    (modulePresheafRightUnitor M).app U
        (m ⊗ₜ[X.sheaf.obj.obj U] r) = r • m := by
  letI : CommRing (X.ringCatSheaf.obj.obj U) :=
    inferInstanceAs (CommRing (X.sheaf.obj.obj U))
  dsimp [modulePresheafRightUnitor]
  exact ModuleCat.MonoidalCategory.rightUnitor_hom_apply m r

set_option backward.isDefEq.respectTransparency false in
private lemma moduleTensorHomEquiv_rightUnit (M : X.Modules) :
    moduleTensorHomEquiv M (SheafOfModules.unit X.ringCatSheaf) M
        (moduleTensorRightUnitIso M).hom =
      modulePresheafRightUnitor M := by
  set_option linter.style.haveILetI false in
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  change adj.homEquiv _ _ (moduleTensorRightUnitIso M).hom = _
  rw [adj.homEquiv_unit]
  change adj.unit.app _ ≫
      (L.map (rightUnitor M.val).hom).val ≫ (adj.counit.app M).val = _
  have hnat := adj.unit.naturality (rightUnitor M.val).hom
  simp only [Functor.id_map, Functor.comp_map] at hnat
  have hnat' := hnat.symm
  change adj.unit.app _ ≫ (L.map (rightUnitor M.val).hom).val =
    (rightUnitor M.val).hom ≫ adj.unit.app M.val at hnat'
  rw [← Category.assoc, hnat', Category.assoc]
  have htri := adj.right_triangle_components (Y := M)
  change adj.unit.app M.val ≫ (adj.counit.app M).val = 𝟙 M.val at htri
  rw [htri, Category.comp_id]
  rfl

private lemma moduleTensorUnit_rightUnit (M : X.Modules) :
    moduleTensorUnit M (SheafOfModules.unit X.ringCatSheaf) ≫
        (moduleTensorRightUnitIso M).hom.val =
      modulePresheafRightUnitor M := by
  change moduleTensorHomEquiv M (SheafOfModules.unit X.ringCatSheaf) M
      (moduleTensorRightUnitIso M).hom = _
  exact moduleTensorHomEquiv_rightUnit M

private def modulePullbackTensorTargetToUnit (f : Y ⟶ X) :
    moduleTensor
        ((Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf))
        ((Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf)) ⟶
      SheafOfModules.unit Y.ringCatSheaf := by
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact moduleTensorMap
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
    (moduleTensorRightUnitIso (SheafOfModules.unit Y.ringCatSheaf)).hom

private def modulePullbackTensorSourceToUnit (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).obj
        (moduleTensor (SheafOfModules.unit X.ringCatSheaf)
          (SheafOfModules.unit X.ringCatSheaf)) ⟶
      SheafOfModules.unit Y.ringCatSheaf := by
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact (Scheme.Modules.pullback f).map
      (moduleTensorRightUnitIso (SheafOfModules.unit X.ringCatSheaf)).hom ≫
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

private def unitPushforwardTensorLeft (f : Y ⟶ X) :=
  PresheafOfModules.Monoidal.tensorHom
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val ≫
    schemePresheafPushforwardTensorMap f
      (SheafOfModules.unit Y.ringCatSheaf).val
      (SheafOfModules.unit Y.ringCatSheaf).val ≫
    (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
      (modulePresheafRightUnitor (SheafOfModules.unit Y.ringCatSheaf))

private def unitPushforwardTensorRight (f : Y ⟶ X) :=
  modulePresheafRightUnitor (SheafOfModules.unit X.ringCatSheaf) ≫
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val

set_option maxHeartbeats 1600000 in
-- Evaluating the three nested objectwise tensor maps unfolds several transported module structures.
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private lemma unitPushforwardTensor_tmul (f : Y ⟶ X)
    (U : (Opens X)ᵒᵖ) (r s : X.sheaf.obj.obj U) :
    (unitPushforwardTensorLeft f).app U
        (r ⊗ₜ[X.sheaf.obj.obj U] s) =
      (unitPushforwardTensorRight f).app U
        (r ⊗ₜ[X.sheaf.obj.obj U] s) := by
  letI : CommRing (X.ringCatSheaf.obj.obj U) :=
    inferInstanceAs (CommRing (X.sheaf.obj.obj U))
  let V := (Opens.map f.base).op.obj U
  letI : CommRing (Y.ringCatSheaf.obj.obj V) :=
    inferInstanceAs (CommRing (Y.sheaf.obj.obj V))
  letI : CommRing ↑(
      (((Opens.map f.base).sheafPushforwardContinuous
        RingCat (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf).obj.obj U) :=
    inferInstanceAs (CommRing (Y.sheaf.obj.obj V))
  dsimp [unitPushforwardTensorLeft, unitPushforwardTensorRight,
    modulePresheafRightUnitor, schemePresheafPushforwardTensorMap,
    SheafOfModules.unitToPushforwardObjUnit]
  change
    (modulePresheafRightUnitor (SheafOfModules.unit Y.ringCatSheaf)).app _
        ((schemePresheafPushforwardTensorMap f
            (SheafOfModules.unit Y.ringCatSheaf).val
            (SheafOfModules.unit Y.ringCatSheaf).val).app U
          ((PresheafOfModules.Monoidal.tensorHom
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val).app U
            (r ⊗ₜ[X.sheaf.obj.obj U] s))) =
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val.app U
        ((modulePresheafRightUnitor
          (SheafOfModules.unit X.ringCatSheaf)).app U
            (r ⊗ₜ[X.sheaf.obj.obj U] s))
  let unitMap :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hTensor := ModuleCat.MonoidalCategory.tensorHom_tmul
    (unitMap.val.app U) (unitMap.val.app U) r s
  change
    (PresheafOfModules.Monoidal.tensorHom unitMap.val unitMap.val).app U
        (r ⊗ₜ[X.sheaf.obj.obj U] s) = _ at hTensor
  rw [hTensor]
  erw [ModuleCat.restrictScalars_μ_tmul]
  erw [modulePresheafRightUnitor_tmul]
  erw [modulePresheafRightUnitor_tmul]
  change (f.toRingCatSheafHom.hom.app U).hom s *
      (f.toRingCatSheafHom.hom.app U).hom r =
    (f.toRingCatSheafHom.hom.app U).hom (s * r)
  exact ((f.toRingCatSheafHom.hom.app U).hom.map_mul s r).symm

set_option maxHeartbeats 400000 in
-- Tensor extensionality elaborates the restriction-of-scalars module structures on both factors.
set_option backward.isDefEq.respectTransparency false in
private lemma unitPushforwardTensor_app (f : Y ⟶ X) (U : (Opens X)ᵒᵖ) :
    (unitPushforwardTensorLeft f).app U =
      (unitPushforwardTensorRight f).app U := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r s
  exact unitPushforwardTensor_tmul f U r s

set_option maxHeartbeats 400000 in
-- Natural-transformation extensionality retains the objectwise tensor module structures.
private lemma schemePresheafPushforwardTensorMap_unit_rightUnitality
    (f : Y ⟶ X) :
    unitPushforwardTensorLeft f = unitPushforwardTensorRight f := by
  ext1 U
  exact unitPushforwardTensor_app f U

set_option maxHeartbeats 400000 in
-- The proof traverses both the sheafification and module pullback-pushforward adjunctions.
set_option backward.isDefEq.respectTransparency false in
private lemma modulePullbackTensorMap_unit_fac (f : Y ⟶ X) :
    modulePullbackTensorMap f
        (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.unit X.ringCatSheaf) ≫
      modulePullbackTensorTargetToUnit f =
    modulePullbackTensorSourceToUnit f := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    adj.isRightAdjoint
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [modulePullbackTensorMap, adj]
  rw [Equiv.apply_symm_apply]
  dsimp [modulePullbackTensorAdjointMap, modulePullbackTensorTargetToUnit,
    modulePullbackTensorSourceToUnit]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← modulePushforwardTensorMap_naturality]
  slice_lhs 1 2 => rw [moduleTensorMap_comp]
  rw [Adjunction.homEquiv_naturality_left]
  rw [← adj.homEquiv_unit]
  have hp :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom
  change adj.homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom at hp
  rw [hp]
  simp only [Category.assoc]
  apply (moduleTensorHomEquiv _ _ _).injective
  rw [moduleTensorHomEquiv_moduleTensorMap_comp]
  rw [moduleTensorHomEquiv_comp, moduleTensorHomEquiv_comp]
  dsimp only [modulePushforwardTensorMap]
  rw [Equiv.apply_symm_apply]
  rw [moduleTensorHomEquiv_rightUnit]
  dsimp only [modulePushforwardTensorPresheafMap]
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    change (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
        (moduleTensorUnit (SheafOfModules.unit Y.ringCatSheaf)
          (SheafOfModules.unit Y.ringCatSheaf)) ≫
      (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
        (moduleTensorRightUnitIso (SheafOfModules.unit Y.ringCatSheaf)).hom.val
    rw [← Functor.map_comp, moduleTensorUnit_rightUnit]
  change unitPushforwardTensorLeft f = unitPushforwardTensorRight f
  exact schemePresheafPushforwardTensorMap_unit_rightUnitality f

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private lemma modulePullbackTensorTargetToUnit_isIso (f : Y ⟶ X) :
    IsIso (modulePullbackTensorTargetToUnit f) := by
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let p := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  letI : IsIso p := by dsimp only [p]; infer_instance
  letI : IsIso (moduleTensorMap p p) := moduleTensorMap_isIso p p
  dsimp only [modulePullbackTensorTargetToUnit]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private lemma modulePullbackTensorSourceToUnit_isIso (f : Y ⟶ X) :
    IsIso (modulePullbackTensorSourceToUnit f) := by
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let p := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let q := (Scheme.Modules.pullback f).map
    (moduleTensorRightUnitIso (SheafOfModules.unit X.ringCatSheaf)).hom
  letI : IsIso p := by dsimp only [p]; infer_instance
  letI : IsIso q := by dsimp only [q]; infer_instance
  change IsIso (q ≫ p)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- The canonical pullback tensor comparison is an isomorphism on the structure sheaf. -/
theorem modulePullbackTensorMap_unit_isIso (f : Y ⟶ X) :
    IsIso (modulePullbackTensorMap f
      (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf)) := by
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : IsIso (modulePullbackTensorTargetToUnit f) :=
    modulePullbackTensorTargetToUnit_isIso f
  letI : IsIso (modulePullbackTensorSourceToUnit f) :=
    modulePullbackTensorSourceToUnit_isIso f
  exact IsIso.of_isIso_fac_right (modulePullbackTensorMap_unit_fac f)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- The canonical pullback tensor comparison is an isomorphism when both module sheaves are
globally trivial. -/
theorem modulePullbackTensorMap_isIso_of_iso_unit (f : Y ⟶ X)
    {M N : X.Modules} (eM : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (modulePullbackTensorMap f M N) := by
  let a := (Scheme.Modules.pullback f).map (moduleTensorMap eM.hom eN.hom)
  let b := moduleTensorMap ((Scheme.Modules.pullback f).map eM.hom)
    ((Scheme.Modules.pullback f).map eN.hom)
  let c := modulePullbackTensorMap f
    (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit X.ringCatSheaf)
  letI : IsIso (moduleTensorMap eM.hom eN.hom) :=
    moduleTensorMap_isIso eM.hom eN.hom
  letI : IsIso a := by dsimp only [a]; infer_instance
  letI : IsIso ((Scheme.Modules.pullback f).map eM.hom) := inferInstance
  letI : IsIso ((Scheme.Modules.pullback f).map eN.hom) := inferInstance
  letI : IsIso b := moduleTensorMap_isIso _ _
  letI : IsIso c := by
    dsimp only [c]
    exact modulePullbackTensorMap_unit_isIso f
  have hfac : a ≫ c = modulePullbackTensorMap f M N ≫ b := by
    exact modulePullbackTensorMap_naturality f eM.hom eN.hom
  haveI : IsIso (a ≫ c) := inferInstance
  exact IsIso.of_isIso_fac_right hfac.symm

private def modulePresheafLeftUnitor (M : X.Modules) :
    moduleTensorPresheaf (SheafOfModules.unit X.ringCatSheaf) M ⟶ M.val := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  exact (leftUnitor M.val).hom

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private lemma modulePresheafLeftUnitor_tmul (M : X.Modules)
    (U : (Opens X)ᵒᵖ) (r : X.sheaf.obj.obj U) (m : M.val.obj U) :
    (modulePresheafLeftUnitor M).app U
        (r ⊗ₜ[X.sheaf.obj.obj U] m) = r • m := by
  letI : CommRing (X.ringCatSheaf.obj.obj U) :=
    inferInstanceAs (CommRing (X.sheaf.obj.obj U))
  dsimp [modulePresheafLeftUnitor]
  exact ModuleCat.MonoidalCategory.leftUnitor_hom_apply r m

set_option backward.isDefEq.respectTransparency false in
private lemma moduleTensorHomEquiv_leftUnit (M : X.Modules) :
    moduleTensorHomEquiv (SheafOfModules.unit X.ringCatSheaf) M M
        (moduleTensorLeftUnitIso M).hom =
      modulePresheafLeftUnitor M := by
  set_option linter.style.haveILetI false in
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  change adj.homEquiv _ _ (moduleTensorLeftUnitIso M).hom = _
  rw [adj.homEquiv_unit]
  change adj.unit.app _ ≫
      (L.map (leftUnitor M.val).hom).val ≫ (adj.counit.app M).val = _
  have hnat := adj.unit.naturality (leftUnitor M.val).hom
  simp only [Functor.id_map, Functor.comp_map] at hnat
  have hnat' := hnat.symm
  change adj.unit.app _ ≫ (L.map (leftUnitor M.val).hom).val =
    (leftUnitor M.val).hom ≫ adj.unit.app M.val at hnat'
  rw [← Category.assoc, hnat', Category.assoc]
  have htri := adj.right_triangle_components (Y := M)
  change adj.unit.app M.val ≫ (adj.counit.app M).val = 𝟙 M.val at htri
  rw [htri, Category.comp_id]
  rfl

private lemma moduleTensorUnit_leftUnit (M : X.Modules) :
    moduleTensorUnit (SheafOfModules.unit X.ringCatSheaf) M ≫
        (moduleTensorLeftUnitIso M).hom.val =
      modulePresheafLeftUnitor M := by
  change moduleTensorHomEquiv (SheafOfModules.unit X.ringCatSheaf) M M
      (moduleTensorLeftUnitIso M).hom = _
  exact moduleTensorHomEquiv_leftUnit M

private def modulePullbackTensorLeftUnitTargetToObj (f : Y ⟶ X)
    (M : X.Modules) :
    moduleTensor
        ((Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf))
        ((Scheme.Modules.pullback f).obj M) ⟶
      (Scheme.Modules.pullback f).obj M := by
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact moduleTensorMap
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
      (𝟙 ((Scheme.Modules.pullback f).obj M)) ≫
    (moduleTensorLeftUnitIso ((Scheme.Modules.pullback f).obj M)).hom

private def modulePullbackTensorLeftUnitSourceToObj (f : Y ⟶ X)
    (M : X.Modules) :
    (Scheme.Modules.pullback f).obj
        (moduleTensor (SheafOfModules.unit X.ringCatSheaf) M) ⟶
      (Scheme.Modules.pullback f).obj M :=
  (Scheme.Modules.pullback f).map (moduleTensorLeftUnitIso M).hom

private def leftUnitPushforwardTensorLeft (f : Y ⟶ X) (M : X.Modules) :=
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  PresheafOfModules.Monoidal.tensorHom
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val
          (adj.unit.app M).val ≫
    schemePresheafPushforwardTensorMap f
      (SheafOfModules.unit Y.ringCatSheaf).val
      ((Scheme.Modules.pullback f).obj M).val ≫
    (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
      (modulePresheafLeftUnitor ((Scheme.Modules.pullback f).obj M))

private def leftUnitPushforwardTensorRight (f : Y ⟶ X) (M : X.Modules) :=
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  modulePresheafLeftUnitor M ≫ (adj.unit.app M).val

set_option maxHeartbeats 1600000 in
-- Evaluating the nested tensor maps unfolds the adjunction-unit module structures at each open.
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private lemma leftUnitPushforwardTensor_tmul (f : Y ⟶ X) (M : X.Modules)
    (U : (Opens X)ᵒᵖ) (r : X.sheaf.obj.obj U) (m : M.val.obj U) :
    (leftUnitPushforwardTensorLeft f M).app U
        (r ⊗ₜ[X.sheaf.obj.obj U] m) =
      (leftUnitPushforwardTensorRight f M).app U
        (r ⊗ₜ[X.sheaf.obj.obj U] m) := by
  letI : CommRing (X.ringCatSheaf.obj.obj U) :=
    inferInstanceAs (CommRing (X.sheaf.obj.obj U))
  let V := (Opens.map f.base).op.obj U
  letI : CommRing (Y.ringCatSheaf.obj.obj V) :=
    inferInstanceAs (CommRing (Y.sheaf.obj.obj V))
  letI : CommRing ↑(
      (((Opens.map f.base).sheafPushforwardContinuous
        RingCat (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf).obj.obj U) :=
    inferInstanceAs (CommRing (Y.sheaf.obj.obj V))
  dsimp [leftUnitPushforwardTensorLeft, leftUnitPushforwardTensorRight,
    modulePresheafLeftUnitor, schemePresheafPushforwardTensorMap,
    SheafOfModules.unitToPushforwardObjUnit]
  change
    (modulePresheafLeftUnitor ((Scheme.Modules.pullback f).obj M)).app _
        ((schemePresheafPushforwardTensorMap f
            (SheafOfModules.unit Y.ringCatSheaf).val
            ((Scheme.Modules.pullback f).obj M).val).app U
          ((PresheafOfModules.Monoidal.tensorHom
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val
              ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val).app U
            (r ⊗ₜ[X.sheaf.obj.obj U] m))) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U
        ((modulePresheafLeftUnitor M).app U
          (r ⊗ₜ[X.sheaf.obj.obj U] m))
  let unitMap :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let moduleMap := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  have hTensor := ModuleCat.MonoidalCategory.tensorHom_tmul
    (unitMap.val.app U) (moduleMap.val.app U) r m
  change
    (PresheafOfModules.Monoidal.tensorHom unitMap.val moduleMap.val).app U
        (r ⊗ₜ[X.sheaf.obj.obj U] m) = _ at hTensor
  rw [hTensor]
  erw [ModuleCat.restrictScalars_μ_tmul]
  erw [modulePresheafLeftUnitor_tmul]
  erw [modulePresheafLeftUnitor_tmul]
  exact ((moduleMap.val.app U).hom.map_smul r m).symm

set_option maxHeartbeats 400000 in
-- Tensor extensionality elaborates the transported module structure on the pulled-back factor.
set_option backward.isDefEq.respectTransparency false in
private lemma leftUnitPushforwardTensor_app (f : Y ⟶ X) (M : X.Modules)
    (U : (Opens X)ᵒᵖ) :
    (leftUnitPushforwardTensorLeft f M).app U =
      (leftUnitPushforwardTensorRight f M).app U := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r m
  exact leftUnitPushforwardTensor_tmul f M U r m

private lemma schemePresheafPushforwardTensorMap_leftUnit (f : Y ⟶ X)
    (M : X.Modules) :
    leftUnitPushforwardTensorLeft f M =
      leftUnitPushforwardTensorRight f M := by
  ext1 U
  exact leftUnitPushforwardTensor_app f M U

set_option maxHeartbeats 400000 in
-- The factorization traverses the sheafification and pullback-pushforward adjunctions.
set_option backward.isDefEq.respectTransparency false in
private lemma modulePullbackTensorMap_leftUnit_fac (f : Y ⟶ X) (M : X.Modules) :
    modulePullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf) M ≫
      modulePullbackTensorLeftUnitTargetToObj f M =
    modulePullbackTensorLeftUnitSourceToObj f M := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    adj.isRightAdjoint
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [modulePullbackTensorMap, adj]
  rw [Equiv.apply_symm_apply]
  dsimp [modulePullbackTensorAdjointMap, modulePullbackTensorLeftUnitTargetToObj,
    modulePullbackTensorLeftUnitSourceToObj]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← modulePushforwardTensorMap_naturality]
  slice_lhs 1 2 => rw [moduleTensorMap_comp]
  have hId := (Scheme.Modules.pushforward f).map_id
    ((Scheme.Modules.pullback f).obj M)
  change (Scheme.Modules.pushforward f).map
      (𝟙 ((Scheme.Modules.pullback f).obj M)) =
    𝟙 ((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback f).obj M)) at hId
  rw [hId, Category.comp_id]
  have hright := adj.homEquiv_naturality_left
    (moduleTensorLeftUnitIso M).hom
    (𝟙 ((Scheme.Modules.pullback f).obj M))
  rw [Category.comp_id, adj.homEquiv_id] at hright
  rw [hright]
  rw [← adj.homEquiv_unit]
  have hp :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom
  change adj.homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom at hp
  rw [hp]
  simp only [Category.assoc]
  apply (moduleTensorHomEquiv _ _ _).injective
  rw [moduleTensorHomEquiv_moduleTensorMap_comp]
  rw [moduleTensorHomEquiv_comp, moduleTensorHomEquiv_comp]
  dsimp only [modulePushforwardTensorMap]
  rw [Equiv.apply_symm_apply]
  rw [moduleTensorHomEquiv_leftUnit]
  dsimp only [modulePushforwardTensorPresheafMap]
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    change (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
        (moduleTensorUnit (SheafOfModules.unit Y.ringCatSheaf)
          ((Scheme.Modules.pullback f).obj M)) ≫
      (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
        (moduleTensorLeftUnitIso ((Scheme.Modules.pullback f).obj M)).hom.val
    rw [← Functor.map_comp, moduleTensorUnit_leftUnit]
  change leftUnitPushforwardTensorLeft f M =
    leftUnitPushforwardTensorRight f M
  exact schemePresheafPushforwardTensorMap_leftUnit f M

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private lemma modulePullbackTensorLeftUnitTargetToObj_isIso (f : Y ⟶ X)
    (M : X.Modules) : IsIso (modulePullbackTensorLeftUnitTargetToObj f M) := by
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let p := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let q := 𝟙 ((Scheme.Modules.pullback f).obj M)
  letI : IsIso p := by dsimp only [p]; infer_instance
  letI : IsIso q := by dsimp only [q]; infer_instance
  letI : IsIso (moduleTensorMap p q) := moduleTensorMap_isIso p q
  dsimp only [modulePullbackTensorLeftUnitTargetToObj]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma modulePullbackTensorLeftUnitSourceToObj_isIso (f : Y ⟶ X)
    (M : X.Modules) : IsIso (modulePullbackTensorLeftUnitSourceToObj f M) := by
  dsimp only [modulePullbackTensorLeftUnitSourceToObj]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- The canonical pullback tensor comparison is an isomorphism whenever its left factor is the
structure sheaf. -/
theorem modulePullbackTensorMap_leftUnit_isIso (f : Y ⟶ X) (M : X.Modules) :
    IsIso (modulePullbackTensorMap f
      (SheafOfModules.unit X.ringCatSheaf) M) := by
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : IsIso (modulePullbackTensorLeftUnitTargetToObj f M) :=
    modulePullbackTensorLeftUnitTargetToObj_isIso f M
  letI : IsIso (modulePullbackTensorLeftUnitSourceToObj f M) :=
    modulePullbackTensorLeftUnitSourceToObj_isIso f M
  exact IsIso.of_isIso_fac_right
    (modulePullbackTensorMap_leftUnit_fac f M)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- The canonical pullback tensor comparison is an isomorphism whenever its left factor is
globally trivial. -/
theorem modulePullbackTensorMap_isIso_of_iso_leftUnit (f : Y ⟶ X)
    {M N : X.Modules} (eM : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (modulePullbackTensorMap f M N) := by
  let a := (Scheme.Modules.pullback f).map
    (moduleTensorMap eM.hom (𝟙 N))
  let b := moduleTensorMap ((Scheme.Modules.pullback f).map eM.hom)
    ((Scheme.Modules.pullback f).map (𝟙 N))
  let c := modulePullbackTensorMap f
    (SheafOfModules.unit X.ringCatSheaf) N
  letI : IsIso (moduleTensorMap eM.hom (𝟙 N)) :=
    moduleTensorMap_isIso eM.hom (𝟙 N)
  letI : IsIso a := by dsimp only [a]; infer_instance
  letI : IsIso ((Scheme.Modules.pullback f).map eM.hom) := inferInstance
  letI : IsIso ((Scheme.Modules.pullback f).map (𝟙 N)) := inferInstance
  letI : IsIso b := moduleTensorMap_isIso _ _
  letI : IsIso c := by
    dsimp only [c]
    exact modulePullbackTensorMap_leftUnit_isIso f N
  have hfac : a ≫ c = modulePullbackTensorMap f M N ≫ b := by
    exact modulePullbackTensorMap_naturality f eM.hom (𝟙 N)
  haveI : IsIso (a ≫ c) := inferInstance
  exact IsIso.of_isIso_fac_right hfac.symm

/-- Pullback of a free module sheaf along a scheme morphism is the free module sheaf on the same
basis. -/
def schemePullbackFreeIso (f : Y ⟶ X) (I : Type u) :
    (Scheme.Modules.pullback f).obj
        (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      SheafOfModules.free (R := Y.ringCatSheaf) I :=
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

/-- Under the equivalence between modules on an over-site and modules on the corresponding open
subscheme, the standard free rank-one module corresponds to the standard free rank-one module. -/
def overEquivFreePUnitIso (U : X.Opens) :
    (Scheme.Modules.overEquiv U).functor.obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} PUnit)) ≅
      SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) (ULift.{u, 0} PUnit) :=
  (Scheme.Modules.overEquiv U).functor.mapIso (freePUnitOverIsoUnit U) ≪≫
    (freePUnitIsoUnit (U : Scheme.{u})).symm

/-- Restricting a pulled-back module to the inverse image of an open set agrees with pulling back
the restriction to that open set. -/
def modulePullbackRestrictIso (f : Y ⟶ X) (U : X.Opens) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.pullback f).obj M) ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app
      ((Scheme.Modules.pullback f).obj M) ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm

/-- A rank-one trivialization on an over-site gives the corresponding trivialization on the open
subscheme. -/
def rankOneLocalSchemeIso {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData]
    (i : q.I) (e : (q.generators i).I ≃ ULift.{u, 0} PUnit) :
    SheafOfModules.free (R := (q.X i : Scheme.{u}).ringCatSheaf)
        (ULift.{u, 0} PUnit) ≅
      (Scheme.Modules.restrictFunctor (Scheme.Opens.ι (q.X i))).obj M := by
  letI : IsIso (q.generators i).π :=
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso i
  exact (overEquivFreePUnitIso (q.X i)).symm ≪≫
    (Scheme.Modules.overEquiv (q.X i)).functor.mapIso
      (freeOverEquivIso e.symm ≪≫ asIso (q.generators i).π) ≪≫
    (Scheme.Modules.overFunctorEquiv (q.X i)).app M

set_option linter.style.haveILetI false in
private lemma moduleHom_over_isIso_of_restrict {M N : X.Modules} (h : M ⟶ N)
    (U : X.Opens) [IsIso ((Scheme.Modules.restrictFunctor U.ι).map h)] :
    IsIso (h.over U) := by
  let E := Scheme.Modules.overEquiv U
  let e := Scheme.Modules.overFunctorEquiv U
  letI : IsIso (e.hom.app M) := CategoryTheory.NatIso.hom_app_isIso e M
  letI : IsIso (e.hom.app N) := CategoryTheory.NatIso.hom_app_isIso e N
  have he := e.hom.naturality h
  haveI hcomp : IsIso
      ((SheafOfModules.overFunctor X.ringCatSheaf U ⋙ E.functor).map h ≫
        e.hom.app N) := by
    rw [he]
    infer_instance
  haveI hmap : IsIso
      ((SheafOfModules.overFunctor X.ringCatSheaf U ⋙ E.functor).map h) :=
    IsIso.of_isIso_comp_right _ (e.hom.app N)
  change IsIso (E.functor.map (h.over U)) at hmap
  exact Functor.ReflectsIsomorphisms.reflects E.functor (h.over U)

set_option linter.style.haveILetI false in
private lemma moduleHom_over_isIso_of_pullback {M N : X.Modules} (h : M ⟶ N)
    (U : X.Opens) [IsIso ((Scheme.Modules.pullback U.ι).map h)] :
    IsIso (h.over U) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback U.ι
  letI : IsIso (e.hom.app M) := CategoryTheory.NatIso.hom_app_isIso e M
  letI : IsIso (e.hom.app N) := CategoryTheory.NatIso.hom_app_isIso e N
  have he := e.hom.naturality h
  haveI hcomp : IsIso
      ((Scheme.Modules.restrictFunctor U.ι).map h ≫ e.hom.app N) := by
    rw [he]
    infer_instance
  haveI : IsIso ((Scheme.Modules.restrictFunctor U.ι).map h) :=
    IsIso.of_isIso_comp_right _ (e.hom.app N)
  exact moduleHom_over_isIso_of_restrict h U

set_option linter.style.haveILetI false in
private lemma pullback_modulePullbackTensorMap_isIso_of_iso_on_open
    (f : Y ⟶ X) (U : X.Opens) {M N : X.Modules}
    (eM : (Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map
      (modulePullbackTensorMap f M N)) := by
  let fU := f ∣_ U
  let iX := U.ι
  let iY := (f ⁻¹ᵁ U).ι
  let cX := modulePullbackTensorMap iX M N
  let cU := modulePullbackTensorMap fU
    ((Scheme.Modules.pullback iX).obj M)
    ((Scheme.Modules.pullback iX).obj N)
  let cComp := modulePullbackTensorMap (fU ≫ iX) M N
  let r := moduleTensorMap
    ((Scheme.Modules.pullbackComp fU iX).inv.app M)
    ((Scheme.Modules.pullbackComp fU iX).inv.app N)
  let l := (Scheme.Modules.pullbackComp fU iX).hom.app (moduleTensor M N)
  let rhs := (Scheme.Modules.pullback fU).map cX ≫ cU
  letI : IsIso cX := by
    dsimp only [cX, iX]
    exact modulePullbackTensorMap_open_ι_isIso U M N
  letI : IsIso cU := by
    dsimp only [cU, fU, iX]
    exact modulePullbackTensorMap_isIso_of_iso_leftUnit (f ∣_ U) eM
  letI : IsIso l := by dsimp only [l]; infer_instance
  letI : IsIso r := by
    dsimp only [r]
    exact moduleTensorMap_isIso _ _
  letI : IsIso rhs := by dsimp only [rhs]; infer_instance
  have hinner : l ≫ cComp ≫ r = rhs := by
    dsimp only [l, cComp, r, rhs, cX, cU, fU, iX]
    exact modulePullbackTensorMap_comp U.ι (f ∣_ U) M N
  haveI : IsIso (cComp ≫ r) := IsIso.of_isIso_fac_left hinner
  haveI hcComp : IsIso cComp := IsIso.of_isIso_comp_right cComp r
  haveI hcComp' : IsIso (modulePullbackTensorMap (iY ≫ f) M N) := by
    dsimp only [iY]
    rw [← morphismRestrict_ι f U]
    exact hcComp
  let cY := modulePullbackTensorMap iY
    ((Scheme.Modules.pullback f).obj M)
    ((Scheme.Modules.pullback f).obj N)
  let pulled := (Scheme.Modules.pullback iY).map
    (modulePullbackTensorMap f M N)
  let outerR := moduleTensorMap
    ((Scheme.Modules.pullbackComp iY f).inv.app M)
    ((Scheme.Modules.pullbackComp iY f).inv.app N)
  let outerL := (Scheme.Modules.pullbackComp iY f).hom.app
    (moduleTensor M N)
  letI : IsIso cY := by
    dsimp only [cY, iY]
    exact modulePullbackTensorMap_open_ι_isIso (f ⁻¹ᵁ U)
      ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N)
  letI : IsIso outerL := by dsimp only [outerL]; infer_instance
  letI : IsIso outerR := by
    dsimp only [outerR]
    exact moduleTensorMap_isIso _ _
  have houter : outerL ≫ modulePullbackTensorMap (iY ≫ f) M N ≫ outerR =
      pulled ≫ cY := by
    dsimp only [outerL, outerR, pulled, cY, iY]
    exact modulePullbackTensorMap_comp f (f ⁻¹ᵁ U).ι M N
  haveI : IsIso (pulled ≫ cY) := by
    rw [← houter]
    infer_instance
  haveI : IsIso pulled := IsIso.of_isIso_comp_right pulled cY
  exact inferInstance

set_option linter.style.haveILetI false in
/-- The canonical pullback tensor comparison is an isomorphism when its left factor has an
explicit rank-one local trivialization. -/
theorem modulePullbackTensorMap_isIso_of_hasRankOneTrivialization
    (f : Y ⟶ X) {M N : X.Modules} (hM : HasRankOneTrivialization M) :
    IsIso (modulePullbackTensorMap f M N) := by
  obtain ⟨q, hqfree, hqrank⟩ := hM
  letI : q.IsLocallyFreeData := hqfree
  apply moduleHom_isIso_of_coversTop _ (fun i => f ⁻¹ᵁ q.X i)
  · rw [Opens.coversTop_iff]
    exact f.iSup_preimage_eq_top
      ((Opens.coversTop_iff X q.X).mp q.coversTop)
  · intro i
    let eFree := rankOneLocalSchemeIso q i (hqrank i).some
    let ePull := (Scheme.Modules.restrictFunctorIsoPullback
      (Scheme.Opens.ι (q.X i))).app M
    let eM : (Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M ≅
        SheafOfModules.unit (q.X i : Scheme.{u}).ringCatSheaf :=
      (eFree ≪≫ ePull).symm ≪≫ freePUnitIsoUnit (q.X i : Scheme.{u})
    letI : IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ q.X i).ι).map
        (modulePullbackTensorMap f M N)) :=
      pullback_modulePullbackTensorMap_isIso_of_iso_on_open f (q.X i) eM
    exact moduleHom_over_isIso_of_pullback (modulePullbackTensorMap f M N)
      (f ⁻¹ᵁ q.X i)

set_option linter.style.haveILetI false in
/-- The canonical pullback tensor comparison is an isomorphism whenever its left factor is an
invertible module sheaf. -/
theorem modulePullbackTensorMap_isIso_of_isInvertible
    (f : Y ⟶ X) {M N : X.Modules} (hM : IsInvertible M) :
    IsIso (modulePullbackTensorMap f M N) := by
  obtain ⟨A, hA, ⟨e⟩⟩ := hM
  let a := (Scheme.Modules.pullback f).map
    (moduleTensorMap e.hom (𝟙 N))
  let b := moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
    ((Scheme.Modules.pullback f).map (𝟙 N))
  let c := modulePullbackTensorMap f A N
  letI : IsIso (moduleTensorMap e.hom (𝟙 N)) :=
    moduleTensorMap_isIso e.hom (𝟙 N)
  letI : IsIso a := by dsimp only [a]; infer_instance
  letI : IsIso ((Scheme.Modules.pullback f).map e.hom) := inferInstance
  letI : IsIso ((Scheme.Modules.pullback f).map (𝟙 N)) := inferInstance
  letI : IsIso b := moduleTensorMap_isIso _ _
  letI : IsIso c := by
    dsimp only [c]
    exact modulePullbackTensorMap_isIso_of_hasRankOneTrivialization f hA
  have hfac : a ≫ c = modulePullbackTensorMap f M N ≫ b := by
    exact modulePullbackTensorMap_naturality f e.hom (𝟙 N)
  haveI : IsIso (a ≫ c) := inferInstance
  exact IsIso.of_isIso_fac_right hfac.symm

/-- Pulling a local rank-one trivialization back to the inverse-image open gives a rank-one
trivialization of the pulled-back module on that open subscheme. -/
def pullbackLocalSchemeIso {M : X.Modules} (f : Y ⟶ X)
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData]
    (i : q.I) (e : (q.generators i).I ≃ ULift.{u, 0} PUnit) :
    SheafOfModules.free (R := (f ⁻¹ᵁ q.X i : Scheme.{u}).ringCatSheaf)
        (ULift.{u, 0} PUnit) ≅
      (Scheme.Modules.restrictFunctor (Scheme.Opens.ι (f ⁻¹ᵁ q.X i))).obj
        ((Scheme.Modules.pullback f).obj M) :=
  (schemePullbackFreeIso (f ∣_ q.X i) (ULift.{u, 0} PUnit)).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ q.X i)).mapIso
      (rankOneLocalSchemeIso q i e) ≪≫
    (modulePullbackRestrictIso f (q.X i) M).symm

/-- Transport an explicit free rank-one trivialization on an open subscheme back to the
corresponding over-site. -/
def overIsoOfSchemeRestrictIso {M : X.Modules} (U : X.Opens)
    (e : SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf)
          (ULift.{u, 0} PUnit) ≅
        (Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).obj M) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} PUnit) ≅
      M.over U :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    (overEquivFreePUnitIso U ≪≫ e ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app M).symm)

/-- The pullback of one local rank-one trivialization, expressed on the source over-site. -/
def pullbackLocalOverIso {M : X.Modules} (f : Y ⟶ X)
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData]
    (i : q.I) (e : (q.generators i).I ≃ ULift.{u, 0} PUnit) :
    SheafOfModules.free (R := Y.ringCatSheaf.over (f ⁻¹ᵁ q.X i))
        (ULift.{u, 0} PUnit) ≅
      ((Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ q.X i) :=
  overIsoOfSchemeRestrictIso (f ⁻¹ᵁ q.X i)
    (pullbackLocalSchemeIso f q i e)

namespace HasRankOneTrivialization

set_option linter.style.haveILetI false in
/-- Rank-one local triviality is preserved by arbitrary scheme pullback. -/
theorem pullback {M : X.Modules} (hM : HasRankOneTrivialization M) (f : Y ⟶ X) :
    HasRankOneTrivialization ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨q, hqfree, hqrank⟩ := hM
  letI : q.IsLocallyFreeData := hqfree
  apply of_freePUnitIso (fun i ↦ f ⁻¹ᵁ q.X i)
  · rw [Opens.coversTop_iff]
    exact f.iSup_preimage_eq_top ((Opens.coversTop_iff X q.X).mp q.coversTop)
  · intro i
    exact pullbackLocalOverIso f q i (hqrank i).some

end HasRankOneTrivialization

namespace IsInvertible

/-- Invertible module sheaves remain invertible after arbitrary scheme pullback. -/
theorem pullback {M : X.Modules} (hM : IsInvertible M) (f : Y ⟶ X) :
    IsInvertible ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨A, hA, ⟨e⟩⟩ := hM
  exact ⟨(Scheme.Modules.pullback f).obj A,
    HasRankOneTrivialization.pullback hA f,
    ⟨(Scheme.Modules.pullback f).mapIso e⟩⟩

end IsInvertible

/-- Associativity of the genuine sheaf tensor product when the outer factors are invertible.
The comparison from sheafifying a raw tensor to tensoring a sheafification supplies the two
non-formal steps; the middle step is the presheaf tensor associator. -/
def moduleTensorAssocIso (M N P : X.Modules)
    (hM : IsInvertible M) (hP : IsInvertible P) :
    moduleTensor (moduleTensor M N) P ≅ moduleTensor M (moduleTensor N P) := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  letI : SymmetricCategory X.PresheafOfModules :=
    PresheafOfModules.symmetricCategory (R := X.sheaf.obj)
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let QMN := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M.val N.val
  let QNP := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) N.val P.val
  let cLeft := moduleTensorSheafificationRightComparison QMN P
  let cRight := moduleTensorSheafificationRightComparison QNP M
  letI : IsIso cLeft :=
    moduleTensorSheafificationRightComparison_isIso_of_isInvertible QMN hP
  letI : IsIso cRight :=
    moduleTensorSheafificationRightComparison_isIso_of_isInvertible QNP hM
  have hcLeft : IsIso cLeft := inferInstance
  have hcRight : IsIso cRight := inferInstance
  exact (@asIso _ _ _ _ cLeft hcLeft).symm |>.trans
    (L.mapIso (associator M.val N.val P.val)) |>.trans
    (L.mapIso (braiding M.val QNP)) |>.trans
    (@asIso _ _ _ _ cRight hcRight) |>.trans
    (moduleTensorCommIso (moduleTensor N P) M)

/-! ## Dual module sheaves -/

/-- Local dual sections over an open subset: module morphisms from the restriction of `M` to
the restricted structure sheaf. -/
abbrev localDualSections (M : X.Modules) (U : X.Opens) :=
  M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)

set_option maxHeartbeats 800000 in
-- Naturality for the sectionwise scalar action requires substantial categorical elaboration.
set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication on the target makes local dual sections into a module over functions on the
open subset. -/
noncomputable def localDualSmul (M : X.Modules) (U : X.Opens)
    (r : X.sheaf.obj.obj (Opposite.op U))
    (φ : localDualSections M U) : localDualSections M U where
  val :=
    { app := fun V => by
        exact ModuleCat.ofHom
          { toFun := fun m =>
              X.sheaf.obj.map V.unop.hom.op r • φ.val.app V m
            map_add' := by simp [mul_add]
            map_smul' := by
              intro a m
              dsimp
              rw [map_smul]
              simp only [smul_eq_mul]
              exact mul_left_comm
                (X.sheaf.obj.map V.unop.hom.op r)
                a (φ.val.app V m) }
      naturality := by
        intro V W f
        ext m
        change
          X.sheaf.obj.map W.unop.hom.op r •
              φ.val.app W ((M.over U).val.map f m) =
            (SheafOfModules.unit (X.ringCatSheaf.over U)).val.map f
              (X.sheaf.obj.map V.unop.hom.op r • φ.val.app V m)
        rw [PresheafOfModules.naturality_apply φ.val f m, map_smul]
        congr 1
        change X.sheaf.obj.map W.unop.hom.op r =
          X.sheaf.obj.map f.unop.left.op
            (X.sheaf.obj.map V.unop.hom.op r)
        rw [← CommRingCat.comp_apply, ← X.sheaf.obj.map_comp]
        congr }

@[simp]
lemma localDualSmul_app_apply (M : X.Modules) (U : X.Opens)
    (r : X.sheaf.obj.obj (Opposite.op U))
    (φ : localDualSections M U) (V : (Over U)ᵒᵖ) (m : (M.over U).val.obj V) :
    (localDualSmul M U r φ).val.app V m =
      X.sheaf.obj.map V.unop.hom.op r *
        (show X.sheaf.obj.obj (Opposite.op V.unop.left) from φ.val.app V m) := rfl

noncomputable instance localDualSMul (M : X.Modules) (U : X.Opens) :
    SMul (X.ringCatSheaf.obj.obj (Opposite.op U)) (localDualSections M U) where
  smul := localDualSmul M U

set_option maxHeartbeats 800000 in
-- The module laws are proved by extensionality through both sheaf and presheaf layers.
set_option backward.isDefEq.respectTransparency false in
noncomputable instance localDualModule (M : X.Modules) (U : X.Opens) :
    Module (X.ringCatSheaf.obj.obj (Opposite.op U)) (localDualSections M U) where
  one_smul φ := by
    ext V m
    change (localDualSmul M U 1 φ).val.app V m = φ.val.app V m
    rw [localDualSmul_app_apply, map_one, one_mul]
  mul_smul r s φ := by
    ext V m
    change (localDualSmul M U (r * s) φ).val.app V m =
      (localDualSmul M U r (localDualSmul M U s φ)).val.app V m
    rw [localDualSmul_app_apply, localDualSmul_app_apply,
      localDualSmul_app_apply, map_mul, mul_assoc]
  smul_zero r := by
    ext V m
    change (localDualSmul M U r 0).val.app V m = 0
    rw [localDualSmul_app_apply]
    change X.sheaf.obj.map V.unop.hom.op r •
      (0 : (SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj V) = 0
    change X.sheaf.obj.map V.unop.hom.op r * 0 = 0
    exact mul_zero _
  smul_add r φ ψ := by
    ext V m
    change (localDualSmul M U r (φ + ψ)).val.app V m =
      (localDualSmul M U r φ + localDualSmul M U r ψ).val.app V m
    rw [localDualSmul_app_apply, SheafOfModules.add_val,
      PresheafOfModules.add_app]
    change X.sheaf.obj.map V.unop.hom.op r •
        (φ.val.app V m + ψ.val.app V m) =
      (localDualSmul M U r φ).val.app V m +
        (localDualSmul M U r ψ).val.app V m
    rw [localDualSmul_app_apply, localDualSmul_app_apply, smul_add]
    simp only [smul_eq_mul]
  add_smul r s φ := by
    ext V m
    change (localDualSmul M U (r + s) φ).val.app V m =
      (localDualSmul M U r φ + localDualSmul M U s φ).val.app V m
    rw [localDualSmul_app_apply, SheafOfModules.add_val,
      PresheafOfModules.add_app]
    change X.sheaf.obj.map V.unop.hom.op (r + s) • φ.val.app V m =
      (localDualSmul M U r φ).val.app V m +
        (localDualSmul M U s φ).val.app V m
    rw [map_add, localDualSmul_app_apply, localDualSmul_app_apply, add_smul]
    simp only [smul_eq_mul]
  zero_smul φ := by
    ext V m
    change (localDualSmul M U 0 φ).val.app V m = 0
    rw [localDualSmul_app_apply, map_zero, zero_mul]

set_option backward.defeqAttrib.useBackward true in
/-- Restriction of a local dual section. -/
noncomputable def localDualRestrict (M : X.Modules) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (φ : localDualSections M U.unop) : localDualSections M V.unop where
  val :=
    { app := fun W => φ.val.app ((Over.map f.unop).op.obj W)
      naturality := fun g => φ.val.naturality ((Over.map f.unop).op.map g) }

@[simp]
lemma localDualRestrict_app_apply (M : X.Modules) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (φ : localDualSections M U.unop) (W : (Over V.unop)ᵒᵖ)
    (m : (M.over V.unop).val.obj W) :
    (localDualRestrict M f φ).val.app W m =
      φ.val.app ((Over.map f.unop).op.obj W) m := rfl

set_option maxHeartbeats 800000 in
-- Restriction compatibility unfolds nested over-site maps and module structures.
set_option backward.isDefEq.respectTransparency false in
lemma localDualRestrict_smul (M : X.Modules) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (r : X.sheaf.obj.obj U) (φ : localDualSections M U.unop) :
    localDualRestrict M f (localDualSmul M U.unop r φ) =
      localDualSmul M V.unop (X.sheaf.obj.map f r) (localDualRestrict M f φ) := by
  ext W m
  change
    (localDualSmul M U.unop r φ).val.app ((Over.map f.unop).op.obj W) m =
      (localDualSmul M V.unop (X.sheaf.obj.map f r)
        (localDualRestrict M f φ)).val.app W m
  rw [localDualSmul_app_apply, localDualSmul_app_apply]
  change (show X.sheaf.obj.obj (Opposite.op W.unop.left) from
      X.sheaf.obj.map (((Over.map f.unop).obj W.unop).hom).op r) *
      (show X.sheaf.obj.obj (Opposite.op W.unop.left) from
        φ.val.app ((Over.map f.unop).op.obj W) m) =
    X.sheaf.obj.map W.unop.hom.op (X.sheaf.obj.map f r) *
      (show X.sheaf.obj.obj (Opposite.op W.unop.left) from
        φ.val.app ((Over.map f.unop).op.obj W) m)
  congr 1
  rw [← CommRingCat.comp_apply, ← X.sheaf.obj.map_comp]
  rfl

/-- The local dual sections over an open, bundled as a module over functions on that open. -/
noncomputable def localDualModuleCat (M : X.Modules) (U : (Opens X)ᵒᵖ) :
    ModuleCat.{u} (X.ringCatSheaf.obj.obj U) := by
  letI := localDualModule M U.unop
  exact ModuleCat.of (X.ringCatSheaf.obj.obj U) (localDualSections M U.unop)

set_option maxHeartbeats 800000 in
-- Assembling the dual presheaf requires checking nested module-valued functor laws.
set_option backward.isDefEq.respectTransparency false in
/-- The module presheaf of local linear maps from `M` to the structure sheaf. -/
noncomputable def moduleDualPresheaf (M : X.Modules) : X.PresheafOfModules where
  obj U := localDualModuleCat M U
  map {U V} f := by
    letI := localDualModule M U.unop
    letI := localDualModule M V.unop
    exact ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
        (localDualModuleCat M V))
      { toFun := localDualRestrict M f
        map_add' := by
          intro φ ψ
          change localDualRestrict M f (φ + ψ) =
            localDualRestrict M f φ + localDualRestrict M f ψ
          ext W m
          rfl
        map_smul' := localDualRestrict_smul M f }
  map_id := by
    rintro ⟨U⟩
    apply ModuleCat.hom_ext
    ext φ
    change localDualRestrict M (𝟙 (Opposite.op U)) φ = φ
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨W⟩
    rfl
  map_comp := by
    rintro ⟨U⟩ ⟨V⟩ ⟨W⟩ f g
    apply ModuleCat.hom_ext
    ext φ
    change localDualRestrict M (f ≫ g) φ =
      localDualRestrict M g (localDualRestrict M f φ)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨T⟩
    rfl

/-- The dual module sheaf, obtained by sheafifying the presheaf of local linear maps. -/
def moduleDual (M : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (moduleDualPresheaf M)

set_option maxHeartbeats 800000 in
-- Constructing the tensor evaluation map elaborates the balanced bilinear universal property.
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a module section against a raw local-dual section on one open subset. -/
noncomputable def moduleDualEvaluationApp (M : X.Modules) (U : (Opens X)ᵒᵖ) :
    (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
      M.val (moduleDualPresheaf M)).obj U ⟶
        (PresheafOfModules.unit X.ringCatSheaf.obj).obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun m φ ↦ φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m)
    (by
      intro m m' φ
      rw [map_add])
    (by
      intro r m φ
      rw [map_smul])
    (by
      intro m φ ψ
      rw [SheafOfModules.add_val, PresheafOfModules.add_app]
      rfl)
    (by
      intro r m φ
      change (localDualSmul M U.unop r φ).val.app
          (Opposite.op (Over.mk (𝟙 U.unop))) m =
        r • φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m
      rw [localDualSmul_app_apply]
      change X.sheaf.obj.map (𝟙 U) r *
          (show X.sheaf.obj.obj U from
            φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m) =
        r • φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m
      have hr := ConcreteCategory.congr_hom (X.sheaf.obj.map_id U) r
      change X.sheaf.obj.map (𝟙 U) r = r at hr
      rw [hr]
      rfl)

@[simp]
lemma moduleDualEvaluationApp_tmul (M : X.Modules) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) (φ : (moduleDualPresheaf M).obj U) :
    (moduleDualEvaluationApp M U).hom (m ⊗ₜ φ) =
      φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m := rfl

set_option maxHeartbeats 800000 in
-- The tensor-generator naturality proof unfolds several over-site restriction maps.
set_option backward.isDefEq.respectTransparency false in
lemma moduleDualEvaluationApp_naturality_tmul (M : X.Modules)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (m : M.val.obj U)
    (φ : (moduleDualPresheaf M).obj U) :
      (moduleDualEvaluationApp M V).hom
          ((PresheafOfModules.Monoidal.tensorObj M.val
            (moduleDualPresheaf M)).map f (m ⊗ₜ φ)) =
        (PresheafOfModules.unit X.ringCatSheaf.obj).map f
          ((moduleDualEvaluationApp M U).hom (m ⊗ₜ φ)) := by
  have hmap := PresheafOfModules.Monoidal.tensorObj_map_tmul
    (R := X.sheaf.obj) (M₁ := M.val) (M₂ := moduleDualPresheaf M) f m φ
  calc
    (moduleDualEvaluationApp M V).hom
        ((PresheafOfModules.Monoidal.tensorObj M.val
          (moduleDualPresheaf M)).map f (m ⊗ₜ φ)) =
      (moduleDualEvaluationApp M V).hom
        (M.val.map f m ⊗ₜ (moduleDualPresheaf M).map f φ) := by
          exact congrArg (fun z ↦ (moduleDualEvaluationApp M V).hom z) hmap
    _ = (PresheafOfModules.unit X.ringCatSheaf.obj).map f
          ((moduleDualEvaluationApp M U).hom (m ⊗ₜ φ)) := by
      rw [moduleDualEvaluationApp_tmul, moduleDualEvaluationApp_tmul]
      change φ.val.app
          ((Over.map f.unop).op.obj (Opposite.op (Over.mk (𝟙 V.unop))))
          (M.val.map f m) =
        X.sheaf.obj.map f
          (φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m)
      let A : Over U.unop := (Over.map f.unop).obj (Over.mk (𝟙 V.unop))
      have h := PresheafOfModules.naturality_apply φ.val
        (Over.mkIdTerminal.from A).op m
      change φ.val.app (Opposite.op A)
          (M.val.map (Over.mkIdTerminal.from A).left.op m) =
        X.sheaf.obj.map (Over.mkIdTerminal.from A).left.op
          (φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m) at h
      rw [Over.mkIdTerminal_from_left] at h
      exact h

set_option maxHeartbeats 800000 in
-- Extending generator naturality to a presheaf morphism uses tensor extensionality.
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation defines a morphism from the objectwise tensor of a module with its raw dual to
the unit module presheaf. -/
noncomputable def moduleDualEvaluationPresheaf (M : X.Modules) :
    PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
        M.val (moduleDualPresheaf M) ⟶
      PresheafOfModules.unit X.ringCatSheaf.obj where
  app U := moduleDualEvaluationApp M U
  naturality {U V} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m φ
    exact moduleDualEvaluationApp_naturality_tmul M f m φ

/-- Evaluation after sheafifying the objectwise tensor of a module with its raw dual. -/
noncomputable def moduleDualEvaluationSheafified (M : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
          M.val (moduleDualPresheaf M)) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (moduleDualEvaluationPresheaf M) ≫
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app (SheafOfModules.unit X.ringCatSheaf)

set_option linter.style.haveILetI false in
/-- The evaluation morphism from an invertible module tensored with its dual to the structure
sheaf.  The comparison between tensoring before and after sheafification is invertible because
the original module is locally free of rank one. -/
noncomputable def moduleDualEvaluation (M : X.Modules) (hM : IsInvertible M) :
    moduleTensor M (moduleDual M) ⟶ SheafOfModules.unit X.ringCatSheaf := by
  let _ := moduleTensorSheafificationRightComparison_isIso_of_isInvertible
    (moduleDualPresheaf M) hM
  let c := moduleTensorSheafificationRightComparison (moduleDualPresheaf M) M
  letI : IsIso c := inferInstance
  let cinv := inv c
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  letI : SymmetricCategory X.PresheafOfModules :=
    PresheafOfModules.symmetricCategory (R := X.sheaf.obj)
  exact (moduleTensorCommIso M (moduleDual M)).hom ≫
    cinv ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (braiding (moduleDualPresheaf M) M.val).hom ≫
    moduleDualEvaluationSheafified M

noncomputable instance localDualUnitModule (U : X.Opens) :
    Module (X.ringCatSheaf.obj.obj (Opposite.op U))
      (localDualSections (SheafOfModules.unit X.ringCatSheaf) U) :=
  localDualModule (SheafOfModules.unit X.ringCatSheaf) U

set_option maxHeartbeats 800000 in
-- The inverse calculation uses nested sheaf extensionality and unit restriction maps.
set_option backward.isDefEq.respectTransparency false in
/-- An endomorphism of the structure sheaf on an open subset is multiplication by its value
at one. -/
noncomputable def localDualUnitLinearEquiv (U : X.Opens) :
    localDualSections (SheafOfModules.unit X.ringCatSheaf) U ≃ₗ[
      X.ringCatSheaf.obj.obj (Opposite.op U)]
      X.ringCatSheaf.obj.obj (Opposite.op U) := by
  letI := localDualModule (SheafOfModules.unit X.ringCatSheaf) U
  exact {
  toFun φ := show X.sheaf.obj.obj (Opposite.op U) from
    φ.val.app (Opposite.op (Over.mk (𝟙 U)))
      (show X.sheaf.obj.obj (Opposite.op U) from 1)
  invFun r := localDualSmul (SheafOfModules.unit X.ringCatSheaf) U r (𝟙 _)
  map_add' φ ψ := by
    change (φ + ψ).val.app (Opposite.op (Over.mk (𝟙 U)))
      (show X.sheaf.obj.obj (Opposite.op U) from 1) = _
    rw [SheafOfModules.add_val, PresheafOfModules.add_app]
    rfl
  map_smul' r φ := by
    change (localDualSmul (SheafOfModules.unit X.ringCatSheaf) U r φ).val.app
      (Opposite.op (Over.mk (𝟙 U)))
        (show X.sheaf.obj.obj (Opposite.op U) from 1) =
      (show X.sheaf.obj.obj (Opposite.op U) from r) *
        (show X.sheaf.obj.obj (Opposite.op U) from
        φ.val.app (Opposite.op (Over.mk (𝟙 U)))
          (show X.sheaf.obj.obj (Opposite.op U) from 1))
    rw [localDualSmul_app_apply]
    change X.sheaf.obj.map (𝟙 (Opposite.op U)) r *
      (show X.sheaf.obj.obj (Opposite.op U) from
        φ.val.app (Opposite.op (Over.mk (𝟙 U)))
          (show X.sheaf.obj.obj (Opposite.op U) from 1)) = _
    have hr := ConcreteCategory.congr_hom
      (X.sheaf.obj.map_id (Opposite.op U))
      (show X.sheaf.obj.obj (Opposite.op U) from r)
    change X.sheaf.obj.map (𝟙 (Opposite.op U)) r = r at hr
    rw [hr]
  left_inv φ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨V⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change
      X.sheaf.obj.map V.hom.op
          (show X.sheaf.obj.obj (Opposite.op U) from
            φ.val.app (Opposite.op (Over.mk (𝟙 U)))
              (show X.sheaf.obj.obj (Opposite.op U) from 1)) *
          (show X.sheaf.obj.obj (Opposite.op V.left) from m) =
        φ.val.app (Opposite.op V) m
    rw [mul_comm]
    have h := PresheafOfModules.naturality_apply φ.val
      (Over.mkIdTerminal.from V).op
      (show X.sheaf.obj.obj (Opposite.op U) from 1)
    have hmap : X.sheaf.obj.map V.hom.op
          (show X.sheaf.obj.obj (Opposite.op U) from
            φ.val.app (Opposite.op (Over.mk (𝟙 U)))
              (show X.sheaf.obj.obj (Opposite.op U) from 1)) =
        (show X.sheaf.obj.obj (Opposite.op V.left) from
          (SheafOfModules.unit (X.ringCatSheaf.over U)).val.map
            (Over.mkIdTerminal.from V).op
            (φ.val.app (Opposite.op (Over.mk (𝟙 U)))
              (show X.sheaf.obj.obj (Opposite.op U) from 1))) := by
      change X.sheaf.obj.map V.hom.op _ =
        X.sheaf.obj.map (Over.mkIdTerminal.from V).left.op _
      rw [Over.mkIdTerminal_from_left]
      rfl
    rw [hmap]
    change
      (show X.sheaf.obj.obj (Opposite.op V.left) from m) *
          (show X.sheaf.obj.obj (Opposite.op V.left) from
            (SheafOfModules.unit (X.ringCatSheaf.over U)).val.map
              (Over.mkIdTerminal.from V).op
              (φ.val.app (Opposite.op (Over.mk (𝟙 U)))
                (show X.sheaf.obj.obj (Opposite.op U) from 1))) =
        (show X.sheaf.obj.obj (Opposite.op V.left) from
          φ.val.app (Opposite.op V) m)
    rw [← h]
    change (show X.sheaf.obj.obj (Opposite.op V.left) from m) •
        (show X.sheaf.obj.obj (Opposite.op V.left) from
          φ.val.app (Opposite.op V)
            (((SheafOfModules.unit X.ringCatSheaf).over U).val.map
              (Over.mkIdTerminal.from V).op
              (show X.sheaf.obj.obj (Opposite.op U) from 1))) = _
    rw [← (φ.val.app (Opposite.op V)).hom.map_smul]
    have hone :
        (((SheafOfModules.unit X.ringCatSheaf).over U).val.map
          (Over.mkIdTerminal.from V).op)
            (show X.sheaf.obj.obj (Opposite.op U) from 1) =
          (show X.sheaf.obj.obj (Opposite.op V.left) from 1) := by
      change ((SheafOfModules.unit (X.ringCatSheaf.over U)).val.map
        (Over.mkIdTerminal.from V).op)
          (show X.sheaf.obj.obj (Opposite.op U) from 1) =
        (show X.sheaf.obj.obj (Opposite.op V.left) from 1)
      exact PresheafOfModules.unit_map_one
        (R := (X.ringCatSheaf.over U).obj) (Over.mkIdTerminal.from V).op
    rw [hone]
    simp only [smul_eq_mul, mul_one]
  right_inv r := by
    change X.sheaf.obj.map (𝟙 (Opposite.op U))
      (show X.sheaf.obj.obj (Opposite.op U) from r) * 1 =
        (show X.sheaf.obj.obj (Opposite.op U) from r)
    have hr := ConcreteCategory.congr_hom
      (X.sheaf.obj.map_id (Opposite.op U))
      (show X.sheaf.obj.obj (Opposite.op U) from r)
    change X.sheaf.obj.map (𝟙 (Opposite.op U)) r = r at hr
    rw [hr, mul_one] }

set_option maxHeartbeats 800000 in
-- Naturality of evaluation at one unfolds terminal objects in two over-sites.
set_option backward.isDefEq.respectTransparency false in
lemma localDualUnitLinearEquiv_naturality {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (φ : localDualSections (SheafOfModules.unit X.ringCatSheaf) U.unop) :
    localDualUnitLinearEquiv V.unop (localDualRestrict _ f φ) =
      X.sheaf.obj.map f (localDualUnitLinearEquiv U.unop φ) := by
  let A : Over U.unop := (Over.map f.unop).obj (Over.mk (𝟙 V.unop))
  have h := PresheafOfModules.naturality_apply φ.val
    (Over.mkIdTerminal.from A).op
    (show X.sheaf.obj.obj U from 1)
  change φ.val.app (Opposite.op A)
      ((((SheafOfModules.unit X.ringCatSheaf).over U.unop).val.map
        (Over.mkIdTerminal.from A).op)
        (show X.sheaf.obj.obj U from 1)) =
    ((SheafOfModules.unit (X.ringCatSheaf.over U.unop)).val.map
      (Over.mkIdTerminal.from A).op)
      (φ.val.app (Opposite.op (Over.mk (𝟙 U.unop)))
        (show X.sheaf.obj.obj U from 1)) at h
  have hone :
      (((SheafOfModules.unit X.ringCatSheaf).over U.unop).val.map
        (Over.mkIdTerminal.from A).op)
          (show X.sheaf.obj.obj U from 1) =
        (show X.sheaf.obj.obj V from 1) := by
    change ((SheafOfModules.unit (X.ringCatSheaf.over U.unop)).val.map
      (Over.mkIdTerminal.from A).op)
        (show X.sheaf.obj.obj U from 1) =
      (show X.sheaf.obj.obj V from 1)
    exact PresheafOfModules.unit_map_one
      (R := (X.ringCatSheaf.over U.unop).obj) (Over.mkIdTerminal.from A).op
  rw [hone] at h
  change φ.val.app (Opposite.op A)
      (show X.sheaf.obj.obj V from 1) =
    X.sheaf.obj.map f
      (show X.sheaf.obj.obj U from
        φ.val.app (Opposite.op (Over.mk (𝟙 U.unop)))
          (show X.sheaf.obj.obj U from 1))
  rw [h]
  change X.sheaf.obj.map (Over.mkIdTerminal.from A).left.op _ =
    X.sheaf.obj.map f _
  rw [Over.mkIdTerminal_from_left]
  rfl

set_option maxHeartbeats 800000 in
-- The presheaf isomorphism packages the sectionwise equivalences and their naturality proof.
set_option backward.isDefEq.respectTransparency false in
/-- The raw dual of the structure sheaf is the unit module presheaf. -/
noncomputable def moduleDualUnitPresheafIso :
    moduleDualPresheaf (SheafOfModules.unit X.ringCatSheaf) ≅
      PresheafOfModules.unit X.ringCatSheaf.obj :=
  PresheafOfModules.isoMk
    (fun U ↦ (localDualUnitLinearEquiv U.unop).toModuleIso)
    (by
      intro U V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      exact localDualUnitLinearEquiv_naturality f φ)

/-- The dual of the structure sheaf is the structure sheaf. -/
noncomputable def moduleDualUnitIso :
    moduleDual (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      moduleDualUnitPresheafIso ≪≫
    moduleSheafificationCounitIso (SheafOfModules.unit X.ringCatSheaf)

set_option maxHeartbeats 800000 in
-- Precomposition is checked through the full sheaf-of-modules morphism hierarchy.
set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with an isomorphism identifies the corresponding local dual modules. -/
noncomputable def localDualPrecompLinearEquiv {M N : X.Modules} (U : X.Opens)
    (e : M.over U ≅ N.over U) :
    localDualSections N U ≃ₗ[X.ringCatSheaf.obj.obj (Opposite.op U)]
      localDualSections M U := by
  letI := localDualModule M U
  letI := localDualModule N U
  exact {
    toFun φ := e.hom ≫ φ
    invFun φ := e.inv ≫ φ
    map_add' φ ψ := by
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro V
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      rfl
    map_smul' r φ := by
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro V
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      rfl
    left_inv φ := by simp
    right_inv φ := by simp }

/-- Restrict an isomorphism on an open subset to any smaller open subset. -/
noncomputable def restrictOverIso {M N : X.Modules} {U : X.Opens}
    (e : M.over U ≅ N.over U) (V : Over U) :
    M.over V.left ≅ N.over V.left :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app M).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf V.hom).mapIso e ≪≫
      (SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app N

/-- A trivialization of a module on an open subset identifies its local dual sections with
functions on that open subset. -/
noncomputable def localDualLinearEquivOfIsoUnit {M : X.Modules} (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    localDualSections M U ≃ₗ[X.ringCatSheaf.obj.obj (Opposite.op U)]
      X.ringCatSheaf.obj.obj (Opposite.op U) :=
  (localDualPrecompLinearEquiv U e).symm.trans (localDualUnitLinearEquiv U)

set_option maxHeartbeats 800000 in
-- Restricting a trivialization requires comparing nested over-site functors objectwise.
set_option backward.isDefEq.respectTransparency false in
/-- On an open subset where `M` is trivial, its raw dual presheaf restricts to the unit
presheaf. -/
noncomputable def moduleDualPresheafOverIsoOfIsoUnit {M : X.Modules} (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    modulePresheafOver (moduleDualPresheaf M) U ≅
      PresheafOfModules.unit (X.ringCatSheaf.over U).obj :=
  PresheafOfModules.isoMk
    (fun V ↦
      (localDualLinearEquivOfIsoUnit V.unop.left
        (restrictOverIso e V.unop)).toModuleIso)
    (by
      intro A B f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      let C : Over A.unop.left :=
        (Over.map f.unop.left).obj (Over.mk (𝟙 B.unop.left))
      change φ.val.app (Opposite.op C)
          (e.inv.val.app B
            (show X.sheaf.obj.obj (Opposite.op B.unop.left) from 1)) =
        (X.ringCatSheaf.over U).obj.map f
          (φ.val.app (Opposite.op (Over.mk (𝟙 A.unop.left)))
            (e.inv.val.app A
              (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1)))
      have he := PresheafOfModules.naturality_apply e.inv.val f
        (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1)
      have hφ := PresheafOfModules.naturality_apply φ.val
        (Over.mkIdTerminal.from C).op
        (e.inv.val.app A
          (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1))
      change e.inv.val.app B
          (((SheafOfModules.unit X.ringCatSheaf).over U).val.map f
            (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1)) =
        (M.over U).val.map f
          (e.inv.val.app A
            (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1)) at he
      have hone : (((SheafOfModules.unit X.ringCatSheaf).over U).val.map f
          (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1)) =
        (show X.sheaf.obj.obj (Opposite.op B.unop.left) from 1) := by
        change ((SheafOfModules.unit (X.ringCatSheaf.over U)).val.map f)
          (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1) =
            (show X.sheaf.obj.obj (Opposite.op B.unop.left) from 1)
        exact PresheafOfModules.unit_map_one
          (R := (X.ringCatSheaf.over U).obj) f
      rw [hone] at he
      change φ.val.app (Opposite.op C)
          ((M.over A.unop.left).val.map (Over.mkIdTerminal.from C).op
            (e.inv.val.app A
              (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1))) =
        (SheafOfModules.unit (X.ringCatSheaf.over A.unop.left)).val.map
          (Over.mkIdTerminal.from C).op
          (φ.val.app (Opposite.op (Over.mk (𝟙 A.unop.left)))
            (e.inv.val.app A
              (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1))) at hφ
      have hmor : ((Over.forget U).op.map f) =
          ((Over.forget A.unop.left).op.map
            (Over.mkIdTerminal.from C).op) := by
        apply Quiver.Hom.unop_inj
        change f.unop.left = (Over.mkIdTerminal.from C).left
        rw [Over.mkIdTerminal_from_left]
        rfl
      have hMmap : (M.over U).val.map f
            (e.inv.val.app A
              (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1)) =
          (M.over A.unop.left).val.map (Over.mkIdTerminal.from C).op
            (e.inv.val.app A
              (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1)) := by
        change M.val.map ((Over.forget U).op.map f) _ =
          M.val.map ((Over.forget A.unop.left).op.map
            (Over.mkIdTerminal.from C).op) _
        rw [hmor]
        rfl
      have hOmap :
          (SheafOfModules.unit (X.ringCatSheaf.over A.unop.left)).val.map
              (Over.mkIdTerminal.from C).op
              (φ.val.app (Opposite.op (Over.mk (𝟙 A.unop.left)))
                (e.inv.val.app A
                  (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1))) =
            (X.ringCatSheaf.over U).obj.map f
              (φ.val.app (Opposite.op (Over.mk (𝟙 A.unop.left)))
                (e.inv.val.app A
                  (show X.sheaf.obj.obj (Opposite.op A.unop.left) from 1))) := by
        change X.sheaf.obj.map
            ((Over.forget A.unop.left).op.map
              (Over.mkIdTerminal.from C).op) _ =
          X.sheaf.obj.map ((Over.forget U).op.map f) _
        rw [hmor]
        rfl
      rw [he, hMmap, hφ, hOmap])

/-- The sheaf dual is trivial on every open subset where the original module is trivial. -/
noncomputable def moduleDualOverIsoOfIsoUnit {M : X.Modules} (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (moduleDual M).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  moduleSheafificationOverIso (moduleDualPresheaf M) U ≪≫
    (PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over U).obj)).mapIso
        (moduleDualPresheafOverIsoOfIsoUnit U e) ≪≫
      moduleSheafificationCounitOverIso
        (SheafOfModules.unit (X.ringCatSheaf.over U))

set_option maxHeartbeats 800000 in
-- The rank-one tensor equivalence expands two transported module isomorphisms.
set_option backward.isDefEq.respectTransparency false in
/-- On a trivializing open, objectwise evaluation against the raw dual is the standard
rank-one tensor pairing. -/
noncomputable def moduleDualEvaluationAppIsoOfIsoUnit
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
      M.val (moduleDualPresheaf M)).obj (Opposite.op U) ≅
        (PresheafOfModules.unit X.ringCatSheaf.obj).obj (Opposite.op U) := by
  let eM : M.val.obj (Opposite.op U) ≅
      (PresheafOfModules.unit X.ringCatSheaf.obj).obj (Opposite.op U) :=
    { hom := e.hom.val.app (Opposite.op (Over.mk (𝟙 U)))
      inv := e.inv.val.app (Opposite.op (Over.mk (𝟙 U)))
      hom_inv_id := by
        change e.hom.val.app (Opposite.op (Over.mk (𝟙 U))) ≫
          e.inv.val.app (Opposite.op (Over.mk (𝟙 U))) = 𝟙 _
        rw [← PresheafOfModules.comp_app]
        change (e.hom ≫ e.inv).val.app (Opposite.op (Over.mk (𝟙 U))) = _
        rw [e.hom_inv_id]
        rfl
      inv_hom_id := by
        change e.inv.val.app (Opposite.op (Over.mk (𝟙 U))) ≫
          e.hom.val.app (Opposite.op (Over.mk (𝟙 U))) = 𝟙 _
        rw [← PresheafOfModules.comp_app]
        change (e.inv ≫ e.hom).val.app (Opposite.op (Over.mk (𝟙 U))) = _
        rw [e.inv_hom_id]
        rfl }
  let eD : (moduleDualPresheaf M).obj (Opposite.op U) ≅
      (PresheafOfModules.unit X.ringCatSheaf.obj).obj (Opposite.op U) :=
    (localDualLinearEquivOfIsoUnit U e).toModuleIso
  exact (eM ⊗ᵢ eD) ≪≫ λ_ _

set_option maxHeartbeats 800000 in
-- Computing the transported tensor pairing requires multiple module and sheaf extensionality steps.
set_option backward.isDefEq.respectTransparency false in
lemma moduleDualEvaluationAppIsoOfIsoUnit_hom_tmul
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (m : M.val.obj (Opposite.op U))
    (φ : (moduleDualPresheaf M).obj (Opposite.op U)) :
    (moduleDualEvaluationAppIsoOfIsoUnit M U e).hom.hom (m ⊗ₜ φ) =
      (moduleDualEvaluationApp M (Opposite.op U)).hom (m ⊗ₜ φ) := by
  rw [moduleDualEvaluationApp_tmul]
  change (show X.sheaf.obj.obj (Opposite.op U) from
      e.hom.val.app (Opposite.op (Over.mk (𝟙 U))) m) *
      (show X.sheaf.obj.obj (Opposite.op U) from
        φ.val.app (Opposite.op (Over.mk (𝟙 U)))
          (e.inv.val.app (Opposite.op (Over.mk (𝟙 U)))
            (show X.sheaf.obj.obj (Opposite.op U) from 1))) =
    (show X.sheaf.obj.obj (Opposite.op U) from
      φ.val.app (Opposite.op (Over.mk (𝟙 U))) m)
  let a : X.sheaf.obj.obj (Opposite.op U) :=
    e.hom.val.app (Opposite.op (Over.mk (𝟙 U))) m
  let g : M.val.obj (Opposite.op U) :=
    e.inv.val.app (Opposite.op (Over.mk (𝟙 U)))
      (show X.sheaf.obj.obj (Opposite.op U) from 1)
  let b : X.sheaf.obj.obj (Opposite.op U) :=
    φ.val.app (Opposite.op (Over.mk (𝟙 U))) g
  let p : X.sheaf.obj.obj (Opposite.op U) :=
    φ.val.app (Opposite.op (Over.mk (𝟙 U))) m
  change a * b = p
  have hg : a • g = m := by
    dsimp only [a, g]
    rw [← (e.inv.val.app
      (Opposite.op (Over.mk (𝟙 U)))).hom.map_smul]
    simp only [smul_eq_mul, mul_one]
    have he := ConcreteCategory.congr_hom
      (PresheafOfModules.comp_app e.hom.val e.inv.val
        (Opposite.op (Over.mk (𝟙 U)))) m
    change e.inv.val.app (Opposite.op (Over.mk (𝟙 U)))
        (e.hom.val.app (Opposite.op (Over.mk (𝟙 U))) m) =
      (e.hom ≫ e.inv).val.app (Opposite.op (Over.mk (𝟙 U))) m at he
    rw [he, e.hom_inv_id]
    rfl
  have hφ : (show X.sheaf.obj.obj (Opposite.op U) from
      φ.val.app (Opposite.op (Over.mk (𝟙 U))) (a • g)) = a * b := by
    have h := (φ.val.app
      (Opposite.op (Over.mk (𝟙 U)))).hom.map_smul a g
    change φ.val.app (Opposite.op (Over.mk (𝟙 U))) (a • g) =
      a • (show X.sheaf.obj.obj (Opposite.op U) from
        φ.val.app (Opposite.op (Over.mk (𝟙 U))) g) at h
    simpa only [b, smul_eq_mul] using h
  calc
    a * b = (show X.sheaf.obj.obj (Opposite.op U) from
        φ.val.app (Opposite.op (Over.mk (𝟙 U))) (a • g)) := hφ.symm
    _ = p := by rw [hg]

set_option maxHeartbeats 800000 in
-- Tensor extensionality identifies evaluation with the explicit rank-one isomorphism.
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation is objectwise invertible on every open where the module is trivial. -/
theorem moduleDualEvaluationApp_isIso_of_isoUnit
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    IsIso (moduleDualEvaluationApp M (Opposite.op U)) := by
  let d := moduleDualEvaluationAppIsoOfIsoUnit M U e
  have h : moduleDualEvaluationApp M (Opposite.op U) = d.hom := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m φ
    exact (moduleDualEvaluationAppIsoOfIsoUnit_hom_tmul M U e m φ).symm
  rw [h]
  infer_instance

/-- The underlying additive-presheaf evaluation map. -/
abbrev moduleDualEvaluationAdd (M : X.Modules) :=
  (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
    (moduleDualEvaluationPresheaf M)

set_option linter.style.haveILetI false in
set_option maxHeartbeats 800000 in
-- The local-surjectivity proof unfolds sheafification and cover membership at each point.
set_option backward.isDefEq.respectTransparency false in
/-- A cover by rank-one trivializations makes raw evaluation locally surjective. -/
theorem moduleDualEvaluationAdd_isLocallySurjective_of_cover
    (M : X.Modules) {I : Type u} (Q : I → X.Opens)
    (hQ : (Opens.grothendieckTopology X).CoversTop Q)
    (eQ : ∀ i, M.over (Q i) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (Q i)) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (moduleDualEvaluationAdd M) := by
  rw [Opens.coversTop_iff] at hQ
  constructor
  intro U s
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  have hxQ : x ∈ iSup Q := by rw [hQ]; trivial
  rw [Opens.mem_iSup] at hxQ
  obtain ⟨i, hxi⟩ := hxQ
  let W : X.Opens := U ⊓ Q i
  let f : W ⟶ U := homOfLE inf_le_left
  let V : Over (Q i) := Over.mk (homOfLE inf_le_right : W ⟶ Q i)
  let eW : M.over W ≅ (SheafOfModules.unit X.ringCatSheaf).over W :=
    restrictOverIso (eQ i) V
  letI : IsIso (moduleDualEvaluationApp M (Opposite.op W)) :=
    moduleDualEvaluationApp_isIso_of_isoUnit M W eW
  haveI : IsIso ((moduleDualEvaluationAdd M).app (Opposite.op W)) := by
    change IsIso ((forget₂
      (ModuleCat (X.sheaf.obj.obj (Opposite.op W))) AddCommGrpCat).map
        (moduleDualEvaluationApp M (Opposite.op W)))
    infer_instance
  refine ⟨W, f, ?_, ⟨hx, hxi⟩⟩
  let t := ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj
    (PresheafOfModules.unit X.ringCatSheaf.obj)).map f.op s
  refine ⟨inv ((moduleDualEvaluationAdd M).app (Opposite.op W)) t, ?_⟩
  exact IsIso.inv_hom_id_apply
    ((moduleDualEvaluationAdd M).app (Opposite.op W)) t

set_option linter.style.haveILetI false in
set_option maxHeartbeats 800000 in
-- The local-injectivity proof compares restriction naturality through the additive forgetful functor.
set_option backward.isDefEq.respectTransparency false in
/-- A cover by rank-one trivializations makes raw evaluation locally injective. -/
theorem moduleDualEvaluationAdd_isLocallyInjective_of_cover
    (M : X.Modules) {I : Type u} (Q : I → X.Opens)
    (hQ : (Opens.grothendieckTopology X).CoversTop Q)
    (eQ : ∀ i, M.over (Q i) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (Q i)) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (moduleDualEvaluationAdd M) := by
  rw [Opens.coversTop_iff] at hQ
  constructor
  intro U m n hmn
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  have hxQ : x ∈ iSup Q := by rw [hQ]; trivial
  rw [Opens.mem_iSup] at hxQ
  obtain ⟨i, hxi⟩ := hxQ
  let W : X.Opens := U.unop ⊓ Q i
  let f : W ⟶ U.unop := homOfLE inf_le_left
  let V : Over (Q i) := Over.mk (homOfLE inf_le_right : W ⟶ Q i)
  let eW : M.over W ≅ (SheafOfModules.unit X.ringCatSheaf).over W :=
    restrictOverIso (eQ i) V
  letI : IsIso (moduleDualEvaluationApp M (Opposite.op W)) :=
    moduleDualEvaluationApp_isIso_of_isoUnit M W eW
  haveI : IsIso ((moduleDualEvaluationAdd M).app (Opposite.op W)) := by
    change IsIso ((forget₂
      (ModuleCat (X.sheaf.obj.obj (Opposite.op W))) AddCommGrpCat).map
        (moduleDualEvaluationApp M (Opposite.op W)))
    infer_instance
  refine ⟨W, f, ?_, ⟨hx, hxi⟩⟩
  apply (Function.Bijective.injective (by
    rw [bijective_iff_isIso_ofHom]
    infer_instance) : Function.Injective
      ((moduleDualEvaluationAdd M).app (Opposite.op W)))
  exact (NatTrans.naturality_apply
    (moduleDualEvaluationAdd M) f.op m).trans
      ((congrArg (fun z ↦
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj
          (PresheafOfModules.unit X.ringCatSheaf.obj)).map f.op z) hmn).trans
        (NatTrans.naturality_apply
          (moduleDualEvaluationAdd M) f.op n).symm)

set_option linter.style.haveILetI false in
set_option maxHeartbeats 800000 in
-- Relating local bijectivity to the sheafified map needs several reflected-isomorphism instances.
set_option backward.isDefEq.respectTransparency false in
/-- Sheafification sends a locally bijective raw evaluation morphism to an isomorphism. -/
theorem moduleDualEvaluationSheafificationMap_isIso
    (M : X.Modules)
    (hinj : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (moduleDualEvaluationAdd M))
    (hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (moduleDualEvaluationAdd M)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (moduleDualEvaluationPresheaf M)) := by
  letI : (Opens.grothendieckTopology X).HasSheafCompose
      (forget AddCommGrpCat.{u}) := by
    apply CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.toSheaf X.ringCatSheaf)]
  apply (Sheaf.isLocallyBijective_iff_isIso
    (J := Opens.grothendieckTopology X)
    (A := AddCommGrpCat.{u})
    ((SheafOfModules.toSheaf X.ringCatSheaf).map
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (moduleDualEvaluationPresheaf M)))).mp
  constructor
  · apply (Presheaf.isLocallyInjective_presheafToSheaf_map_iff
      (J := Opens.grothendieckTopology X)
      (moduleDualEvaluationAdd M)).mpr
    exact hinj
  · apply (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      (J := Opens.grothendieckTopology X)
      (moduleDualEvaluationAdd M)).mpr
    exact hsurj

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1200000 in
-- Building the coverwise trivializations and both locality witnesses is elaboration intensive.
set_option backward.isDefEq.respectTransparency false in
/-- If a module has rank-one local trivializations, its sheafified evaluation pairing is an
isomorphism. -/
theorem moduleDualEvaluationSheafified_isIso_of_hasRankOneTrivialization
    {M : X.Modules} (hM : HasRankOneTrivialization M) :
    IsIso (moduleDualEvaluationSheafified M) := by
  obtain ⟨q, hqfree, hqrank⟩ := hM
  letI : q.IsLocallyFreeData := hqfree
  let eQ (i : q.I) : M.over (q.X i) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (q.X i) := by
    letI : IsIso (q.generators i).π :=
      SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso i
    exact (asIso (q.generators i).π).symm ≪≫
      freeOverEquivIso (hqrank i).some ≪≫
        freePUnitOverIsoUnit (q.X i)
  have hinj := moduleDualEvaluationAdd_isLocallyInjective_of_cover
    M q.X q.coversTop eQ
  have hsurj := moduleDualEvaluationAdd_isLocallySurjective_of_cover
    M q.X q.coversTop eQ
  letI : IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (moduleDualEvaluationPresheaf M)) :=
    moduleDualEvaluationSheafificationMap_isIso M hinj hsurj
  dsimp only [moduleDualEvaluationSheafified]
  infer_instance

namespace HasRankOneTrivialization

set_option linter.style.haveILetI false in
/-- Rank-one local triviality is invariant under isomorphism of module sheaves. -/
theorem of_iso {M N : X.Modules} (hM : HasRankOneTrivialization M) (e : M ≅ N) :
    HasRankOneTrivialization N := by
  obtain ⟨q, hqfree, hqrank⟩ := hM
  letI : q.IsLocallyFreeData := hqfree
  apply of_freePUnitIso q.X q.coversTop
  intro i
  letI : IsIso (q.generators i).π :=
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso i
  exact (freeOverEquivIso (hqrank i).some).symm ≪≫
    asIso (q.generators i).π ≪≫
      (SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e

set_option linter.style.haveILetI false in
/-- The sheaf dual of a module with rank-one local trivializations again has rank-one local
trivializations. -/
theorem dual {M : X.Modules} (hM : HasRankOneTrivialization M) :
    HasRankOneTrivialization (moduleDual M) := by
  obtain ⟨q, hqfree, hqrank⟩ := hM
  letI : q.IsLocallyFreeData := hqfree
  apply of_freePUnitIso q.X q.coversTop
  intro i
  letI : IsIso (q.generators i).π :=
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso i
  let eM : M.over (q.X i) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (q.X i) :=
    (asIso (q.generators i).π).symm ≪≫
      freeOverEquivIso (hqrank i).some ≪≫
        freePUnitOverIsoUnit (q.X i)
  exact freePUnitOverIsoUnit (q.X i) ≪≫
    (moduleDualOverIsoOfIsoUnit (q.X i) eM).symm

end HasRankOneTrivialization

namespace IsInvertible

/-- The sheaf dual of an invertible module sheaf is invertible. -/
theorem dual {M : X.Modules} (hM : IsInvertible M) : IsInvertible (moduleDual M) := by
  obtain ⟨A, hA, ⟨e⟩⟩ := hM
  have hM' : HasRankOneTrivialization M :=
    HasRankOneTrivialization.of_iso hA e.symm
  exact ⟨moduleDual M, HasRankOneTrivialization.dual hM', ⟨Iso.refl _⟩⟩

end IsInvertible

set_option linter.style.haveILetI false in
/-- Evaluation identifies an invertible module tensored with its dual with the structure
sheaf. -/
theorem moduleDualEvaluation_isIso {M : X.Modules} (hM : IsInvertible M) :
    IsIso (moduleDualEvaluation M hM) := by
  have hMcopy := hM
  obtain ⟨A, hA, ⟨e⟩⟩ := hMcopy
  have hM' : HasRankOneTrivialization M :=
    HasRankOneTrivialization.of_iso hA e.symm
  letI : IsIso (moduleDualEvaluationSheafified M) :=
    moduleDualEvaluationSheafified_isIso_of_hasRankOneTrivialization hM'
  let _ := moduleTensorSheafificationRightComparison_isIso_of_isInvertible
    (moduleDualPresheaf M) hM
  let c := moduleTensorSheafificationRightComparison (moduleDualPresheaf M) M
  letI : IsIso c := inferInstance
  let ec := asIso c
  let ev := moduleDualEvaluationSheafified M
  letI : IsIso ev := inferInstance
  let eev := asIso ev
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  letI : SymmetricCategory X.PresheafOfModules :=
    PresheafOfModules.symmetricCategory (R := X.sheaf.obj)
  let eb := (PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).mapIso (braiding (moduleDualPresheaf M) M.val)
  let total := moduleTensorCommIso M (moduleDual M) ≪≫
    ec.symm ≪≫ eb ≪≫ eev
  have h : moduleDualEvaluation M hM = total.hom := rfl
  rw [h]
  exact total.isIso_hom

/-- A line bundle is an actual rank-one locally-free sheaf. -/
structure LineBundle (X : Scheme.{u}) where
  obj : X.Modules
  isInvertible : IsInvertible obj

namespace LineBundle

variable (L : LineBundle X)

/-- The globally trivial line bundle. -/
def trivial (X : Scheme.{u}) : LineBundle X where
  obj := SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u, 0} PUnit)
  isInvertible := IsInvertible.free_punit X

/-- Isomorphisms of line bundles are isomorphisms of their underlying module sheaves. -/
abbrev Iso (L M : LineBundle X) := L.obj ≅ M.obj

/-- Pullback of a line bundle along an arbitrary scheme morphism. -/
def pullback (f : Y ⟶ X) : LineBundle Y where
  obj := (Scheme.Modules.pullback f).obj L.obj
  isInvertible := IsInvertible.pullback L.isInvertible f

/-- The underlying module of a pulled-back line bundle is definitionally the Mathlib module
pullback. -/
@[simp]
theorem pullback_obj (f : Y ⟶ X) : (L.pullback f).obj =
    (Scheme.Modules.pullback f).obj L.obj := rfl

/-- Iterated line-bundle pullback has the canonical underlying module isomorphism. -/
def pullbackPullbackIso (f : Y ⟶ X) (g : Z ⟶ Y) :
    LineBundle.Iso ((L.pullback f).pullback g) (L.pullback (g ≫ f)) :=
  (Scheme.Modules.pullbackComp g f).app L.obj

/-- Tensor product of line bundles, using the genuine sheaf tensor product. -/
def tensor (L M : LineBundle X) : LineBundle X where
  obj := moduleTensor L.obj M.obj
  isInvertible := IsInvertible.tensor L.isInvertible M.isInvertible

/-- The dual line bundle. -/
def dual (L : LineBundle X) : LineBundle X where
  obj := moduleDual L.obj
  isInvertible := IsInvertible.dual L.isInvertible

/-- The underlying module of the dual line bundle is definitionally the sheaf dual. -/
@[simp]
theorem dual_obj (L : LineBundle X) : L.dual.obj = moduleDual L.obj := rfl

/-- The underlying module of the tensor product is definitionally the genuine sheaf tensor
product. -/
@[simp]
theorem tensor_obj (L M : LineBundle X) : (L.tensor M).obj = moduleTensor L.obj M.obj := rfl

/-- Pullback commutes with tensor product of line bundles. -/
def pullbackTensorIso (f : Y ⟶ X) (L M : LineBundle X) :
    ((L.tensor M).pullback f).Iso ((L.pullback f).tensor (M.pullback f)) := by
  change (Scheme.Modules.pullback f).obj (moduleTensor L.obj M.obj) ≅
    moduleTensor ((Scheme.Modules.pullback f).obj L.obj)
      ((Scheme.Modules.pullback f).obj M.obj)
  letI : IsIso (modulePullbackTensorMap f L.obj M.obj) :=
    modulePullbackTensorMap_isIso_of_isInvertible f L.isInvertible
  exact asIso (modulePullbackTensorMap f L.obj M.obj)

/-- Pullback of the trivial line bundle is trivial. -/
def pullbackTrivialIso (f : Y ⟶ X) :
    (trivial X).pullback f |>.Iso (trivial Y) :=
  schemePullbackFreeIso f (ULift.{u, 0} PUnit)

/-- Isomorphisms in each factor induce an isomorphism of tensor-product line bundles. -/
def tensorMapIso {L L' M M' : LineBundle X} (eL : L.Iso L') (eM : M.Iso M') :
    (L.tensor M).Iso (L'.tensor M') :=
  moduleTensorMapIso eL eM

/-- Tensor product of line bundles is symmetric. -/
def tensorCommIso (L M : LineBundle X) : (L.tensor M).Iso (M.tensor L) :=
  moduleTensorCommIso L.obj M.obj

/-- Tensor product of line bundles is associative up to the canonical sheafification
comparison. -/
def tensorAssocIso (L M N : LineBundle X) :
    ((L.tensor M).tensor N).Iso (L.tensor (M.tensor N)) :=
  moduleTensorAssocIso L.obj M.obj N.obj L.isInvertible N.isInvertible

/-- The trivial line bundle is a left unit for tensor product. -/
def trivialTensorIso (L : LineBundle X) : (trivial X).tensor L |>.Iso L :=
  moduleTensorMapIso (freePUnitIsoUnit X) (Iso.refl L.obj) ≪≫
    moduleTensorLeftUnitIso L.obj

/-- The trivial line bundle is a right unit for tensor product. -/
def tensorTrivialIso (L : LineBundle X) : (L.tensor (trivial X)).Iso L :=
  moduleTensorMapIso (Iso.refl L.obj) (freePUnitIsoUnit X) ≪≫
    moduleTensorRightUnitIso L.obj

/-- A line bundle tensored with its dual is trivial. -/
noncomputable def tensorDualIso (L : LineBundle X) :
    (L.tensor L.dual).Iso (trivial X) := by
  let ev := moduleDualEvaluation L.obj L.isInvertible
  exact (@asIso _ _ _ _ ev
      (moduleDualEvaluation_isIso L.isInvertible)) ≪≫
    (freePUnitIsoUnit X).symm

/-- The dual of a line bundle tensored with the original line bundle is trivial. -/
noncomputable def dualTensorIso (L : LineBundle X) :
    (L.dual.tensor L).Iso (trivial X) :=
  tensorCommIso L.dual L ≪≫ tensorDualIso L

/-- The nonnegative tensor powers of a line bundle. -/
def tensorPow (L : LineBundle X) : ℕ → LineBundle X
  | 0 => trivial X
  | n + 1 => (tensorPow L n).tensor L

@[simp]
theorem tensorPow_zero (L : LineBundle X) : L.tensorPow 0 = trivial X := rfl

@[simp]
theorem tensorPow_succ (L : LineBundle X) (n : ℕ) :
    L.tensorPow (n + 1) = (L.tensorPow n).tensor L := rfl

/-- Integer tensor powers, using tensor powers of the dual for negative exponents. -/
def tensorIntPow (L : LineBundle X) : ℤ → LineBundle X
  | .ofNat n => L.tensorPow n
  | .negSucc n => L.dual.tensorPow (n + 1)

end LineBundle

/-- Isomorphism classes of line bundles. -/
def LineBundle.Isomorphic (L M : LineBundle X) : Prop := Nonempty (L.Iso M)

instance lineBundleSetoid (X : Scheme.{u}) : Setoid (LineBundle X) where
  r := LineBundle.Isomorphic
  iseqv :=
    { refl := fun L ↦ ⟨Iso.refl L.obj⟩
      symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
      trans := fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩ }

/-- The set of isomorphism classes of line bundles on a scheme. -/
abbrev PicardClass (X : Scheme.{u}) := Quotient (lineBundleSetoid X)

/-- Tensor product on isomorphism classes of line bundles. -/
def PicardClass.tensor : PicardClass X → PicardClass X → PicardClass X :=
  Quotient.map₂ LineBundle.tensor (by
    intro L L' hL M M' hM
    obtain ⟨eL⟩ := hL
    obtain ⟨eM⟩ := hM
    exact ⟨LineBundle.tensorMapIso eL eM⟩)

/-- The class of the trivial line bundle. -/
def PicardClass.trivial : PicardClass X := ⟦LineBundle.trivial X⟧

/-- Nonnegative tensor powers on line-bundle classes. -/
def PicardClass.tensorPow (a : PicardClass X) (n : ℕ) : PicardClass X :=
  Quotient.map (fun L ↦ L.tensorPow n) (by
    intro L M h
    obtain ⟨e⟩ := h
    induction n with
    | zero => exact ⟨Iso.refl _⟩
    | succ n ih =>
      exact ⟨LineBundle.tensorMapIso ih.some e⟩) a

@[simp]
theorem PicardClass.tensor_mk (L M : LineBundle X) :
    PicardClass.tensor (⟦L⟧ : PicardClass X) ⟦M⟧ = ⟦L.tensor M⟧ := rfl

@[simp]
theorem PicardClass.trivial_tensor (a : PicardClass X) :
    PicardClass.tensor (PicardClass.trivial (X := X)) a = a := by
  refine Quotient.inductionOn a ?_
  intro L
  apply Quotient.sound
  exact ⟨LineBundle.trivialTensorIso L⟩

@[simp]
theorem PicardClass.tensor_trivial (a : PicardClass X) :
    PicardClass.tensor a (PicardClass.trivial (X := X)) = a := by
  refine Quotient.inductionOn a ?_
  intro L
  apply Quotient.sound
  exact ⟨LineBundle.tensorTrivialIso L⟩

theorem PicardClass.tensor_comm (a b : PicardClass X) :
    PicardClass.tensor a b = PicardClass.tensor b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro L M
  apply Quotient.sound
  exact ⟨LineBundle.tensorCommIso L M⟩

/-- Tensor product is associative on isomorphism classes of line bundles. -/
theorem PicardClass.tensor_assoc (a b c : PicardClass X) :
    PicardClass.tensor (PicardClass.tensor a b) c =
      PicardClass.tensor a (PicardClass.tensor b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro L M N
  apply Quotient.sound
  exact ⟨LineBundle.tensorAssocIso L M N⟩

@[simp]
theorem PicardClass.tensorPow_mk (L : LineBundle X) (n : ℕ) :
    PicardClass.tensorPow (⟦L⟧ : PicardClass X) n = ⟦L.tensorPow n⟧ := rfl

@[simp]
theorem PicardClass.tensorPow_zero (a : PicardClass X) :
    PicardClass.tensorPow a 0 = PicardClass.trivial := by
  refine Quotient.inductionOn a ?_
  intro L
  rfl

@[simp]
theorem PicardClass.tensorPow_succ (a : PicardClass X) (n : ℕ) :
    PicardClass.tensorPow a (n + 1) =
      PicardClass.tensor (PicardClass.tensorPow a n) a := by
  refine Quotient.inductionOn a ?_
  intro L
  rfl

/-- The class of a line bundle tensored with its dual is trivial. -/
@[simp]
theorem PicardClass.tensor_dual_mk (L : LineBundle X) :
    PicardClass.tensor (⟦L⟧ : PicardClass X) ⟦L.dual⟧ =
      PicardClass.trivial := by
  apply Quotient.sound
  exact ⟨LineBundle.tensorDualIso L⟩

/-- Tensor product and the trivial class make the Picard classes into a commutative monoid. -/
instance PicardClass.commMonoid : CommMonoid (PicardClass X) where
  mul := PicardClass.tensor
  mul_assoc := PicardClass.tensor_assoc
  one := PicardClass.trivial
  one_mul := PicardClass.trivial_tensor
  mul_one := PicardClass.tensor_trivial
  mul_comm := PicardClass.tensor_comm
  npow := fun n a ↦ PicardClass.tensorPow a n
  npow_zero := PicardClass.tensorPow_zero
  npow_succ := fun n a ↦ PicardClass.tensorPow_succ a n

/-- Two right inverses of an element of the commutative Picard monoid coincide. -/
theorem PicardClass.inverse_unique (a b c : PicardClass X)
    (hb : PicardClass.tensor a b = PicardClass.trivial)
    (hc : PicardClass.tensor a c = PicardClass.trivial) : b = c := by
  calc
    b = PicardClass.tensor b PicardClass.trivial :=
      (PicardClass.tensor_trivial b).symm
    _ = PicardClass.tensor b (PicardClass.tensor a c) := by rw [hc]
    _ = PicardClass.tensor (PicardClass.tensor b a) c :=
      (PicardClass.tensor_assoc b a c).symm
    _ = PicardClass.tensor (PicardClass.tensor a b) c := by
      rw [PicardClass.tensor_comm b a]
    _ = PicardClass.tensor PicardClass.trivial c := by rw [hb]
    _ = c := PicardClass.trivial_tensor c

/-- Dual line bundles descend to isomorphism classes. -/
def PicardClass.dual : PicardClass X → PicardClass X :=
  Quotient.map LineBundle.dual (by
    intro L M hLM
    have hclass : (⟦L⟧ : PicardClass X) = ⟦M⟧ := Quotient.sound hLM
    apply Quotient.exact
    apply PicardClass.inverse_unique (⟦L⟧ : PicardClass X)
    · exact PicardClass.tensor_dual_mk L
    · rw [hclass]
      exact PicardClass.tensor_dual_mk M)

@[simp]
theorem PicardClass.dual_mk (L : LineBundle X) :
    PicardClass.dual (⟦L⟧ : PicardClass X) = ⟦L.dual⟧ := rfl

/-- Every Picard class has its dual as a tensor inverse. -/
@[simp]
theorem PicardClass.tensor_dual (a : PicardClass X) :
    PicardClass.tensor a (PicardClass.dual a) = PicardClass.trivial := by
  refine Quotient.inductionOn a ?_
  exact PicardClass.tensor_dual_mk

/-- Picard classes form a commutative group under tensor product. -/
instance PicardClass.commGroup : CommGroup (PicardClass X) where
  __ := PicardClass.commMonoid
  inv := PicardClass.dual
  inv_mul_cancel a := by
    change PicardClass.tensor (PicardClass.dual a) a = PicardClass.trivial
    rw [PicardClass.tensor_comm]
    exact PicardClass.tensor_dual a

@[simp]
theorem PicardClass.dual_eq_inv (a : PicardClass X) : PicardClass.dual a = a⁻¹ := rfl

/-- The bundled integer tensor power represents the group-theoretic integer power of a Picard
class. -/
@[simp]
theorem PicardClass.zpow_mk (L : LineBundle X) (n : ℤ) :
    (⟦L⟧ : PicardClass X) ^ n = ⟦L.tensorIntPow n⟧ := by
  cases n with
  | ofNat n =>
      calc
        (⟦L⟧ : PicardClass X) ^ (Int.ofNat n) =
            (⟦L⟧ : PicardClass X) ^ n := zpow_ofNat _ n
        _ = PicardClass.tensorPow (⟦L⟧ : PicardClass X) n := rfl
        _ = ⟦L.tensorPow n⟧ := PicardClass.tensorPow_mk L n
        _ = ⟦L.tensorIntPow (Int.ofNat n)⟧ := rfl
  | negSucc n =>
      calc
        (⟦L⟧ : PicardClass X) ^ (Int.negSucc n) =
            ((⟦L⟧ : PicardClass X) ^ (n + 1))⁻¹ := zpow_negSucc _ n
        _ = ((⟦L⟧ : PicardClass X)⁻¹) ^ (n + 1) := (inv_pow _ _).symm
        _ = PicardClass.tensorPow
            (PicardClass.dual (⟦L⟧ : PicardClass X)) (n + 1) := rfl
        _ = PicardClass.tensorPow (⟦L.dual⟧ : PicardClass X) (n + 1) := by
          rw [PicardClass.dual_mk]
        _ = ⟦L.dual.tensorPow (n + 1)⟧ :=
          PicardClass.tensorPow_mk L.dual (n + 1)
        _ = ⟦L.tensorIntPow (Int.negSucc n)⟧ := rfl

/-- Pullback on line-bundle classes. -/
def PicardClass.pullback (f : Y ⟶ X) : PicardClass X → PicardClass Y :=
  Quotient.map (fun L ↦ L.pullback f) (by
    intro L M h
    rcases h with ⟨e⟩
    exact ⟨(Scheme.Modules.pullback f).mapIso e⟩)

/-- Pullback preserves tensor products of line-bundle classes. -/
@[simp]
theorem PicardClass.pullback_tensor (f : Y ⟶ X) (a b : PicardClass X) :
    PicardClass.pullback f (PicardClass.tensor a b) =
      PicardClass.tensor (PicardClass.pullback f a) (PicardClass.pullback f b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro L M
  apply Quotient.sound
  exact ⟨LineBundle.pullbackTensorIso f L M⟩

/-- Pullback preserves the trivial line-bundle class. -/
@[simp]
theorem PicardClass.pullback_trivial (f : Y ⟶ X) :
    PicardClass.pullback f (PicardClass.trivial (X := X)) =
      PicardClass.trivial (X := Y) := by
  apply Quotient.sound
  exact ⟨LineBundle.pullbackTrivialIso f⟩

/-- Pullback is a homomorphism of the tensor commutative monoids of line-bundle classes. -/
def PicardClass.pullbackMonoidHom (f : Y ⟶ X) :
    PicardClass X →* PicardClass Y where
  toFun := PicardClass.pullback f
  map_one' := PicardClass.pullback_trivial f
  map_mul' := PicardClass.pullback_tensor f

/-- Pullback preserves duals, equivalently inverses, of Picard classes. -/
@[simp]
theorem PicardClass.pullback_dual (f : Y ⟶ X) (a : PicardClass X) :
    PicardClass.pullback f (PicardClass.dual a) =
      PicardClass.dual (PicardClass.pullback f a) := by
  change PicardClass.pullbackMonoidHom f (a⁻¹) =
    (PicardClass.pullbackMonoidHom f a)⁻¹
  exact map_inv (PicardClass.pullbackMonoidHom f) a

/-- Pullback preserves all integer tensor powers. -/
@[simp]
theorem PicardClass.pullback_zpow (f : Y ⟶ X) (a : PicardClass X) (n : ℤ) :
    PicardClass.pullback f (a ^ n) = (PicardClass.pullback f a) ^ n := by
  exact map_zpow (PicardClass.pullbackMonoidHom f) a n

/-- A line bundle is isomorphic to its double dual. -/
noncomputable def LineBundle.dualDualIso (L : LineBundle X) : L.dual.dual.Iso L := by
  have h : (⟦L.dual.dual⟧ : PicardClass X) = ⟦L⟧ := by
    calc
      (⟦L.dual.dual⟧ : PicardClass X) =
          PicardClass.dual (⟦L.dual⟧ : PicardClass X) :=
        (PicardClass.dual_mk L.dual).symm
      _ = (⟦L.dual⟧ : PicardClass X)⁻¹ := PicardClass.dual_eq_inv _
      _ = (PicardClass.dual (⟦L⟧ : PicardClass X))⁻¹ := by
        rw [PicardClass.dual_mk]
      _ = ((⟦L⟧ : PicardClass X)⁻¹)⁻¹ := by
        rw [PicardClass.dual_eq_inv]
      _ = ⟦L⟧ := inv_inv _
  exact (Quotient.exact h).some

/-- Pullback commutes with dual line bundles up to an actual bundle isomorphism. -/
noncomputable def LineBundle.pullbackDualIso (f : Y ⟶ X) (L : LineBundle X) :
    (L.dual.pullback f).Iso ((L.pullback f).dual) := by
  have h := PicardClass.pullback_dual f (⟦L⟧ : PicardClass X)
  change (⟦L.dual.pullback f⟧ : PicardClass Y) = ⟦(L.pullback f).dual⟧ at h
  exact (Quotient.exact h).some

/-- Pullback commutes with every integer tensor power up to an actual bundle isomorphism. -/
noncomputable def LineBundle.pullbackIntPowIso (f : Y ⟶ X) (L : LineBundle X) (n : ℤ) :
    (L.tensorIntPow n).pullback f |>.Iso ((L.pullback f).tensorIntPow n) := by
  have h : (⟦(L.tensorIntPow n).pullback f⟧ : PicardClass Y) =
      ⟦(L.pullback f).tensorIntPow n⟧ := by
    calc
      (⟦(L.tensorIntPow n).pullback f⟧ : PicardClass Y) =
          PicardClass.pullback f ((⟦L⟧ : PicardClass X) ^ n) := by
        rw [PicardClass.zpow_mk]
        rfl
      _ = (PicardClass.pullback f (⟦L⟧ : PicardClass X)) ^ n :=
        PicardClass.pullback_zpow f _ n
      _ = (⟦L.pullback f⟧ : PicardClass Y) ^ n := rfl
      _ = ⟦(L.pullback f).tensorIntPow n⟧ :=
        PicardClass.zpow_mk (L.pullback f) n
  exact (Quotient.exact h).some

/-- Pullback of line-bundle classes along the identity is the identity. -/
theorem PicardClass.pullback_id (a : PicardClass X) :
    PicardClass.pullback (𝟙 X) a = a := by
  refine Quotient.inductionOn a ?_
  intro L
  apply Quotient.sound
  exact ⟨(Scheme.Modules.pullbackId X).app L.obj⟩

/-- Pullback of line-bundle classes is contravariantly functorial. -/
theorem PicardClass.pullback_comp (f : Y ⟶ X) (g : Z ⟶ Y) (a : PicardClass X) :
    PicardClass.pullback g (PicardClass.pullback f a) =
      PicardClass.pullback (g ≫ f) a := by
  refine Quotient.inductionOn a ?_
  intro L
  apply Quotient.sound
  exact ⟨(Scheme.Modules.pullbackComp g f).app L.obj⟩

/-- Sheaf cohomology of an `O_X`-module, using Mathlib's `Ext`-based sheaf cohomology on the
topological site of `X`. -/
abbrev SheafCohomology (M : X.Modules) (n : ℕ)
    [hExt : CategoryTheory.HasExt.{u}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] :=
  @CategoryTheory.Sheaf.H.{u, u, u, u}
    (Opens X) _ (Opens.grothendieckTopology X)
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) inferInstance hExt n

end

end GromovWitten.AlgebraicGeometry.Curves
