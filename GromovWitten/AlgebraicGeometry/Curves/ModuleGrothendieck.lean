/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyBasic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.Grp.AB

/-!
# Generators for sheaves of modules

The category of sheaves of modules over a scheme is presented as the reflective
sheafification of presheaves of modules.  This file records the concrete free-Yoneda
separator obtained by transporting the presheaf generator through that sheafification.
It also proves the AB5 part for presheaves of modules. The sheaf-level Grothendieck
instance is assembled downstream by `ModuleEnoughInjectives`, using the reflective
sheafification adjunction and its finite-limit preservation.
-/

open CategoryTheory Limits Opposite
open _root_.AlgebraicGeometry
open scoped AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X : Scheme.{u}}

abbrev moduleSheafification (X : Scheme.{u}) :
    PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Modules :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The sheafified free presheaf of modules represented by an open `U`. -/
noncomputable abbrev moduleFreeYoneda (X : Scheme.{u}) (U : X.Opens) : X.Modules :=
  (moduleSheafification X).obj
    ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))

/-- Maps out of the sheafified free-Yoneda module are exactly sections over its open. -/
noncomputable def moduleFreeYonedaHomEquiv {U : X.Opens} {M : X.Modules} :
    (moduleFreeYoneda X U ⟶ M) ≃ M.presheaf.obj (Opposite.op U) := by
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    _ _ |>.trans PresheafOfModules.freeYonedaEquiv

lemma moduleFreeYonedaHomEquiv_comp {U : X.Opens} {M N : X.Modules}
    (α : moduleFreeYoneda X U ⟶ M) (f : M ⟶ N) :
    moduleFreeYonedaHomEquiv (α ≫ f) =
      f.app U (moduleFreeYonedaHomEquiv α) := by
  change PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
        _ _ (α ≫ f)) = _
  rw [(PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right
    α f]
  rw [PresheafOfModules.freeYonedaEquiv_comp]
  rfl

/-- The family of all sheafified free-Yoneda modules on opens of `X`. -/
def moduleFreeYonedaFamily (X : Scheme.{u}) : ObjectProperty X.Modules :=
  .ofObj (fun U : X.Opens => moduleFreeYoneda X U)

/-- The free-Yoneda family separates morphisms of sheaves of modules. -/
lemma moduleFreeYonedaFamily_isSeparating :
    ObjectProperty.IsSeparating (moduleFreeYonedaFamily X) := by
  intro M N f g h
  apply Scheme.Modules.hom_ext f g
  intro U
  refine ConcreteCategory.hom_ext _ _ ?_
  intro x
  obtain ⟨α, rfl⟩ :=
    (moduleFreeYonedaHomEquiv (X := X) (U := U) (M := M)).surjective x
  simpa only [moduleFreeYonedaHomEquiv_comp] using
    congr_arg moduleFreeYonedaHomEquiv (h _ ⟨U⟩ α)

/-- A concrete separator for `X.Modules`, assembled from all open free-Yoneda modules. -/
noncomputable def moduleSeparator (X : Scheme.{u}) : X.Modules :=
  ∐ (fun U : X.Opens => moduleFreeYoneda X U)

theorem moduleSeparator_isSeparator (X : Scheme.{u}) :
    IsSeparator (moduleSeparator X) :=
  ObjectProperty.IsSeparating.isSeparator_coproduct
    (moduleFreeYonedaFamily_isSeparating (X := X))

instance hasSeparator_schemeModules (X : Scheme.{u}) : HasSeparator X.Modules where
  hasSeparator := ⟨moduleSeparator X, moduleSeparator_isSeparator X⟩

/-! ### The presheaf AB5 prerequisite -/

/-- Filtered colimits of presheaves of modules are exact.

The proof reduces finite-limit preservation to the underlying presheaves of abelian groups,
where it is pointwise, and uses the exact filtered-colimit theorem for `AddCommGrp`. -/
theorem presheafModules_hasExactColimitsOfShape
    {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u})
    {J : Type u} [Category.{u} J] [IsFiltered J] :
    HasExactColimitsOfShape J (PresheafOfModules.{u} R) := by
  exact HasExactColimitsOfShape.domain_of_functor J (PresheafOfModules.toPresheaf R)

noncomputable def presheafModulesSeparator {C : Type u} [SmallCategory C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) : PresheafOfModules.{u} R :=
  ∐ (fun X : C => (PresheafOfModules.free R).obj (yoneda.obj X))

theorem presheafModulesSeparator_isSeparator {C : Type u} [SmallCategory C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) :
    IsSeparator (presheafModulesSeparator R) := by
  apply ObjectProperty.IsSeparating.isSeparator_coproduct
  exact PresheafOfModules.freeYoneda.isSeparating R

/-- Presheaves of modules form a Grothendieck abelian category.

This is the presheaf part of the derived-functor construction; the corresponding sheaf
category instance is assembled in `ModuleEnoughInjectives`. -/
noncomputable instance presheafModules_isGrothendieckAbelian
    {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R) where
  locallySmall := locallySmall_self _
  hasFilteredColimitsOfSize := inferInstance
  ab5OfSize := ⟨fun _J _ _ => presheafModules_hasExactColimitsOfShape R⟩
  hasSeparator := ⟨presheafModulesSeparator R, presheafModulesSeparator_isSeparator R⟩

end

end GromovWitten.AlgebraicGeometry.Curves
