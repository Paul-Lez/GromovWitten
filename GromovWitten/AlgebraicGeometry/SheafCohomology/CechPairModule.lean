/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairComparison
import GromovWitten.AlgebraicGeometry.SheafCohomology.RightDerivedAdditivity
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The scalar-linear two-open Čech comparison

The two-open Čech calculation is naturally linear over the ring of global functions.  This file
puts the restriction-difference map in `ModuleCat` and compares its module cokernel with the
additive cokernel used by `CechPairComparison`.  The projection equation with the
Mayer--Vietoris connecting map is retained explicitly.

The Ext-based `Sheaf.H` comparison is made scalar-linear using the naturality of the additive
comparison in positive degree.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open TopologicalSpace Opposite
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X : Scheme.{u}}

/-! ## Sections as modules over global functions -/

/-- The global-functions module structure on sections over an open, with scalars restricted to it.

This is a value rather than a global instance so it cannot compete with the native structure on
global sections over `⊤`. -/
@[instance_reducible]
def sectionModule (M : X.Modules) (U : X.Opens) : Module Γ(X, ⊤) Γ(M, U) :=
  Module.compHom _ (restrictTop X U)

def sectionModuleCat (M : X.Modules) (U : X.Opens) : ModuleCat Γ(X, ⊤) :=
  @ModuleCat.of Γ(X, ⊤) _ (Γ(M, U)) _ (sectionModule M U)

@[instance_reducible]
def sectionsPairModuleStructure (M : X.Modules) (U V : X.Opens) :
    Module Γ(X, ⊤) (Γ(M, U) × Γ(M, V)) := by
  letI : Module Γ(X, ⊤) Γ(M, U) := sectionModule M U
  letI : Module Γ(X, ⊤) Γ(M, V) := sectionModule M V
  infer_instance

/-- Restriction of module sections, viewed as a linear map over global functions. -/
def sectionRestrictionLinear (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    @LinearMap Γ(X, ⊤) Γ(X, ⊤) _ _ (RingHom.id _) Γ(M, U) Γ(M, V) _ _
      (sectionModule M U) (sectionModule M V) := by
  letI : Module Γ(X, ⊤) Γ(M, U) := sectionModule M U
  letI : Module Γ(X, ⊤) Γ(M, V) := sectionModule M V
  exact LinearMap.mk
    (AddMonoidHom.mk' (fun x => M.presheaf.map i.op x) (by simp)) (by
      intro a x
      change M.presheaf.map i.op (restrictTop X U a • x) =
        restrictTop X V a • M.presheaf.map i.op x
      rw [M.map_smul, restrictTop_map])

@[simp]
theorem sectionRestrictionLinear_apply (M : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (x : Γ(M, U)) : sectionRestrictionLinear M i x = M.presheaf.map i.op x := rfl

/-! ## The scalar-linear restriction difference -/

def sectionsPairModule (M : X.Modules) (U V : X.Opens) : ModuleCat Γ(X, ⊤) := by
  exact @ModuleCat.of Γ(X, ⊤) _ (Γ(M, U) × Γ(M, V)) _
    (sectionsPairModuleStructure M U V)

def sectionsFromPairLinear (M : X.Modules) (U V : X.Opens) :
    @LinearMap Γ(X, ⊤) Γ(X, ⊤) _ _ (RingHom.id _) (Γ(M, U) × Γ(M, V)) Γ(M, U ⊓ V)
      _ _ (sectionsPairModuleStructure M U V) (sectionModule M (U ⊓ V)) := by
  letI : Module Γ(X, ⊤) Γ(M, U) := sectionModule M U
  letI : Module Γ(X, ⊤) Γ(M, V) := sectionModule M V
  letI : Module Γ(X, ⊤) (Γ(M, U) × Γ(M, V)) := sectionsPairModuleStructure M U V
  letI : Module Γ(X, ⊤) Γ(M, U ⊓ V) := sectionModule M (U ⊓ V)
  exact
    (sectionRestrictionLinear M (homOfLE (inf_le_left : U ⊓ V ≤ U))).comp
        (LinearMap.fst Γ(X, ⊤) Γ(M, U) Γ(M, V)) -
      (sectionRestrictionLinear M (homOfLE (inf_le_right : U ⊓ V ≤ V))).comp
        (LinearMap.snd Γ(X, ⊤) Γ(M, U) Γ(M, V))

def sectionsFromPairModuleHom (M : X.Modules) (U V : X.Opens) :
    sectionsPairModule M U V ⟶ sectionModuleCat M (U ⊓ V) := by
  letI : Module Γ(X, ⊤) Γ(M, U) := sectionModule M U
  letI : Module Γ(X, ⊤) Γ(M, V) := sectionModule M V
  letI : Module Γ(X, ⊤) Γ(M, U ⊓ V) := sectionModule M (U ⊓ V)
  exact ModuleCat.ofHom (sectionsFromPairLinear M U V)

/-! ## The scalar-linear degree-zero kernel -/

/-- Restriction from the union to the two opens, as a global-functions-linear map. -/
def sectionsToPairLinear (M : X.Modules) (U V : X.Opens) :
    @LinearMap Γ(X, ⊤) Γ(X, ⊤) _ _ (RingHom.id _) Γ(M, U ⊔ V)
      (Γ(M, U) × Γ(M, V)) _ _ (sectionModule M (U ⊔ V))
      (sectionsPairModuleStructure M U V) := by
  letI : Module Γ(X, ⊤) Γ(M, U ⊔ V) := sectionModule M (U ⊔ V)
  letI : Module Γ(X, ⊤) Γ(M, U) := sectionModule M U
  letI : Module Γ(X, ⊤) Γ(M, V) := sectionModule M V
  letI : Module Γ(X, ⊤) (Γ(M, U) × Γ(M, V)) := sectionsPairModuleStructure M U V
  exact
    (sectionRestrictionLinear M (homOfLE (le_sup_left : U ≤ U ⊔ V))).prod
      (sectionRestrictionLinear M (homOfLE (le_sup_right : V ≤ U ⊔ V)))

@[simp]
theorem sectionsToPairLinear_apply (M : X.Modules) (U V : X.Opens)
    (x : Γ(M, U ⊔ V)) :
    sectionsToPairLinear M U V x =
      (M.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op x,
        M.presheaf.map (homOfLE (le_sup_right : V ≤ U ⊔ V)).op x) := rfl

/-- The kernel of the restriction-difference map on the pair of sections. -/
def sectionsPairKernel (M : X.Modules) (U V : X.Opens) :
    Submodule Γ(X, ⊤) (sectionsPairModule M U V : Type u) :=
  by
    letI : Module Γ(X, ⊤) (Γ(M, U) × Γ(M, V)) := sectionsPairModuleStructure M U V
    letI : Module Γ(X, ⊤) Γ(M, U ⊓ V) := sectionModule M (U ⊓ V)
    exact LinearMap.ker (sectionsFromPairLinear M U V)

/-- The union-to-pair restriction map with codomain restricted to the Cech kernel. -/
def sectionsToPairKernelLinear (M : X.Modules) (U V : X.Opens) :
    @LinearMap Γ(X, ⊤) Γ(X, ⊤) _ _ (RingHom.id _) Γ(M, U ⊔ V)
      (sectionsPairKernel M U V) _ _ (sectionModule M (U ⊔ V)) inferInstance := by
  letI : Module Γ(X, ⊤) Γ(M, U ⊔ V) := sectionModule M (U ⊔ V)
  letI : Module Γ(X, ⊤) (Γ(M, U) × Γ(M, V)) := sectionsPairModuleStructure M U V
  exact (sectionsToPairLinear M U V).codRestrict _ (fun x => by
    change sectionsFromPairLinear M U V (sectionsToPairLinear M U V x) = 0
    change (sectionsToPair ((moduleToSheafAb X).obj M) U V ≫
      sectionsFromPair ((moduleToSheafAb X).obj M) U V).hom x = 0
    exact ConcreteCategory.congr_hom
      (sectionsToPair_fromPair ((moduleToSheafAb X).obj M) U V) x)

/-- Degree-zero sections are canonically the global sections satisfying the Cech relation. -/
def sectionsToPairKernelLinearEquiv (M : X.Modules) (U V : X.Opens) :
    (sectionModuleCat M (U ⊔ V) : Type u) ≃ₗ[Γ(X, ⊤)] sectionsPairKernel M U V := by
  letI : Module Γ(X, ⊤) Γ(M, U ⊔ V) := sectionModule M (U ⊔ V)
  exact LinearEquiv.ofBijective (sectionsToPairKernelLinear M U V) ⟨by
    intro x y h
    apply (sectionsToPair_injective ((moduleToSheafAb X).obj M) U V)
    have h' := congrArg Subtype.val h
    change sectionsToPairLinear M U V x = sectionsToPairLinear M U V y at h'
    change sectionsToPair ((moduleToSheafAb X).obj M) U V x =
      sectionsToPair ((moduleToSheafAb X).obj M) U V y
    exact h', by
    intro x
    have hx : sectionsFromPair ((moduleToSheafAb X).obj M) U V x.1 = 0 := by
      change sectionsFromPairLinear M U V x.1 = 0
      exact x.property
    have hx' : sectionsFromPair ((moduleToSheafAb X).obj M) U V x.1 =
        (0 : Γ(M, U ⊓ V)) := hx
    obtain ⟨s, hs⟩ := (ShortComplex.ab_exact_iff _).mp
      (sectionsMV_exact ((moduleToSheafAb X).obj M) U V) x.1 hx'
    refine ⟨s, ?_⟩
    apply Subtype.ext
    change sectionsToPairLinear M U V s = x.1
    change sectionsToPair ((moduleToSheafAb X).obj M) U V s = x.1
    exact hs⟩

/-! ## Scalar actions on arbitrary derived sections -/

/-- Multiplication by a global function on derived sections over an arbitrary open and degree. -/
def derivedSectionsSMulRingHom (M : X.Modules) (W : X.Opens) (n : ℕ) :
    Γ(X, ⊤) →+* End (((sections W).rightDerived n).obj ((moduleToSheafAb X).obj M)) :=
  (additiveMapEndRingHom ((sections W).rightDerived n)
    ((moduleToSheafAb X).obj M)).comp (sectionSMulRingHom M)

@[simp]
theorem derivedSectionsSMulRingHom_apply (M : X.Modules) (W : X.Opens) (n : ℕ)
    (a : Γ(X, ⊤)) :
    derivedSectionsSMulRingHom M W n a =
      ((sections W).rightDerived n).map (sectionSMul M a) := rfl

/-- The induced global-functions module structure on a derived section object. -/
def derivedSectionsModuleCat (M : X.Modules) (W : X.Opens) (n : ℕ) :
    ModuleCat Γ(X, ⊤) :=
  ModuleCat.mkOfSMul (derivedSectionsSMulRingHom M W n)

/-! ## The scalar-linear Mayer--Vietoris boundary -/

def intersectionConnectingModuleHom (M : X.Modules) (U V : X.Opens) :
    sectionModuleCat M (U ⊓ V) ⟶ derivedSectionsModuleCat M (U ⊔ V) 1 := by
  let φ :
      (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).obj (sectionModuleCat M (U ⊓ V)) ⟶
        (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).obj
          (derivedSectionsModuleCat M (U ⊔ V) 1) :=
    (sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M) ≫
      mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0
  apply ModuleCat.homMk (M := sectionModuleCat M (U ⊓ V))
    (N := derivedSectionsModuleCat M (U ⊔ V) 1) φ
  intro a
  have hsource :
      (sectionModuleCat M (U ⊓ V)).smul a =
        (sections (U ⊓ V)).map (sectionSMul M a) := by
    apply AddCommGrpCat.hom_ext
    ext x
    rfl
  have htarget :
      (derivedSectionsModuleCat M (U ⊔ V) 1).smul a =
        ((sections (U ⊔ V)).rightDerived 1).map (sectionSMul M a) := by
    change derivedSectionsSMulRingHom M (U ⊔ V) 1 a = _
    rfl
  apply AddCommGrpCat.hom_ext
  ext x
  have h0 := (sections (U ⊓ V)).toRightDerivedZero.naturality (sectionSMul M a)
  have hδ := mvRightDerivedConnecting_naturality (sectionSMul M a) U V 0
  have h0' := congrArg (fun q => q ≫
    mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0) h0
  have hδ' := congrArg (fun q =>
    (sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M) ≫ q) hδ
  have h :
      ((sections (U ⊓ V)).map (sectionSMul M a) ≫
          (sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M)) ≫
          mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0 =
        ((sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M) ≫
          mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0) ≫
          ((sections (U ⊔ V)).rightDerived 1).map (sectionSMul M a) := by
    calc
      _ = (sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M) ≫
          ((sections (U ⊓ V)).rightDerived 0).map (sectionSMul M a) ≫
            mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0 := by
        simpa only [Category.assoc] using h0'
      _ = _ := by
        simpa only [Category.assoc] using hδ'
  have hx := ConcreteCategory.congr_hom h x
  rw [htarget, hsource]
  exact hx.symm

def cechPairModule (M : X.Modules) (U V : X.Opens) : ModuleCat Γ(X, ⊤) :=
  cokernel (sectionsFromPairModuleHom M U V)

def cechPairModuleProjection (M : X.Modules) (U V : X.Opens) :
    sectionModuleCat M (U ⊓ V) ⟶ cechPairModule M U V := by
  dsimp only [cechPairModule]
  exact cokernel.π (sectionsFromPairModuleHom M U V)

private lemma sectionsFromPair_comp_intersectionConnecting
    (M : X.Modules) (U V : X.Opens) :
    sectionsFromPair ((moduleToSheafAb X).obj M) U V ≫
        (sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M) ≫
        mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0 = 0 := by
  have hnat := NatTrans.toRightDerivedZero_comp (sectionsFromPairNat U V)
    ((moduleToSheafAb X).obj M)
  change (Functor.toRightDerivedZero (sectionsPairFunctor U V)).app
      ((moduleToSheafAb X).obj M) ≫
      (NatTrans.rightDerived (sectionsFromPairNat U V) 0).app
        ((moduleToSheafAb X).obj M) =
      sectionsFromPair ((moduleToSheafAb X).obj M) U V ≫
        (sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M) at hnat
  dsimp only [sectionsPairFunctor] at hnat
  have hnat' := congrArg (fun q => q ≫
    mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0) hnat
  have hright :
      (sectionsFromPair ((moduleToSheafAb X).obj M) U V ≫
        (sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M)) ≫
          mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0 =
        ((Functor.toRightDerivedZero (sectionsPairFunctor U V)).app
            ((moduleToSheafAb X).obj M) ≫
          (NatTrans.rightDerived (sectionsFromPairNat U V) 0).app
            ((moduleToSheafAb X).obj M)) ≫
          mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0 := by
    simpa only [sectionsPairFunctor] using hnat'.symm
  have hpair :
      ((Functor.toRightDerivedZero (sectionsPairFunctor U V)).app
            ((moduleToSheafAb X).obj M) ≫
          (NatTrans.rightDerived (sectionsFromPairNat U V) 0).app
            ((moduleToSheafAb X).obj M)) ≫
          mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0 = 0 := by
    change
      ((Functor.toRightDerivedZero (sectionsPairFunctor U V)).app
            ((moduleToSheafAb X).obj M) ≫
          mvRightDerivedFromPair (F := (moduleToSheafAb X).obj M) U V 0) ≫
          mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0 = 0
    rw [Category.assoc, mvRightDerivedFromPair_comp_mvRightDerivedConnecting, comp_zero]
  exact hright.trans hpair

private lemma sectionsFromPairModuleHom_comp_intersectionConnectingModuleHom
    (M : X.Modules) (U V : X.Opens) :
    sectionsFromPairModuleHom M U V ≫ intersectionConnectingModuleHom M U V = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (sectionsFromPair ((moduleToSheafAb X).obj M) U V ≫
      (sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M) ≫
      mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0).hom x = 0
  rw [sectionsFromPair_comp_intersectionConnecting]
  rfl

/-- The scalar-linear map from the Čech cokernel to derived sections. -/
def cechPairModuleToDerived (M : X.Modules) (U V : X.Opens) :
    cechPairModule M U V ⟶ derivedSectionsModuleCat M (U ⊔ V) 1 :=
  cokernel.desc (sectionsFromPairModuleHom M U V)
    (intersectionConnectingModuleHom M U V)
    (sectionsFromPairModuleHom_comp_intersectionConnectingModuleHom M U V)

@[reassoc (attr := simp)]
theorem cechPairModuleProjection_comp_toDerived (M : X.Modules) (U V : X.Opens) :
    cechPairModuleProjection M U V ≫ cechPairModuleToDerived M U V =
      intersectionConnectingModuleHom M U V := by
  apply cokernel.π_desc

theorem sectionsFromPairModuleHom_forget
    (M : X.Modules) (U V : X.Opens) :
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map
        (sectionsFromPairModuleHom M U V) =
      sectionsFromPair ((moduleToSheafAb X).obj M) U V := by
  apply AddCommGrpCat.hom_ext
  rw [ModuleCat.forget₂_map]
  rfl

/-! ## The additive comparison of the two cokernels -/

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting scalars identifies the module Čech cokernel with the additive Čech cokernel. -/
noncomputable def cechPairModuleForgetIso (M : X.Modules) (U V : X.Opens) :
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).obj (cechPairModule M U V) ≅
      cechPairCohomology ((moduleToSheafAb X).obj M) U V := by
  exact PreservesCokernel.iso (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat)
    (sectionsFromPairModuleHom M U V)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem cechPairModuleForgetIso_comp_cokernel_π (M : X.Modules) (U V : X.Opens) :
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map
        (cechPairModuleProjection M U V) ≫
        (cechPairModuleForgetIso M U V).hom =
      cokernel.π (sectionsFromPair ((moduleToSheafAb X).obj M) U V) := by
  exact PreservesCokernel.π_iso_hom
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat)
    (sectionsFromPairModuleHom M U V)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem cechPairModuleToDerived_forget
    (M : X.Modules) (U V : X.Opens)
    (hU : IsZero (((sections U).rightDerived 1).obj ((moduleToSheafAb X).obj M)))
    (hV : IsZero (((sections V).rightDerived 1).obj ((moduleToSheafAb X).obj M))) :
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map
        (cechPairModuleToDerived M U V) =
      (cechPairModuleForgetIso M U V).hom ≫
        (cechPairCohomologyIsoRightDerived ((moduleToSheafAb X).obj M) U V hU hV).hom := by
  let hIso : IsIso ((cechPairModuleForgetIso M U V).hom) := by infer_instance
  let hEpiComp : Epi ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map
      (cechPairModuleProjection M U V) ≫ (cechPairModuleForgetIso M U V).hom) := by
    rw [cechPairModuleForgetIso_comp_cokernel_π]
    infer_instance
  let hEpi : Epi ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map
      (cechPairModuleProjection M U V)) := by
    exact (@epi_comp_iff_of_isIso _ _ _ _ _ _ _ hIso).mp hEpiComp
  apply (@cancel_epi _ _ _ _ _ _ hEpi).mp
  rw [← Functor.map_comp, cechPairModuleProjection_comp_toDerived]
  change ((sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M) ≫
      mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0) = _
  rw [← Category.assoc, cechPairModuleForgetIso_comp_cokernel_π,
    cokernel_π_cechPairCohomologyIsoRightDerived_hom]

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-linear Čech comparison is an isomorphism under the two vanishing hypotheses. -/
noncomputable def cechPairModuleIsoRightDerived
    (M : X.Modules) (U V : X.Opens)
    (hU : IsZero (((sections U).rightDerived 1).obj ((moduleToSheafAb X).obj M)))
    (hV : IsZero (((sections V).rightDerived 1).obj ((moduleToSheafAb X).obj M))) :
    cechPairModule M U V ≅ derivedSectionsModuleCat M (U ⊔ V) 1 := by
  haveI : IsIso ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map
      (cechPairModuleToDerived M U V)) := by
    rw [cechPairModuleToDerived_forget M U V hU hV]
    infer_instance
  haveI : IsIso (cechPairModuleToDerived M U V) :=
    isIso_of_reflects_iso (cechPairModuleToDerived M U V)
      (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat)
  exact asIso (cechPairModuleToDerived M U V)

/-- The scalar-linear Čech comparison for a two-affine cover of a locally Noetherian scheme. -/
noncomputable def cechPairModuleIsoRightDerived_of_affine
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = (⊤ : X.Opens)) (M : X.Modules) [M.IsQuasicoherent] :
    cechPairModule M U V ≅ derivedSectionsModuleCat M (⊤ : X.Opens) 1 := by
  exact (cechPairModuleIsoRightDerived M U V
    (isZero_rightDerived_sections_affineOpen_succ U hU M 0)
    (isZero_rightDerived_sections_affineOpen_succ V hV M 0)).trans
    (eqToIso (congrArg (fun W : X.Opens => derivedSectionsModuleCat M W 1) hcover))

/-! ## Scalar-linear Ext comparison -/

/-- Positive-degree Ext cohomology is linearly identified with the corresponding derived
sections object.  The scalar compatibility is the naturality of the additive comparison applied
to multiplication by a global function. -/
noncomputable def cohomologyRightDerivedSectionsLinearEquiv
    (M : X.Modules) (n : ℕ) :
    cohomology X M (n + 1) ≃ₗ[Γ(X, ⊤)]
      (derivedSectionsModuleCat M (⊤ : X.Opens) (n + 1) : Type u) := by
  let e : (cohomology X M (n + 1) : Type u) ≃+
      (derivedSectionsModuleCat M (⊤ : X.Opens) (n + 1) : Type u) := by
    exact sheafHRightDerivedSectionsAddEquiv
      (F := ((moduleToSheafAb X).obj M :
        Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) n
  let f : cohomology X M (n + 1) →ₗ[Γ(X, ⊤)]
      (derivedSectionsModuleCat M (⊤ : X.Opens) (n + 1) : Type u) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro a x
        change e (Sheaf.H.map (sectionSMul M a) (n + 1) x) =
          ((sections (⊤ : X.Opens)).rightDerived (n + 1)).map (sectionSMul M a) (e x)
        exact sheafHRightDerivedSectionsAddEquiv_naturality (sectionSMul M a) n x }
  exact LinearEquiv.ofBijective f e.bijective

/-- The scalar-linear two-affine Čech calculation, with target the actual Ext-based degree-one
cohomology group. -/
noncomputable def cechPairModuleLinearEquivCohomology
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = (⊤ : X.Opens)) (M : X.Modules) [M.IsQuasicoherent] :
    (cechPairModule M U V : Type u) ≃ₗ[Γ(X, ⊤)] cohomology X M 1 :=
  (cechPairModuleIsoRightDerived_of_affine U V hU hV hcover M).toLinearEquiv.trans
    (cohomologyRightDerivedSectionsLinearEquiv M 0).symm

end GromovWitten.AlgebraicGeometry.SheafCohomology
