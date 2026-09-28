/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairModule

/-!
# Naturality of the scalar-linear two-open Čech comparison

The module-valued Čech cokernel and its comparison with derived sections are functorial in the
module.  This file records the scalar-linear maps and the resulting comparison equation.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open TopologicalSpace Opposite
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X : Scheme.{u}}

/-! ## Maps on section modules -/

/-- The map on sections induced by a morphism of `𝒪_X`-modules, viewed as linear over global
functions. -/
def sectionModuleLinearMap {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) :
    @LinearMap Γ(X, ⊤) Γ(X, ⊤) _ _ (RingHom.id _) Γ(M, W) Γ(N, W)
      _ _ (sectionModule M W) (sectionModule N W) := by
  letI : Module Γ(X, ⊤) Γ(M, W) := sectionModule M W
  letI : Module Γ(X, ⊤) Γ(N, W) := sectionModule N W
  exact
    { toFun := (φ.app W).hom
      map_add' := by intro x y; exact map_add (φ.app W).hom x y
      map_smul' := by
        intro a x
        change (φ.app W).hom (restrictTop X W a • x) =
          restrictTop X W a • (φ.app W).hom x
        exact Scheme.Modules.Hom.app_smul φ (restrictTop X W a) x }

def sectionModuleMap {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) :
    sectionModuleCat M W ⟶ sectionModuleCat N W := by
  letI : Module Γ(X, ⊤) Γ(M, W) := sectionModule M W
  letI : Module Γ(X, ⊤) Γ(N, W) := sectionModule N W
  exact ModuleCat.ofHom (sectionModuleLinearMap φ W)

theorem sectionModuleMap_forget {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) :
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map (sectionModuleMap φ W) =
      AddCommGrpCat.ofHom (φ.app W).hom := by
  rw [ModuleCat.forget₂_map]
  rfl

/-- The induced map on the two-open product of section modules. -/
def sectionsPairModuleMap {M N : X.Modules} (φ : M ⟶ N) (U V : X.Opens) :
    sectionsPairModule M U V ⟶ sectionsPairModule N U V := by
  letI : Module Γ(X, ⊤) Γ(M, U) := sectionModule M U
  letI : Module Γ(X, ⊤) Γ(M, V) := sectionModule M V
  letI : Module Γ(X, ⊤) Γ(N, U) := sectionModule N U
  letI : Module Γ(X, ⊤) Γ(N, V) := sectionModule N V
  letI : Module Γ(X, ⊤) (Γ(M, U) × Γ(M, V)) := sectionsPairModuleStructure M U V
  letI : Module Γ(X, ⊤) (Γ(N, U) × Γ(N, V)) := sectionsPairModuleStructure N U V
  exact ModuleCat.ofHom ((sectionModuleLinearMap φ U).prodMap (sectionModuleLinearMap φ V))

theorem sectionsPairModuleMap_forget {M N : X.Modules} (φ : M ⟶ N) (U V : X.Opens) :
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map
        (sectionsPairModuleMap φ U V) =
      AddCommGrpCat.ofHom ((φ.app U).hom.prodMap (φ.app V).hom) := by
  rw [ModuleCat.forget₂_map]
  rfl

/-! ## Maps on derived sections -/

/-- The map on derived sections induced by a module morphism, with its global-functions-linear
structure. -/
def derivedSectionsModuleMap {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) (n : ℕ) :
    derivedSectionsModuleCat M W n ⟶ derivedSectionsModuleCat N W n := by
  let f :
      (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).obj
          (derivedSectionsModuleCat M W n) ⟶
        (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).obj
          (derivedSectionsModuleCat N W n) :=
    ((sections W).rightDerived n).map ((moduleToSheafAb X).map φ)
  apply ModuleCat.homMk f
  intro a
  have h := congrArg (fun ψ => ((sections W).rightDerived n).map ψ)
    (sectionSMul_naturality φ a)
  change f ≫ ((sections W).rightDerived n).map (sectionSMul N a) =
    ((sections W).rightDerived n).map (sectionSMul M a) ≫ f
  simp only [Functor.map_comp] at h
  apply AddCommGrpCat.hom_ext
  ext x
  exact ConcreteCategory.congr_hom h x

theorem derivedSectionsModuleMap_forget {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) (n : ℕ) :
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map
        (derivedSectionsModuleMap φ W n) =
      ((sections W).rightDerived n).map ((moduleToSheafAb X).map φ) := by
  rw [ModuleCat.forget₂_map]
  change AddCommGrpCat.ofHom _ = _
  apply AddCommGrpCat.hom_ext
  ext x
  rfl

/-! ## Maps on the Čech cokernel -/

theorem sectionsPairModuleMap_comp_fromPairModuleHom
    {M N : X.Modules} (φ : M ⟶ N) (U V : X.Opens) :
    sectionsPairModuleMap φ U V ≫ sectionsFromPairModuleHom N U V =
      sectionsFromPairModuleHom M U V ≫ sectionModuleMap φ (U ⊓ V) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (sectionsFromPair ((moduleToSheafAb X).obj N) U V)
      ((φ.app U).hom x.1, (φ.app V).hom x.2) =
    (φ.app (U ⊓ V)).hom
      (sectionsFromPair ((moduleToSheafAb X).obj M) U V x)
  exact ConcreteCategory.congr_hom
    ((sectionsFromPairNat U V).naturality ((moduleToSheafAb X).map φ)) x

def cechPairModuleMap {M N : X.Modules} (φ : M ⟶ N) (U V : X.Opens) :
    cechPairModule M U V ⟶ cechPairModule N U V :=
  cokernel.map (sectionsFromPairModuleHom M U V) (sectionsFromPairModuleHom N U V)
    (sectionsPairModuleMap φ U V) (sectionModuleMap φ (U ⊓ V))
    (sectionsPairModuleMap_comp_fromPairModuleHom φ U V).symm

@[reassoc (attr := simp)]
theorem cechPairModuleProjection_comp_map {M N : X.Modules} (φ : M ⟶ N)
    (U V : X.Opens) :
    cechPairModuleProjection M U V ≫ cechPairModuleMap φ U V =
      sectionModuleMap φ (U ⊓ V) ≫ cechPairModuleProjection N U V := by
  apply cokernel.π_desc

/-! ## Naturality of the derived comparison -/

theorem intersectionConnectingModuleHom_naturality
    {M N : X.Modules} (φ : M ⟶ N) (U V : X.Opens) :
      sectionModuleMap φ (U ⊓ V) ≫ intersectionConnectingModuleHom N U V =
      intersectionConnectingModuleHom M U V ≫ derivedSectionsModuleMap φ (U ⊔ V) 1 := by
  apply (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map_injective
  change (sections (U ⊓ V)).map ((moduleToSheafAb X).map φ) ≫
      ((sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj N) ≫
      mvRightDerivedConnecting (F := (moduleToSheafAb X).obj N) U V 0) =
    ((sections (U ⊓ V)).toRightDerivedZero.app ((moduleToSheafAb X).obj M) ≫
      mvRightDerivedConnecting (F := (moduleToSheafAb X).obj M) U V 0) ≫
      ((sections (U ⊔ V)).rightDerived 1).map ((moduleToSheafAb X).map φ)
  have h0 := (sections (U ⊓ V)).toRightDerivedZero.naturality
    ((moduleToSheafAb X).map φ)
  have hδ := mvRightDerivedConnecting_naturality ((moduleToSheafAb X).map φ) U V 0
  rw [← Category.assoc, h0, Category.assoc, hδ, ← Category.assoc]

theorem cechPairModuleMap_comp_toDerived {M N : X.Modules} (φ : M ⟶ N)
    (U V : X.Opens) :
    cechPairModuleMap φ U V ≫ cechPairModuleToDerived N U V =
      cechPairModuleToDerived M U V ≫ derivedSectionsModuleMap φ (U ⊔ V) 1 := by
  have hEpi : Epi (cechPairModuleProjection M U V) := by
    change Epi (cokernel.π (sectionsFromPairModuleHom M U V))
    infer_instance
  apply (@cancel_epi _ _ _ _ _ _ hEpi).mp
  calc
    cechPairModuleProjection M U V ≫
        (cechPairModuleMap φ U V ≫ cechPairModuleToDerived N U V) =
      sectionModuleMap φ (U ⊓ V) ≫
        (cechPairModuleProjection N U V ≫ cechPairModuleToDerived N U V) := by
          rw [← Category.assoc, cechPairModuleProjection_comp_map, Category.assoc]
    _ = sectionModuleMap φ (U ⊓ V) ≫ intersectionConnectingModuleHom N U V := by
          rw [cechPairModuleProjection_comp_toDerived]
    _ = intersectionConnectingModuleHom M U V ≫
        derivedSectionsModuleMap φ (U ⊔ V) 1 :=
      intersectionConnectingModuleHom_naturality φ U V
    _ = cechPairModuleProjection M U V ≫
        (cechPairModuleToDerived M U V ≫ derivedSectionsModuleMap φ (U ⊔ V) 1) := by
          rw [← Category.assoc, cechPairModuleProjection_comp_toDerived]

end GromovWitten.AlgebraicGeometry.SheafCohomology
