/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.OpenSectionsBaseChange
import GromovWitten.Algebra.ModuleCatScalarExtension

/-!
# Base change of the two-open Čech modules

The definitions here package the scalar-extension maps on the Čech pair and
overlap modules. Their isomorphism statements require only affine opens and
quasi-coherence; naturality and compatibility with the Čech differential are
separate results.
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open scoped ChangeOfRings
open Scheme.Modules
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- The product of two base-section modules is the base restriction of the Čech pair module. -/
def baseCechPairSectionsIso (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    ModuleCat.of R (baseSectionModule s U M × baseSectionModule s V M) ≅
      (ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
        (sectionsPairModule M U V) := Iso.refl _

@[simp]
lemma baseCechPairSectionsIso_hom_apply (s : X ⟶ Spec R) (M : X.Modules)
    (U V : X.Opens) (x : baseSectionModule s U M × baseSectionModule s V M) :
    (baseCechPairSectionsIso s M U V).hom x = x := rfl

@[simp]
lemma baseCechPairSectionsIso_inv_apply (s : X ⟶ Spec R) (M : X.Modules)
    (U V : X.Opens) (x : sectionsPairModule M U V) :
    (baseCechPairSectionsIso s M U V).inv x = x := rfl

/-- The base-section module on an overlap is the base restriction of the overlap section module. -/
def baseCechOverlapSectionsIso (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    baseSectionModule s (U ⊓ V) M ≅
      (ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
        (sectionModuleCat M (U ⊓ V)) := Iso.refl _

@[simp]
lemma baseCechOverlapSectionsIso_hom_apply (s : X ⟶ Spec R) (M : X.Modules)
    (U V : X.Opens) (x : baseSectionModule s (U ⊓ V) M) :
    (baseCechOverlapSectionsIso s M U V).hom x = x := rfl

@[simp]
lemma baseCechOverlapSectionsIso_inv_apply (s : X ⟶ Spec R) (M : X.Modules)
    (U V : X.Opens) (x : sectionModuleCat M (U ⊓ V)) :
    (baseCechOverlapSectionsIso s M U V).inv x = x := rfl

/-- The scalar-extension map on the pair of sections in a Cartesian square. -/
def cechPairBaseChangeMap (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) (U V : X.Opens) :
    (ModuleCat.extendScalars φ.hom).obj
        ((ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
          (sectionsPairModule M U V)) ⟶
      (ModuleCat.restrictScalars (baseRingHom (T : Type u) g)).obj
        (sectionsPairModule ((Scheme.Modules.pullback p).obj M)
          (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)) :=
  (ModuleCat.extendScalars φ.hom).map (baseCechPairSectionsIso s M U V).inv ≫
    (ModuleCat.extendScalarsProdIso φ.hom (baseSectionModule s U M)
      (baseSectionModule s V M)).hom ≫
    ModuleCat.ofHom ((openSectionsBaseChangeMap s φ p g h M U).hom.prodMap
      (openSectionsBaseChangeMap s φ p g h M V).hom) ≫
    (baseCechPairSectionsIso g ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)).hom

/-- The scalar-extension map on sections over the overlap in a Cartesian square. -/
def cechOverlapBaseChangeMap (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) (U V : X.Opens) :
    (ModuleCat.extendScalars φ.hom).obj
        ((ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
          (sectionModuleCat M (U ⊓ V))) ⟶
      (ModuleCat.restrictScalars (baseRingHom (T : Type u) g)).obj
        (sectionModuleCat ((Scheme.Modules.pullback p).obj M)
          ((p ⁻¹ᵁ U) ⊓ (p ⁻¹ᵁ V))) :=
  (ModuleCat.extendScalars φ.hom).map (baseCechOverlapSectionsIso s M U V).inv ≫
    openSectionsBaseChangeMap s φ p g h M (U ⊓ V) ≫
    (baseCechOverlapSectionsIso g ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)).hom

set_option backward.isDefEq.respectTransparency false in
/-- The pair base-change map is an isomorphism when both opens are affine. -/
lemma cechPairBaseChangeMap_isIso (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsIso (cechPairBaseChangeMap s φ p g h M U V) := by
  let fU := openSectionsBaseChangeMap s φ p g h M U
  let fV := openSectionsBaseChangeMap s φ p g h M V
  let _ : IsIso fU := by
    dsimp [fU]
    exact openSectionsBaseChangeMap_isIso s φ p g h M U hU
  let _ : IsIso fV := by
    dsimp [fV]
    exact openSectionsBaseChangeMap_isIso s φ p g h M V hV
  let eprod :=
    ((asIso fU).toLinearEquiv.prodCongr (asIso fV).toLinearEquiv).toModuleIso
  have heprod : eprod.hom = ModuleCat.ofHom (fU.hom.prodMap fV.hom) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((asIso fU).toLinearEquiv.prodCongr (asIso fV).toLinearEquiv) x =
      (fU.hom.prodMap fV.hom) x
    rw [LinearEquiv.prodCongr_apply, LinearMap.prodMap_apply]
    rfl
  let _ : IsIso (ModuleCat.ofHom (fU.hom.prodMap fV.hom)) := by
    rw [← heprod]
    infer_instance
  dsimp only [cechPairBaseChangeMap]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The overlap base-change map is an isomorphism when the overlap is affine. -/
lemma cechOverlapBaseChangeMap_isIso (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hI : IsAffineOpen (U ⊓ V)) :
    IsIso (cechOverlapBaseChangeMap s φ p g h M U V) := by
  let fI := openSectionsBaseChangeMap s φ p g h M (U ⊓ V)
  let _ : IsIso fI := by
    dsimp [fI]
    exact openSectionsBaseChangeMap_isIso s φ p g h M (U ⊓ V) hI
  dsimp only [cechOverlapBaseChangeMap]
  infer_instance

end GromovWitten.AlgebraicGeometry.Curves
