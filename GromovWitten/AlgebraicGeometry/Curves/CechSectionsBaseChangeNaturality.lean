/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CechSectionsBaseChange
import GromovWitten.AlgebraicGeometry.Curves.OpenSectionsBaseChangeNaturality

/-!
# Generators for Čech section base change

The scalar-extension maps on the Čech pair and overlap are determined on the
canonical tensor generators by the pullback/pushforward adjunction unit.
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open scoped ChangeOfRings
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

private lemma pairScalarExtension_one_tmul {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {P Q : ModuleCat.{u} A} {P' Q' : ModuleCat.{u} B}
    (f : (ModuleCat.extendScalars φ).obj P ⟶ P')
    (g : (ModuleCat.extendScalars φ).obj Q ⟶ Q') (z : P × Q) :
    ((ModuleCat.extendScalarsProdIso φ P Q).hom ≫ ModuleCat.ofHom
      (f.hom.prodMap g.hom)) ((1 : B) ⊗ₜ[A, φ] z) =
      (f ((1 : B) ⊗ₜ[A, φ] z.1), g ((1 : B) ⊗ₜ[A, φ] z.2)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The Čech pair base-change map sends a tensor generator to the two pullback unit maps. -/
lemma cechPairBaseChangeMap_one_tmul (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) (U V : X.Opens)
    (z : (ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
      (sectionsPairModule M U V)) :
    cechPairBaseChangeMap s φ p g h M U V ((1 : T) ⊗ₜ[R, φ.hom] z) =
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app U z.1,
       ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app V z.2) := by
  let z' : baseSectionModule s U M × baseSectionModule s V M :=
    (baseCechPairSectionsIso s M U V).inv z
  have hp := pairScalarExtension_one_tmul φ.hom
    (openSectionsBaseChangeMap s φ p g h M U)
    (openSectionsBaseChangeMap s φ p g h M V) z'
  have hu := openSectionsBaseChangeMap_one_tmul s φ p g h M U z'.1
  have hv := openSectionsBaseChangeMap_one_tmul s φ p g h M V z'.2
  have hp' := hp.trans (congrArg₂ Prod.mk hu hv)
  have hp'' := congrArg
    ((baseCechPairSectionsIso g ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)).hom) hp'
  simp only [ConcreteCategory.comp_apply] at hp''
  simp only [cechPairBaseChangeMap, ConcreteCategory.comp_apply,
    ModuleCat.ExtendScalars.map_tmul]
  exact hp''.trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The overlap base-change map sends a tensor generator to the pullback unit map. -/
lemma cechOverlapBaseChangeMap_one_tmul (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) (U V : X.Opens)
    (x : (ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).obj
      (sectionModuleCat M (U ⊓ V))) :
    cechOverlapBaseChangeMap s φ p g h M U V ((1 : T) ⊗ₜ[R, φ.hom] x) =
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app (U ⊓ V) x := by
  have hi := openSectionsBaseChangeMap_one_tmul s φ p g h M (U ⊓ V)
    ((baseCechOverlapSectionsIso s M U V).inv x)
  simp only [cechOverlapBaseChangeMap, ConcreteCategory.comp_apply,
    ModuleCat.ExtendScalars.map_tmul]
  rw [hi]
  rfl

end GromovWitten.AlgebraicGeometry.Curves
