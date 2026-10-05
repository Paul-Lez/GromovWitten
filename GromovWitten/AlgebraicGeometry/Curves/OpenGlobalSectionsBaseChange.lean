/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.OpenSectionsBaseChangeNaturality
import GromovWitten.AlgebraicGeometry.Curves.AffineSectionsBaseChange
/-!
# Comparing open-top and global-sections base change

The canonical open-section base-change map on the top open is the usual affine
base global-sections comparison after identifying the section modules. In
particular, the two maps are invertible under exactly the same conditions.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
open scoped TensorProduct ChangeOfRings
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}
/-- Identify top-open base-linear sections with global sections of the pushforward. -/
def baseTopPushforwardSectionsIso (s : X ⟶ Spec R) (M : X.Modules) :
    baseSectionModule s ⊤ M ≅ moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward s).obj M) :=
  (baseTopSectionsEquiv s M).toModuleIso ≪≫
    (pushforwardSectionsBaseLinearEquiv s M).toModuleIso.symm
private lemma baseTopPushforwardSectionsIso_hom_apply (s : X ⟶ Spec R) (M : X.Modules)
    (x : baseSectionModule s ⊤ M) :
    (baseTopPushforwardSectionsIso s M).hom x =
      (show moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward s).obj M) from x) := rfl
set_option backward.isDefEq.respectTransparency false in
private lemma topSections_transport (s : X ⟶ Spec R) (φ : R ⟶ T) (g : Y ⟶ Spec T)
    (M : X.Modules) (N : Y.Modules)
    (f : (ModuleCat.extendScalars φ.hom).obj (baseSectionModule s ⊤ M) ⟶
      baseSectionModule g ⊤ N)
    (k : (ModuleCat.extendScalars φ.hom).obj
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward s).obj M)) ⟶
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward g).obj N))
    (hf : ∀ x : baseSectionModule s ⊤ M,
      (f ((1 : T) ⊗ₜ[R, φ.hom] x) : Γ(N, ⊤)) =
      k ((1 : T) ⊗ₜ[R, φ.hom] ((baseTopPushforwardSectionsIso s M).hom x))) :
    f ≫ (baseTopPushforwardSectionsIso g N).hom =
      (ModuleCat.extendScalars φ.hom).map (baseTopPushforwardSectionsIso s M).hom ≫ k := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  simp only [ConcreteCategory.comp_apply, ModuleCat.ExtendScalars.map_tmul,
    baseTopPushforwardSectionsIso_hom_apply]
  exact hf x
set_option backward.isDefEq.respectTransparency false in
/-- The top-open comparison agrees with canonical base change on global sections. -/
lemma openSectionsBaseChangeMap_top_comp
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) :
    openSectionsBaseChangeMap s φ p g h M ⊤ ≫
      (baseTopPushforwardSectionsIso g ((Scheme.Modules.pullback p).obj M)).hom =
      (ModuleCat.extendScalars φ.hom).map (baseTopPushforwardSectionsIso s M).hom ≫
        sectionsBaseChangeMap s φ p g h M := by
  apply topSections_transport s φ g M ((Scheme.Modules.pullback p).obj M)
  intro x
  exact (openSectionsBaseChangeMap_one_tmul s φ p g h M ⊤ x).trans
    (sectionsBaseChangeMap_one_tmul s φ p g h M
      ((baseTopPushforwardSectionsIso s M).hom x)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The open-top base-change map is invertible exactly when the canonical
global-sections base-change map is. -/
lemma isIso_openSectionsBaseChangeMap_top_iff
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) :
    IsIso (openSectionsBaseChangeMap s φ p g h M ⊤) ↔
      IsIso (sectionsBaseChangeMap s φ p g h M) := by
  let eR : baseSectionModule s ⊤ M ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward s).obj M) :=
    baseTopPushforwardSectionsIso s M
  let eT : baseSectionModule g ⊤ ((Scheme.Modules.pullback p).obj M) ≅
      moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M)) :=
    baseTopPushforwardSectionsIso g ((Scheme.Modules.pullback p).obj M)
  have hcomp := openSectionsBaseChangeMap_top_comp s φ p g h M
  calc
    IsIso (openSectionsBaseChangeMap s φ p g h M ⊤) ↔
        IsIso (openSectionsBaseChangeMap s φ p g h M ⊤ ≫ eT.hom) :=
      (isIso_comp_right_iff _ _).symm
    _ ↔ IsIso ((ModuleCat.extendScalars φ.hom).map eR.hom ≫
        sectionsBaseChangeMap s φ p g h M) := by rw [hcomp]
    _ ↔ IsIso (sectionsBaseChangeMap s φ p g h M) := isIso_comp_left_iff _ _

end GromovWitten.AlgebraicGeometry.Curves
