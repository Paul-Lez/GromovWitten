/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineSectionsBaseChange

/-!
# The canonical degree-zero cohomology base-change map

The map here is the actual transported global-sections base-change map.  Its definition makes no
isomorphism claim; invertibility is established separately under appropriate geometric hypotheses.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- Degree-zero cohomology over an affine base, transported to sections of the pushforward. -/
def cohomologyZeroPushforwardSectionsIso (s : X ⟶ Spec R) (M : X.Modules) :
    cohomologyModuleCat R s M 0 ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward s).obj M) :=
  (cohomologyZeroBaseLinearEquiv (R : Type u) s M).toModuleIso ≪≫
    (pushforwardSectionsBaseLinearEquiv s M).symm.toModuleIso

/-- The canonical degree-zero cohomology base-change map transported from global sections. -/
def canonicalCohomologyZeroBaseChangeMap
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) :
    (ModuleCat.extendScalars φ.hom).obj (cohomologyModuleCat R s M 0) ⟶
      cohomologyModuleCat T g ((Scheme.Modules.pullback p).obj M) 0 :=
  (ModuleCat.extendScalars φ.hom).map (cohomologyZeroPushforwardSectionsIso s M).hom ≫
    sectionsBaseChangeMap s φ p g h M ≫
      (cohomologyZeroPushforwardSectionsIso g ((Scheme.Modules.pullback p).obj M)).inv

set_option backward.isDefEq.respectTransparency false in
/-- On the scalar-extension unit generator, the canonical map is the pullback adjunction unit. -/
lemma canonicalCohomologyZeroBaseChangeMap_one_tmul
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) (x : cohomologyModuleCat R s M 0) :
    cohomologyZeroBaseLinearEquiv (T : Type u) g ((Scheme.Modules.pullback p).obj M)
      (canonicalCohomologyZeroBaseChangeMap s φ p g h M ((1 : T) ⊗ₜ[R, φ.hom] x)) =
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤
      (cohomologyZeroBaseLinearEquiv (R : Type u) s M x) := by
  simp only [canonicalCohomologyZeroBaseChangeMap, ConcreteCategory.comp_apply,
    ModuleCat.ExtendScalars.map_tmul]
  rw [sectionsBaseChangeMap_one_tmul]
  change cohomologyZeroBaseLinearEquiv (T : Type u) g ((Scheme.Modules.pullback p).obj M)
    ((cohomologyZeroBaseLinearEquiv (T : Type u) g ((Scheme.Modules.pullback p).obj M)).symm
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤
        (cohomologyZeroBaseLinearEquiv (R : Type u) s M x))) = _
  exact LinearEquiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- The transported degree-zero base-change map is the canonical Beck--Chevalley map on
global sections. -/
lemma canonicalCohomologyZeroBaseChangeMap_comp_pushforwardSectionsIso
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) :
    canonicalCohomologyZeroBaseChangeMap s φ p g h M ≫
        (cohomologyZeroPushforwardSectionsIso g
          ((Scheme.Modules.pullback p).obj M)).hom =
      (ModuleCat.extendScalars φ.hom).map
          (cohomologyZeroPushforwardSectionsIso s M).hom ≫
        affinePullbackGammaMap φ ((Scheme.Modules.pushforward s).obj M) ≫
          moduleSpecΓFunctor.map
            (canonicalPushforwardBaseChangeComparison s M (Spec.map φ) p g h) := by
  unfold canonicalCohomologyZeroBaseChangeMap
  simp only [Category.assoc]
  rw [Iso.inv_hom_id]
  simp only [Category.comp_id]
  unfold sectionsBaseChangeMap
  rw [modulePushforwardBaseChangeNatTrans_app_eq_canonical]

end GromovWitten.AlgebraicGeometry.Curves
