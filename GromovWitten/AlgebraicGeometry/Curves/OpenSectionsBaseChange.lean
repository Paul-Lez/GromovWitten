/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenSections
import GromovWitten.AlgebraicGeometry.Curves.PushforwardSectionsLinear
import GromovWitten.AlgebraicGeometry.Curves.AffineSectionsBaseChange
import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairBaseModule

/-!
# Base change for sections on open subschemes

This file constructs the scalar-extension map from sections on an affine open to sections on its
geometric pullback in a Cartesian square, together with its affine-open isomorphism theorem.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- Sections on an open, viewed as sections of the pushforward from that open, are identified
with the base-linear section module. -/
def openSectionsOverBaseIso (s : X ⟶ Spec R) (M : X.Modules) (U : X.Opens) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (U.ι ≫ s)).obj
      ((Scheme.Modules.pullback U.ι).obj M)) ≅ baseSectionModule s U M :=
  ((pushforwardSectionsBaseLinearEquiv (U.ι ≫ s) ((Scheme.Modules.pullback U.ι).obj M)).trans
    ((baseTopSectionsEquiv (U.ι ≫ s) ((Scheme.Modules.pullback U.ι).obj M)).symm.trans
      ((openPullbackBaseSectionsLinearEquiv s U.ι M ⊤).trans
        (baseSectionCongr s M U.ι_image_top)))).toModuleIso

/-- Pullback of a module first to an open and then along a morphism agrees with pullback along
the inverse-image open. -/
def restrictionPullbackIso (p : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    (Scheme.Modules.pullback (p ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj M) ≅
      (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackComp (p ∣_ U) U.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι p U)).app M ≪≫
    ((Scheme.Modules.pullbackComp (p ⁻¹ᵁ U).ι p).app M).symm

variable {T : CommRingCat.{u}}

/-- The canonical scalar-extension map on sections over an open in a Cartesian square. -/
def openSectionsBaseChangeMap (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) (U : X.Opens) :
    (ModuleCat.extendScalars φ.hom).obj (baseSectionModule s U M) ⟶
      baseSectionModule g (p ⁻¹ᵁ U) ((Scheme.Modules.pullback p).obj M) :=
  (ModuleCat.extendScalars φ.hom).map (openSectionsOverBaseIso s M U).inv ≫
    sectionsBaseChangeMap (U.ι ≫ s) φ (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ g)
      ((isPullback_morphismRestrict p U).paste_vert h) ((Scheme.Modules.pullback U.ι).obj M) ≫
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforward ((p ⁻¹ᵁ U).ι ≫ g)).map
      (restrictionPullbackIso p M U).hom) ≫
    (openSectionsOverBaseIso g ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U)).hom

/-- The open-section base-change map is an isomorphism when the open is affine and the original
module is quasicoherent. -/
lemma openSectionsBaseChangeMap_isIso (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso (openSectionsBaseChangeMap s φ p g h M U) := by
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffineHom (U.ι ≫ s) := inferInstance
  dsimp only [openSectionsBaseChangeMap]
  infer_instance

end GromovWitten.AlgebraicGeometry.Curves
