/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffinePullbackGamma

/-!
# Sections on an affine open immersion

This file identifies sections of the pullback of a module along an affine open
immersion with sections of the original module on the image, and records the
canonical scalar map for this identification.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- Sections of an open-immersion pullback, identified with sections on its image. -/
def openPullbackSectionsIso (f : Spec R ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj
        ((moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pullback f).obj M)) ≅
      Γ(M, f.opensRange) := by
  let ePull :
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
          ((moduleSpecΓFunctor (R := R)).obj
            ((Scheme.Modules.pullback f).obj M)) ≅
        (forget₂ (ModuleCat R) AddCommGrpCat).obj
          ((moduleSpecΓFunctor (R := R)).obj
            ((Scheme.Modules.restrictFunctor f).obj M)) :=
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapIso
      ((moduleSpecΓFunctor (R := R)).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback f).app M))).symm
  let eRestrict := M.restrictAppIso f (⊤ : (Spec R).Opens)
  let eImage := M.presheaf.mapIso
    (eqToIso (Scheme.Hom.image_top_eq_opensRange f).symm).op
  exact ePull ≪≫ eRestrict ≪≫ eImage

/-- The scalar map from the affine source ring to the image's global sections. -/
def openPullbackSectionsRingEquiv (f : Spec R ⟶ X)
    [IsOpenImmersion f] : (R : Type u) ≃+* Γ(X, f.opensRange) :=
  (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.trans
    (AlgebraicGeometry.IsOpenImmersion.ΓIsoTop f).commRingCatIsoToRingEquiv

/-- The section identification is semilinear for the canonical scalar map. -/
lemma openPullbackSectionsIso_smul (f : Spec R ⟶ X)
    [IsOpenImmersion f] (M : X.Modules) (r : R)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback f).obj M)) :
    (openPullbackSectionsIso f M).hom (r • x) =
      openPullbackSectionsRingEquiv f r • (openPullbackSectionsIso f M).hom x := by
  let ePullM := ((moduleSpecΓFunctor (R := R)).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M)).symm
  have hPull (r : R) (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback f).obj M)) :
      ePullM.hom.hom (r • x) = r • ePullM.hom.hom x := by
    exact LinearMapClass.map_smul ePullM.hom.hom r x
  let eRestrict := M.restrictAppIso f (⊤ : (Spec R).Opens)
  let eImage := M.presheaf.mapIso
    (eqToIso (Scheme.Hom.image_top_eq_opensRange f).symm).op
  change (eRestrict ≪≫ eImage).hom (ePullM.hom.hom (r • x)) =
    openPullbackSectionsRingEquiv f r •
      (eRestrict ≪≫ eImage).hom (ePullM.hom.hom x)
  rw [hPull r x]
  let y : Γ(M.restrict f, (⊤ : (Spec R).Opens)) :=
    ePullM.hom.hom x
  change (eRestrict ≪≫ eImage).hom (r • y) =
    openPullbackSectionsRingEquiv f r • (eRestrict ≪≫ eImage).hom y
  rw [Scheme.Modules.smul_Spec_def]
  let r' := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv r
  change (eRestrict ≪≫ eImage).hom (r' • y) =
    (AlgebraicGeometry.IsOpenImmersion.ΓIsoTop f).hom r' •
      (eRestrict ≪≫ eImage).hom y
  change eImage.hom (eRestrict.hom (r' • y)) =
    (AlgebraicGeometry.IsOpenImmersion.ΓIsoTop f).hom r' •
      eImage.hom (eRestrict.hom y)
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
  exact M.map_smul (eqToIso (Scheme.Hom.image_top_eq_opensRange f).symm).hom
    ((Scheme.Hom.appIso f (⊤ : (Spec R).Opens)).inv r')
    (eRestrict.hom y)

end GromovWitten.AlgebraicGeometry.Curves
