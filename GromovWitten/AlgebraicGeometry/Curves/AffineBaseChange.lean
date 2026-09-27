/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChange

/-!
# Affine pullback of associated module sheaves

The affine pullback statement is obtained from uniqueness of left adjoints.  The
right adjoints are identified by the fact that sections of a pushforward over
the top open are the sections over the inverse image of the top open; the
restriction of scalars records the resulting change of coefficient ring.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Global sections identify affine pushforward with restriction of scalars. -/
def affineGammaIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom := by
  let e := AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso φ
  let H := TopCat.Sheaf.forget (ModuleCat R) (Spec R).toTopCat ⋙
    (evaluation (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj (.op ⊤)
  dsimp [moduleSpecΓFunctor]
  exact Functor.isoWhiskerRight e H

def affinePullbackAdjunction :
    tilde.functor (R := R) ⋙ Scheme.Modules.pullback (Spec.map φ) ⊣
      Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
  (tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))

def affineExtendAdjunction :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor (R := S) ⊣
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (tilde.adjunction (R := S))

/-- Pullback of an affine associated module is associated to scalar extension. -/
def affinePullbackTildeIso :
    tilde.functor (R := R) ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor (R := S) := by
  exact
    ((conjugateIsoEquiv (affinePullbackAdjunction φ) (affineExtendAdjunction φ)).symm
      (affineGammaIso φ)).symm

/-- The affine pullback isomorphism is compatible with the two adjunction counits. -/
theorem affinePullbackTildeIso_counit {N : (Spec S).Modules} :
    (affinePullbackTildeIso φ).hom.app
        ((moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pushforward (Spec.map φ)).obj N)) ≫
      (ModuleCat.extendScalars φ.hom ⋙ tilde.functor (R := S)).map
        ((affineGammaIso φ).hom.app N) ≫
      (affineExtendAdjunction φ).counit.app N =
    (affinePullbackAdjunction φ).counit.app N := by
  let adj₁ := affinePullbackAdjunction φ
  let adj₂ := affineExtendAdjunction φ
  let e := affineGammaIso φ
  let i := ((conjugateIsoEquiv adj₁ adj₂).symm e).symm
  have h := conjugateEquiv_counit_symm adj₁ adj₂ e.hom N
  change i.hom.app
      ((moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj N)) ≫
      (ModuleCat.extendScalars φ.hom ⋙ tilde.functor (R := S)).map
        (e.hom.app N) ≫ adj₂.counit.app N = adj₁.counit.app N
  rw [h]
  change i.hom.app _ ≫ i.inv.app _ ≫ adj₁.counit.app N = _
  simp

end
end GromovWitten.AlgebraicGeometry.Curves
