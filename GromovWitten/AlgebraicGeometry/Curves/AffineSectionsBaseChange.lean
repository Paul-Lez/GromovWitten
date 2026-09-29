/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineBaseChangeIsomorphism
import GromovWitten.AlgebraicGeometry.Curves.AffinePullbackGamma
import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeSections

/-!
# Affine sections and base change

This file records the canonical scalar-extension map on global sections for a Cartesian square
over an affine base, together with its isomorphism, generator, and module naturality properties.
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open scoped ChangeOfRings

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- Global sections of a pushforward to an affine base, with its canonical base-ring action,
are the usual base-linear sections module. -/
def pushforwardSectionsBaseLinearEquiv (s : X ⟶ Spec R) (M : X.Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward s).obj M) ≃ₗ[R]
      sectionsModuleCat R s M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change _ = baseRingHom R s r • (show Γ(M, ⊤) from m)
    simp only [baseRingHom, CommRingCat.comp_apply]
    rfl

/-- The canonical scalar-extension map on affine global sections in a Cartesian square. -/
def sectionsBaseChangeMap (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) :
    (ModuleCat.extendScalars φ.hom).obj
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward s).obj M)) ⟶
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pullback p).obj M)) :=
  affinePullbackGammaMap φ ((Scheme.Modules.pushforward s).obj M) ≫
    moduleSpecΓFunctor.map ((modulePushforwardBaseChangeNatTrans s (Spec.map φ) p g h).app M)

/-- The affine sections base-change map is invertible when the source map is affine and the module
is quasicoherent. -/
instance sectionsBaseChangeMap_isIso (s : X ⟶ Spec R) [IsAffineHom s]
    (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (sectionsBaseChangeMap s φ p g h M) := by
  have := moduleBaseChange_isIso_of_isAffineHom s (Spec.map φ) p g h M
  dsimp only [sectionsBaseChangeMap]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- On the tensor generator, the affine sections base-change map is the pullback-pushforward
adjunction unit on sections. -/
lemma sectionsBaseChangeMap_one_tmul (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules)
    (m : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward s).obj M)) :
    sectionsBaseChangeMap s φ p g h M ((1 : T) ⊗ₜ[R, φ.hom] m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ m := by
  change moduleSpecΓFunctor.map
    ((modulePushforwardBaseChangeNatTrans s (Spec.map φ) p g h).app M)
      (affinePullbackGammaMap φ ((Scheme.Modules.pushforward s).obj M)
        ((1 : T) ⊗ₜ[R, φ.hom] m)) = _
  rw [affinePullbackGammaMap_one_tmul_unit]
  exact moduleBaseChange_unit_app_top s (Spec.map φ) p g h M m

/-- The affine sections base-change map is natural in the quasicoherent module. -/
lemma sectionsBaseChangeMap_naturality (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    {M N : X.Modules} (f : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map
        (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward s).map f)) ≫
      sectionsBaseChangeMap s φ p g h N =
    sectionsBaseChangeMap s φ p g h M ≫
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pullback p).map f)) := by
  simp only [sectionsBaseChangeMap]
  rw [← Category.assoc, affinePullbackGammaMap_naturality, Category.assoc,
    ← Functor.map_comp]
  have hn := (modulePushforwardBaseChangeNatTrans s (Spec.map φ) p g h).naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hn, Functor.map_comp, Category.assoc]

end GromovWitten.AlgebraicGeometry.Curves
