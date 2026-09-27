/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineBaseChange

/-!
# Compatibility of affine adjunctions

The comparison between pullback of an associated module sheaf and extension of
scalars is compatible with the corresponding adjunction units and hom-equivalences.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-! The unit form of the conjugate-adjunction compatibility used by the affine pullback iso. -/
theorem affinePullbackTildeIso_unit {Q : ModuleCat.{u} R} :
    (affinePullbackAdjunction φ).unit.app Q ≫
        (affineGammaIso φ).hom.app
          ((Scheme.Modules.pullback (Spec.map φ)).obj
            ((tilde.functor (R := R)).obj Q)) =
      (affineExtendAdjunction φ).unit.app Q ≫
        (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).map
          ((affinePullbackTildeIso φ).inv.app Q) := by
  let adj₁ := affinePullbackAdjunction φ
  let adj₂ := affineExtendAdjunction φ
  let γ := affineGammaIso φ
  let e := affinePullbackTildeIso φ
  change adj₁.unit.app Q ≫ γ.hom.app
      ((Scheme.Modules.pullback (Spec.map φ)).obj
        ((tilde.functor (R := R)).obj Q)) =
    adj₂.unit.app Q ≫
      (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).map
        (((conjugateEquiv adj₁ adj₂).symm γ.hom).app Q)
  exact unit_conjugateEquiv_symm adj₁ adj₂ γ.hom Q

theorem affinePullbackTildeIso_homEquiv {Q : ModuleCat.{u} R}
    {N : (Spec S).Modules}
    (g : ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor (R := S)).obj Q) ⟶ N) :
    (affineExtendAdjunction φ).homEquiv Q N g =
      (affinePullbackAdjunction φ).homEquiv Q N
          ((affinePullbackTildeIso φ).hom.app Q ≫ g) ≫
        (affineGammaIso φ).hom.app N := by
  let adj₁ := affinePullbackAdjunction φ
  let adj₂ := affineExtendAdjunction φ
  let γ := affineGammaIso φ
  let e := affinePullbackTildeIso φ
  have hunit :
      adj₁.unit.app Q ≫ γ.hom.app ((tilde.functor (R := R) ⋙
          Scheme.Modules.pullback (Spec.map φ)).obj Q) =
        adj₂.unit.app Q ≫
          (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).map
            (e.inv.app Q) := by
    exact affinePullbackTildeIso_unit φ (Q := Q)
  change adj₂.homEquiv Q N g =
    adj₁.homEquiv Q N (e.hom.app Q ≫ g) ≫ γ.hom.app N
  simp only [Adjunction.homEquiv_unit]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [γ.hom.naturality]
  rw [γ.hom.naturality_assoc]
  rw [← Category.assoc]
  rw [hunit]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← Category.assoc]
  rw [e.inv_hom_id_app]
  simp only [Category.id_comp]


end
end GromovWitten.AlgebraicGeometry.Curves
