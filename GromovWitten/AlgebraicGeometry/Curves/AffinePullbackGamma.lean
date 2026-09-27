/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineAdjunctionCompatibility
import GromovWitten.CategoryTheory.BeckChevalley
/-!
# Affine pullback and global sections

The canonical map from scalar extension of global sections to global sections of
pullback is invertible on quasi-coherent modules. Its adjunction characterization
and naturality allow comparisons of canonical geometric base-change morphisms.
-/

open CategoryTheory Limits
open scoped ChangeOfRings
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
/-- The canonical map from scalar extension of sections to sections of pullback. -/
def affinePullbackGammaMap (M : (Spec R).Modules) :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ⟶
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) :=
  (tilde.adjunction (R := S)).unit.app _ ≫
    (moduleSpecΓFunctor (R := S)).map
      ((affinePullbackTildeIso φ).inv.app (moduleSpecΓFunctor.obj M) ≫
        (Scheme.Modules.pullback (Spec.map φ)).map ((tilde.adjunction (R := R)).counit.app M))
set_option backward.isDefEq.respectTransparency false in
/-- Pullback of a quasi-coherent module on an affine scheme is computed by scalar extension. -/
instance affinePullbackGammaMap_isIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsIso (affinePullbackGammaMap φ M) := by
  have : IsIso ((tilde.adjunction (R := R)).counit.app M) := by
    change IsIso M.fromTildeΓ
    infer_instance
  dsimp only [affinePullbackGammaMap]
  rw [Functor.map_comp]
  infer_instance
set_option backward.isDefEq.respectTransparency false in
/-- The comparison is adjoint to global sections of the geometric pullback unit. -/
lemma affinePullbackGammaMap_homEquiv (M : (Spec R).Modules) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
        (affinePullbackGammaMap φ M) =
      (moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
        (affineGammaIso φ).hom.app ((Scheme.Modules.pullback (Spec.map φ)).obj M) := by
  let g := (affinePullbackTildeIso φ).inv.app (moduleSpecΓFunctor.obj M) ≫
    (Scheme.Modules.pullback (Spec.map φ)).map ((tilde.adjunction (R := R)).counit.app M)
  have h := affinePullbackTildeIso_homEquiv φ g
  have hg : (affinePullbackTildeIso φ).hom.app (moduleSpecΓFunctor.obj M) ≫ g =
      (Scheme.Modules.pullback (Spec.map φ)).map ((tilde.adjunction (R := R)).counit.app M) := by
    dsimp [g]
    simp
  rw [hg] at h
  have hext : (affineExtendAdjunction φ).homEquiv _ _ g =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
        (affinePullbackGammaMap φ M) := by
    rw [affineExtendAdjunction, Adjunction.comp_homEquiv]
    rfl
  rw [hext] at h
  have hpull : (affinePullbackAdjunction φ).homEquiv _ _
      ((Scheme.Modules.pullback (Spec.map φ)).map ((tilde.adjunction (R := R)).counit.app M)) =
      (moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) := by
    exact Adjunction.comp_homEquiv_map_counit (tilde.adjunction (R := R))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) M
  rw [hpull] at h
  exact h
set_option backward.isDefEq.respectTransparency false in
/-- The affine pullback/global-sections comparison is natural in the module. -/
lemma affinePullbackGammaMap_naturality {M N : (Spec R).Modules} (f : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map ((moduleSpecΓFunctor (R := R)).map f) ≫
        affinePullbackGammaMap φ N =
      affinePullbackGammaMap φ M ≫ (moduleSpecΓFunctor (R := S)).map
        ((Scheme.Modules.pullback (Spec.map φ)).map f) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    affinePullbackGammaMap_homEquiv, affinePullbackGammaMap_homEquiv]
  have hγ := (affineGammaIso φ).hom.naturality
    ((Scheme.Modules.pullback (Spec.map φ)).map f)
  dsimp only [Functor.comp_map] at hγ
  rw [Category.assoc, ← hγ]
  simp only [← Functor.map_comp, ← Category.assoc]
  have h := (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality f
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h
  rw [h]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the comparison on the scalar-extension adjunction generators. -/
lemma affinePullbackGammaMap_one_tmul (M : (Spec R).Modules)
    (n : (moduleSpecΓFunctor (R := R)).obj M) :
    affinePullbackGammaMap φ M ((1 : S) ⊗ₜ[R, φ.hom] n) =
      ((affineGammaIso φ).hom.app ((Scheme.Modules.pullback (Spec.map φ)).obj M))
        (((moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M)) n) := by
  have h := ConcreteCategory.congr_hom (affinePullbackGammaMap_homEquiv φ M) n
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at h
  exact h

private theorem eq_of_eq_map {α : Type u} (F : α → α) {x y : α}
    (h : x = F y) (hF : ∀ z, F z = z) : x = y :=
  h.trans (hF y)

private lemma affineGammaIso_apply {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec S).Modules) (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj M)) :
    ((affineGammaIso φ).hom.app M) x = x := by
  dsimp [affineGammaIso, moduleSpecΓFunctor, modulesSpecToSheaf]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On a tensor generator, the affine comparison is global sections of the pullback unit. -/
lemma affinePullbackGammaMap_one_tmul_unit
    (M : (Spec R).Modules) (x : (moduleSpecΓFunctor (R := R)).obj M) :
    affinePullbackGammaMap φ M ((1 : S) ⊗ₜ[R, φ.hom] x) =
      ((moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M)) x := by
  refine eq_of_eq_map
    (F := fun z => ((affineGammaIso φ).hom.app
      ((Scheme.Modules.pullback (Spec.map φ)).obj M)) z)
    (x := affinePullbackGammaMap φ M ((1 : S) ⊗ₜ[R, φ.hom] x))
    (y := ((moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M)) x) ?_ ?_
  · exact affinePullbackGammaMap_one_tmul φ M x
  · intro z
    exact affineGammaIso_apply φ ((Scheme.Modules.pullback (Spec.map φ)).obj M) z

end
end GromovWitten.AlgebraicGeometry.Curves
