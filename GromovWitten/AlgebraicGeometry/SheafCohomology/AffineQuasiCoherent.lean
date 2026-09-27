/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineAcyclic
import GromovWitten.AlgebraicGeometry.SheafCohomology.OpenRestriction
import GromovWitten.AlgebraicGeometry.SheafCohomology.LocalVanishing
import GromovWitten.AlgebraicGeometry.Curves.CohomologyBaseChange

/-!
# Quasi-coherent cohomology on an affine scheme

The affine acyclicity theorem in `AffineAcyclic` is stated for an associated module sheaf on a
`Spec`.  This file supplies the geometric transport needed for an arbitrary affine scheme.  A
quasi-coherent module is restricted along the inverse of `X.isoSpec`; Mathlib's actual affine
quasi-coherence theorem then gives the `fromTildeΓ` isomorphism.  Restriction along the inverse
isomorphism transports that isomorphism back to `X`.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

abbrev affineGlobalRing (X : Scheme.{u}) : CommRingCat.{u} := Γ(X, ⊤)

/-- The restriction to the canonical affine `Spec` of an affine scheme. -/
abbrev affineSpecModule {X : Scheme.{u}} [IsAffine X] (M : X.Modules) :
    (Spec (affineGlobalRing X)).Modules :=
  (Scheme.Modules.restrictFunctor X.isoSpec.inv).obj M

/-- A quasi-coherent module restricted to the canonical affine `Spec` remains quasi-coherent. -/
theorem affineSpecModule_isQuasicoherent {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineSpecModule M).IsQuasicoherent := by
  exact Scheme.Modules.isQuasicoherent_restrictFunctor X.isoSpec.inv M

/-- The module on the canonical `Spec` which gives its quasi-coherent sheaf by tilde. -/
abbrev affineSpecModuleSections {X : Scheme.{u}} [IsAffine X] (M : X.Modules) :
    ModuleCat (affineGlobalRing X) :=
  moduleSpecΓFunctor.obj (affineSpecModule M)

/-- The actual affine `fromTildeΓ` isomorphism for the restricted module. -/
noncomputable def affineSpecModule_tildeIso {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] :
    (tilde.functor (affineGlobalRing X)).obj (affineSpecModuleSections M) ≅
      affineSpecModule M := by
  let hM : (affineSpecModule M).IsQuasicoherent := affineSpecModule_isQuasicoherent M
  let hIso : IsIso (affineSpecModule M).fromTildeΓ :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _ (affineSpecModule M) hM
  exact @asIso _ _ _ _ (affineSpecModule M).fromTildeΓ hIso

/-- The module isomorphism induced by the two inverse restriction functors of `X.isoSpec`. -/
noncomputable def affineSpecModule_restrictIso {X : Scheme.{u}} [IsAffine X] (M : X.Modules) :
    M ≅ (Scheme.Modules.restrictFunctor X.isoSpec.hom).obj (affineSpecModule M) := by
  exact (Scheme.Modules.restrictFunctorId (X := X)).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorCongr (X.isoSpec.hom_inv_id)).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).app M

/-- The underlying abelian sheaf on an affine scheme is the restriction of an actual tilde. -/
noncomputable def affineQuasicoherentTildeIso {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] :
    (moduleToSheafAb X).obj M ≅
      (X.isoSpec.hom.isOpenEmbedding.sheafPullback Ab).obj
        ((moduleToSheafAb (Spec (affineGlobalRing X))).obj
          ((tilde.functor (affineGlobalRing X)).obj (affineSpecModuleSections M))) := by
  let eM := (moduleToSheafAb X).mapIso (affineSpecModule_restrictIso M)
  let eN := (moduleToSheafAb (Spec (affineGlobalRing X))).mapIso
    (affineSpecModule_tildeIso M)
  exact eM ≪≫ (X.isoSpec.hom.isOpenEmbedding.sheafPullback Ab).mapIso eN.symm

private theorem affine_top_image {X : Scheme.{u}} [IsAffine X] :
    X.isoSpec.hom.isOpenEmbedding.functor.obj (⊤ : Opens X) =
      (⊤ : Opens (Spec (affineGlobalRing X))) := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨X.isoSpec.inv.base x, by simp, by simp⟩

/-- Positive derived pushforward of a quasi-coherent module on an affine scheme vanishes. -/
theorem isZero_affine_rightDerived_succ {X : Scheme.{u}} [IsAffine X]
    [IsNoetherianRing (affineGlobalRing X)] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X.toTopCat)).rightDerived
      (n + 1)).obj ((moduleToSheafAb X).obj M)) := by
  let N := affineSpecModule M
  let Q := affineSpecModuleSections M
  let eT := affineQuasicoherentTildeIso M
  have hspec : IsZero (((sections (⊤ : Opens (Spec (affineGlobalRing X)))).rightDerived
      (n + 1)).obj ((moduleToSheafAb (Spec (affineGlobalRing X))).obj
        ((tilde.functor (affineGlobalRing X)).obj Q))) := by
    have hz := isZero_affineToPoint_rightDerived_succ (affineGlobalRing X) Q n
    have hg : IsZero (PointSheaves.globalSections.{u}.obj
        (((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
          (affineToPoint (affineGlobalRing X))).rightDerived (n + 1)).obj
          ((moduleToSheafAb (Spec (affineGlobalRing X))).obj
            ((tilde.functor (affineGlobalRing X)).obj Q)))) := by
      exact Functor.map_isZero PointSheaves.globalSections.{u} hz
    exact IsZero.of_iso hg (derivedSectionsTopIso
      (Spec (affineGlobalRing X)).toTopCat
      ((moduleToSheafAb (Spec (affineGlobalRing X))).obj
        ((tilde.functor (affineGlobalRing X)).obj Q)) (n + 1))
  have hopenRaw := derivedSectionsOpenIso X.isoSpec.hom.isOpenEmbedding
    ((moduleToSheafAb (Spec (affineGlobalRing X))).obj
      ((tilde.functor (affineGlobalRing X)).obj Q)) (n + 1)
  rw [affine_top_image] at hopenRaw
  have hopen :
      (((sections (⊤ : Opens (Spec (affineGlobalRing X)))).rightDerived (n + 1)).obj
          ((moduleToSheafAb (Spec (affineGlobalRing X))).obj
            ((tilde.functor (affineGlobalRing X)).obj Q))) ≅
        (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj
          ((X.isoSpec.hom.isOpenEmbedding.sheafPullback Ab).obj
            ((moduleToSheafAb (Spec (affineGlobalRing X))).obj
              ((tilde.functor (affineGlobalRing X)).obj Q)))) :=
    by
      simpa only [Ab] using hopenRaw
  have hpullback : IsZero (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj
      ((X.isoSpec.hom.isOpenEmbedding.sheafPullback Ab).obj
        ((moduleToSheafAb (Spec (affineGlobalRing X))).obj
          ((tilde.functor (affineGlobalRing X)).obj Q)))) := by
    exact IsZero.of_iso hspec hopen.symm
  have hsections : IsZero (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj
      ((moduleToSheafAb X).obj M)) := by
    exact IsZero.of_iso hpullback
      (((sections (⊤ : Opens X)).rightDerived (n + 1)).mapIso eT)
  have hg : IsZero (PointSheaves.globalSections.{u}.obj
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X.toTopCat)).rightDerived
        (n + 1)).obj ((moduleToSheafAb X).obj M))) := by
    exact IsZero.of_iso hsections (derivedSectionsTopIso X.toTopCat
      ((moduleToSheafAb X).obj M) (n + 1)).symm
  exact PointSheaves.isZero_of_globalSections_obj _ hg

/-- Positive derived sections on an affine scheme vanish for a quasi-coherent module. -/
theorem isZero_affine_sections_rightDerived_succ {X : Scheme.{u}} [IsAffine X]
    [IsNoetherianRing (affineGlobalRing X)] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj
      ((moduleToSheafAb X).obj M)) := by
  have hz := isZero_affine_rightDerived_succ M n
  have hg : IsZero (PointSheaves.globalSections.{u}.obj
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X.toTopCat)).rightDerived
        (n + 1)).obj ((moduleToSheafAb X).obj M))) := by
    exact Functor.map_isZero PointSheaves.globalSections.{u} hz
  have he := derivedSectionsTopIso X.toTopCat ((moduleToSheafAb X).obj M) (n + 1)
  have he' :
      (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj ((moduleToSheafAb X).obj M)) ≅
        PointSheaves.globalSections.{u}.obj
          (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toPoint X.toTopCat)).rightDerived
            (n + 1)).obj ((moduleToSheafAb X).obj M)) := by
    simpa only [Ab] using he
  exact IsZero.of_iso hg he'

/-- Positive derived pushforward along an affine morphism vanishes on quasi-coherent modules.

The proof uses the affine-open basis of the target.  On an affine target open, the inverse
image is affine by `IsAffineHom`, and restriction of a quasi-coherent module is
quasi-coherent; `derivedSectionsOpenIso` identifies the resulting local derived sections
with the derived sections over that inverse image.
-/
theorem isZero_affineHom_rightDerived_succ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).rightDerived
      (n + 1)).obj ((moduleToSheafAb X).obj M)) := by
  refine isZero_rightDerived_pushforward_of_basis f.base
    ((moduleToSheafAb X).obj M) (n + 1) Y.isBasis_affineOpens ?_
  intro U hU
  let V : X.Opens := f ⁻¹ᵁ U
  have hVaff : IsAffineOpen V := IsAffineHom.isAffine_preimage _ hU
  have hVaffI : IsAffine V.toScheme := hVaff
  let j : V.toScheme ⟶ X := V.ι
  let N := (Scheme.Modules.restrictFunctor j).obj M
  let hN : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j M
  let hVring : IsNoetherianRing (affineGlobalRing V.toScheme) :=
    @IsLocallyNoetherian.component_noetherian V.toScheme inferInstance
      ⟨⊤, @isAffineOpen_top V.toScheme hVaffI⟩
  have hVzero : IsZero (((sections (⊤ : Opens V.toScheme)).rightDerived (n + 1)).obj
      ((moduleToSheafAb V.toScheme).obj N)) := by
    exact @isZero_affine_sections_rightDerived_succ V.toScheme hVaffI hVring N hN n
  have himage : j.isOpenEmbedding.functor.obj (⊤ : Opens V.toScheme) =
      (Opens.map f.base).obj U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change f y.1 ∈ U
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by trivial⟩
  have hopen := derivedSectionsOpenIso j.isOpenEmbedding
    ((moduleToSheafAb X).obj M) (n + 1)
  rw [himage] at hopen
  have hmodule :
      ((moduleToSheafAb V.toScheme).obj N) ≅
        ((j.isOpenEmbedding.sheafPullback Ab).obj ((moduleToSheafAb X).obj M)) := by
    rfl
  have hopen' :
      (((sections ((Opens.map f.base).obj U)).rightDerived (n + 1)).obj
          ((moduleToSheafAb X).obj M)) ≅
        (((sections (⊤ : Opens V.toScheme)).rightDerived (n + 1)).obj
          ((moduleToSheafAb V.toScheme).obj N)) := by
    exact hopen ≪≫
      (((sections (⊤ : Opens V.toScheme)).rightDerived (n + 1)).mapIso hmodule.symm)
  exact IsZero.of_iso hVzero hopen'

end GromovWitten.AlgebraicGeometry.SheafCohomology
