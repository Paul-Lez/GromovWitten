/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffinePullbackGamma
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeSections
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward
import GromovWitten.Algebra.ModuleCatBaseChange
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine compatibility of canonical module base change

Global sections identify the canonical geometric comparison with the algebraic
base-change map. The unit formulas are checked before specializing the scheme
morphisms, keeping the affine identifications explicit.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open scoped ChangeOfRings
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
private lemma affineGammaIso_apply {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec S).Modules) (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj M)) :
    ((affineGammaIso φ).hom.app M) x = x := by
  dsimp [affineGammaIso, moduleSpecΓFunctor, modulesSpecToSheaf]
  rfl
private lemma affineGammaIso_inv_apply {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec S).Modules) (x : (moduleSpecΓFunctor (R := S)).obj M) :
    ((affineGammaIso φ).inv.app M) x = x := by
  have h := ConcreteCategory.congr_hom ((affineGammaIso φ).inv_hom_id_app M) x
  change ((affineGammaIso φ).hom.app M) (((affineGammaIso φ).inv.app M) x) = x at h
  rw [affineGammaIso_apply] at h
  exact h
variable {A B C D : CommRingCat.{u}}
  (φ : A ⟶ B) (ψ : A ⟶ C) (δ : B ⟶ D) (γ : C ⟶ D)
  (h : IsPullback (Spec.map δ) (Spec.map γ) (Spec.map φ) (Spec.map ψ))
  (M : (Spec B).Modules)
set_option backward.isDefEq.respectTransparency false in
/-- The global-sections form of canonical base change, with affine pushforwards
identified with restriction of scalars. -/
def affineBaseChangeGammaMap :
    (ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.restrictScalars φ.hom).obj
      ((moduleSpecΓFunctor (R := B)).obj M)) ⟶
    (ModuleCat.restrictScalars γ.hom).obj ((moduleSpecΓFunctor (R := D)).obj
      ((Scheme.Modules.pullback (Spec.map δ)).obj M)) :=
  (ModuleCat.extendScalars ψ.hom).map ((affineGammaIso φ).inv.app M) ≫
    affinePullbackGammaMap ψ ((Scheme.Modules.pushforward (Spec.map φ)).obj M) ≫
      (moduleSpecΓFunctor (R := C)).map
        (canonicalPushforwardBaseChangeComparison (Spec.map φ) M
          (Spec.map ψ) (Spec.map δ) (Spec.map γ) h) ≫
        (affineGammaIso γ).hom.app ((Scheme.Modules.pullback (Spec.map δ)).obj M)

set_option backward.isDefEq.respectTransparency false in
private lemma affineGamma_unit_abstract
    {A B C D : CommRingCat.{u}}
    (f : Spec B ⟶ Spec A) (b : Spec C ⟶ Spec A)
    (p : Spec D ⟶ Spec B) (g : Spec D ⟶ Spec C)
    (h : IsPullback p g f b) (M : (Spec B).Modules)
    (x : (moduleSpecΓFunctor (R := B)).obj M) :
    ((moduleSpecΓFunctor (R := C)).map
      (canonicalPushforwardBaseChangeComparison f M b p g h))
        (((moduleSpecΓFunctor (R := A)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
            ((Scheme.Modules.pushforward f).obj M))) x) =
      ((moduleSpecΓFunctor (R := B)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M)) x := by
  exact moduleBaseChange_unit_app_top f b p g h M x

set_option backward.isDefEq.respectTransparency false in
private lemma affineBaseChangeGammaMap_unit
    (x : (moduleSpecΓFunctor (R := B)).obj M) :
    ((moduleSpecΓFunctor (R := C)).map
      (canonicalPushforwardBaseChangeComparison (Spec.map φ) M
          (Spec.map ψ) (Spec.map δ) (Spec.map γ) h))
        (((moduleSpecΓFunctor (R := A)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
            ((Scheme.Modules.pushforward (Spec.map φ)).obj M))) x) =
      ((moduleSpecΓFunctor (R := B)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)).unit.app M)) x := by
  exact affineGamma_unit_abstract (Spec.map φ) (Spec.map ψ)
    (Spec.map δ) (Spec.map γ) h M x


/-- A map out of scalar extension is determined by its values on the
adjunction generators, with an arbitrary target after the right-hand
restriction map. -/
private lemma raw_mate_eq_of_one_tmul
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D]
    (N : ModuleCat.{u} B) (P : ModuleCat.{u} D)
    (e : (ModuleCat.extendScalars (algebraMap B D)).obj N ⟶ P)
    (F : (ModuleCat.extendScalars (algebraMap A C)).obj
      ((ModuleCat.restrictScalars (algebraMap A B)).obj N) ⟶
      (ModuleCat.restrictScalars (algebraMap C D)).obj P)
    (hF : ∀ n : N,
      F ((1 : C) ⊗ₜ[A,algebraMap A C] n) =
        ((ModuleCat.restrictScalars (algebraMap C D)).map e)
          ((1 : D) ⊗ₜ[B,algebraMap B D] n)) :
    F = ModuleCat.algebraBaseChangeMate (A := A) (B := B) (C := C) (D := D) N ≫
      (ModuleCat.restrictScalars (algebraMap C D)).map e := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  change F ((1 : C) ⊗ₜ[A,algebraMap A C] (show N from n)) =
    ((ModuleCat.restrictScalars (algebraMap C D)).map e)
      (ModuleCat.algebraBaseChangeMate (A := A) (B := B) (C := C) (D := D) N
        ((1 : C) ⊗ₜ[A,algebraMap A C] (show N from n)))
  rw [ModuleCat.algebraBaseChangeMate_one_tmul]
  exact hF (show N from n)


section

local notation "f" => Spec.map φ
local notation "b" => Spec.map ψ
local notation "p" => Spec.map δ
local notation "g" => Spec.map γ

private theorem iso_middle_of_iso_comp {C : Type u} [Category C]
    {X Y Z W V : C} {α : X ⟶ Y} {β : Y ⟶ Z} {γ : Z ⟶ W} {δ : W ⟶ V}
    [IsIso α] [IsIso β] [IsIso δ]
    (hcomp : IsIso (α ≫ β ≫ γ ≫ δ)) : IsIso γ := by
  have : IsIso (β ≫ γ ≫ δ) := IsIso.of_isIso_comp_left α _
  have : IsIso (γ ≫ δ) := IsIso.of_isIso_comp_left β _
  exact IsIso.of_isIso_comp_right γ δ

private theorem affineBaseChange_isIso_of_gammaMap
    (h : IsPullback p g f b) (M : (Spec B).Modules)
    [M.IsQuasicoherent]
    (hΓcomp : IsIso ((ModuleCat.extendScalars ψ.hom).map
          ((affineGammaIso φ).inv.app M) ≫
        affinePullbackGammaMap ψ
          ((Scheme.Modules.pushforward f).obj M) ≫
        (moduleSpecΓFunctor (R := C)).map
          (canonicalPushforwardBaseChangeComparison f M b p g h) ≫
        (affineGammaIso γ).hom.app
          ((Scheme.Modules.pullback p).obj M))) :
    IsIso (canonicalPushforwardBaseChangeComparison f M b p g h) := by
  have : IsAffineHom f := by infer_instance
  have : IsAffineHom g := by infer_instance
  have : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by infer_instance
  have : ((Scheme.Modules.pullback p).obj M).IsQuasicoherent := by infer_instance
  have hN : IsIso (@Scheme.Modules.fromTildeΓ C
      ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj M))) := by
    have : ((Scheme.Modules.pullback b).obj
        ((Scheme.Modules.pushforward f).obj M)).IsQuasicoherent := by
      infer_instance
    exact Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _
  have hP : IsIso (@Scheme.Modules.fromTildeΓ C
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M))) := by
    have : ((Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pullback p).obj M)).IsQuasicoherent := by
      infer_instance
    exact Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _
  have : IsIso (@Scheme.Modules.fromTildeΓ C
      ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj M))) := hN
  have : IsIso (@Scheme.Modules.fromTildeΓ C
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M))) := hP
  have hΓ : IsIso ((moduleSpecΓFunctor (R := C)).map
      (canonicalPushforwardBaseChangeComparison f M b p g h)) := by
    have hAC : IsIso (affinePullbackGammaMap ψ
        ((Scheme.Modules.pushforward f).obj M)) := by
      apply affinePullbackGammaMap_isIso
    have : IsIso (affinePullbackGammaMap ψ
        ((Scheme.Modules.pushforward f).obj M)) := hAC
    have : IsIso ((ModuleCat.extendScalars ψ.hom).map
      ((affineGammaIso φ).inv.app M) ≫
      affinePullbackGammaMap ψ ((Scheme.Modules.pushforward f).obj M) ≫
      (moduleSpecΓFunctor (R := C)).map
        (canonicalPushforwardBaseChangeComparison f M b p g h) ≫
      (affineGammaIso γ).hom.app ((Scheme.Modules.pullback p).obj M)) := hΓcomp
    exact iso_middle_of_iso_comp hΓcomp
  exact isIso_of_isIso_fromTildeΓ _

end

/-! A pullback of affine schemes gives the corresponding pushout of rings. -/
private lemma isPushout_of_isPullback_SpecMap
    {A B C D : CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : A ⟶ C) (δ : B ⟶ D) (γ : C ⟶ D)
    (h : IsPullback (Scheme.Spec.map (δ.op : Opposite.op D ⟶ Opposite.op B))
      (Scheme.Spec.map (γ.op : Opposite.op D ⟶ Opposite.op C))
      (Scheme.Spec.map (φ.op : Opposite.op B ⟶ Opposite.op A))
      (Scheme.Spec.map (ψ.op : Opposite.op C ⟶ Opposite.op A))) :
    IsPushout φ ψ δ γ := by
  have hh : IsPullback δ.op γ.op φ.op ψ.op :=
    IsPullback.of_map_of_faithful Scheme.Spec h
  exact hh.unop.flip


private theorem isIso_of_equal {C : Type u} [Category C] {X Y : C}
    {f g : X ⟶ Y} [IsIso g] (h : f = g) : IsIso f := by
  rw [h]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma raw_generator_isIso
    {A B C D : CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : A ⟶ C) (δ : B ⟶ D) (γ : C ⟶ D)
    (hp : IsPushout φ ψ δ γ) (N : ModuleCat.{u} B) (P : ModuleCat.{u} D)
    (e : (ModuleCat.extendScalars δ.hom).obj N ⟶ P) [IsIso e]
    (F : (ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.restrictScalars φ.hom).obj N) ⟶
      (ModuleCat.restrictScalars γ.hom).obj P)
    (hgen : ∀ x : N, F ((1 : C) ⊗ₜ[A,ψ.hom] x) = e ((1 : D) ⊗ₜ[B,δ.hom] x)) :
    IsIso F := by
  let : Algebra A B := φ.hom.toAlgebra
  let : Algebra A C := ψ.hom.toAlgebra
  let : Algebra B D := δ.hom.toAlgebra
  let : Algebra C D := γ.hom.toAlgebra
  let : Algebra A D := (φ ≫ δ).hom.toAlgebra
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A C D :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hp.w)
  have : Algebra.IsPushout A B C D := CommRingCat.isPushout_iff_isPushout.mp hp
  exact isIso_of_equal (raw_mate_eq_of_one_tmul (A := A) (B := B) (C := C) (D := D)
    N P e F hgen)

set_option backward.isDefEq.respectTransparency false in
private lemma moduleBaseChange_spec_isIso_of_generators [M.IsQuasicoherent]
    (hgen : ∀ x : (moduleSpecΓFunctor (R := B)).obj M,
      affineBaseChangeGammaMap φ ψ δ γ h M ((1 : C) ⊗ₜ[A,ψ.hom] x) =
        affinePullbackGammaMap δ M ((1 : D) ⊗ₜ[B,δ.hom] x)) :
    IsIso (canonicalPushforwardBaseChangeComparison (Spec.map φ) M
      (Spec.map ψ) (Spec.map δ) (Spec.map γ) h) := by
  have hp : IsPushout φ ψ δ γ := isPushout_of_isPullback_SpecMap φ ψ δ γ h
  have hi : IsIso (affineBaseChangeGammaMap φ ψ δ γ h M) :=
    raw_generator_isIso φ ψ δ γ hp
      ((moduleSpecΓFunctor (R := B)).obj M)
      ((moduleSpecΓFunctor (R := D)).obj ((Scheme.Modules.pullback (Spec.map δ)).obj M))
      (affinePullbackGammaMap δ M) (affineBaseChangeGammaMap φ ψ δ γ h M) hgen
  exact affineBaseChange_isIso_of_gammaMap φ ψ δ γ h M hi


set_option backward.isDefEq.respectTransparency false in
private lemma affineBaseChangeGammaMap_hFmap
    {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ C)
    (M : (Spec B).Modules)
    (x : (moduleSpecΓFunctor (R := B)).obj M) :
    affinePullbackGammaMap ψ ((Scheme.Modules.pushforward (Spec.map φ)).obj M)
        (((ModuleCat.extendScalars ψ.hom).map ((affineGammaIso φ).inv.app M))
          ((1 : C) ⊗ₜ[A,ψ.hom] x)) =
      ((moduleSpecΓFunctor (R := A)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
          ((Scheme.Modules.pushforward (Spec.map φ)).obj M))) x := by
  have hmap :
      ((ModuleCat.extendScalars ψ.hom).map ((affineGammaIso φ).inv.app M))
          ((1 : C) ⊗ₜ[A,ψ.hom] x) =
        (show (ModuleCat.extendScalars ψ.hom).obj
          ((moduleSpecΓFunctor (R := A)).obj
            ((Scheme.Modules.pushforward (Spec.map φ)).obj M)) from
          (1 : C) ⊗ₜ[A] ((affineGammaIso φ).inv.app M x)) := by
    exact ModuleCat.ExtendScalars.map_tmul ψ.hom
      ((affineGammaIso φ).inv.app M) 1 x
  have hunit_inv :
      affinePullbackGammaMap ψ ((Scheme.Modules.pushforward (Spec.map φ)).obj M)
          (show (ModuleCat.extendScalars ψ.hom).obj
            ((moduleSpecΓFunctor (R := A)).obj
              ((Scheme.Modules.pushforward (Spec.map φ)).obj M)) from
            (1 : C) ⊗ₜ[A] ((affineGammaIso φ).inv.app M x)) =
        ((moduleSpecΓFunctor (R := A)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
            ((Scheme.Modules.pushforward (Spec.map φ)).obj M)))
          ((affineGammaIso φ).inv.app M x) := by
    exact affinePullbackGammaMap_one_tmul_unit ψ
      ((Scheme.Modules.pushforward (Spec.map φ)).obj M)
      ((affineGammaIso φ).inv.app M x)
  have hinv : ((affineGammaIso φ).inv.app M) x = x :=
    affineGammaIso_inv_apply φ M x
  have hunit :
      affinePullbackGammaMap ψ ((Scheme.Modules.pushforward (Spec.map φ)).obj M)
          (show (ModuleCat.extendScalars ψ.hom).obj
            ((moduleSpecΓFunctor (R := A)).obj
              ((Scheme.Modules.pushforward (Spec.map φ)).obj M)) from
            (1 : C) ⊗ₜ[A] ((affineGammaIso φ).inv.app M x)) =
        ((moduleSpecΓFunctor (R := A)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
            ((Scheme.Modules.pushforward (Spec.map φ)).obj M))) x := by
    exact hunit_inv.trans
      (congrArg
        (fun z => ((moduleSpecΓFunctor (R := A)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
            ((Scheme.Modules.pushforward (Spec.map φ)).obj M))) z) hinv)
  exact (congrArg
      (fun z => affinePullbackGammaMap ψ
        ((Scheme.Modules.pushforward (Spec.map φ)).obj M) z) hmap).trans hunit

set_option backward.isDefEq.respectTransparency false in
private lemma affineBaseChangeGammaMap_hH
    {B C D : CommRingCat.{u}} (δ : B ⟶ D) (γ : C ⟶ D)
    (M : (Spec B).Modules)
    (x : (moduleSpecΓFunctor (R := B)).obj M) :
    ((affineGammaIso γ).hom.app ((Scheme.Modules.pullback (Spec.map δ)).obj M))
        (((moduleSpecΓFunctor (R := B)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)).unit.app M)) x) =
      affinePullbackGammaMap δ M ((1 : D) ⊗ₜ[B,δ.hom] x) := by
  have hγid :
      ((affineGammaIso γ).hom.app ((Scheme.Modules.pullback (Spec.map δ)).obj M))
          (((moduleSpecΓFunctor (R := B)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)).unit.app M)) x) =
        ((moduleSpecΓFunctor (R := B)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)).unit.app M)) x := by
    exact affineGammaIso_apply γ ((Scheme.Modules.pullback (Spec.map δ)).obj M) _
  have hδ :
      affinePullbackGammaMap δ M ((1 : D) ⊗ₜ[B,δ.hom] x) =
        ((moduleSpecΓFunctor (R := B)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)).unit.app M)) x := by
    exact affinePullbackGammaMap_one_tmul_unit δ M x
  exact hγid.trans hδ.symm


private lemma extended_comp_one_tmul_map
    {A C : Type u} [CommRing A] [CommRing C]
    (ψ : A →+* C)
    {N N' : ModuleCat.{u} A} (i : N ⟶ N')
    {Q R S : ModuleCat.{u} C}
    (F : (ModuleCat.extendScalars ψ).obj N' ⟶ Q)
    (G : Q ⟶ R) (H : R ⟶ S)
    (x : N) (c : Q) (d : R) (e : S)
    (hF : F (((ModuleCat.extendScalars ψ).map i)
      ((1 : C) ⊗ₜ[A,ψ] x)) = c)
    (hG : G c = d) (hH : H d = e) :
    ((ModuleCat.extendScalars ψ).map i ≫ F ≫ G ≫ H)
        ((1 : C) ⊗ₜ[A,ψ] x) = e := by
  change H (G (F (((ModuleCat.extendScalars ψ).map i)
    ((1 : C) ⊗ₜ[A,ψ] x)))) = e
  rw [hF, hG, hH]

set_option backward.isDefEq.respectTransparency false in
private def affineGammaComposite
    (τ : (Scheme.Modules.pullback (Spec.map ψ)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj M) ⟶
      (Scheme.Modules.pushforward (Spec.map γ)).obj
        ((Scheme.Modules.pullback (Spec.map δ)).obj M)) :
    (ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.restrictScalars φ.hom).obj
      ((moduleSpecΓFunctor (R := B)).obj M)) ⟶
    (ModuleCat.restrictScalars γ.hom).obj ((moduleSpecΓFunctor (R := D)).obj
      ((Scheme.Modules.pullback (Spec.map δ)).obj M)) :=
  (ModuleCat.extendScalars ψ.hom).map ((affineGammaIso φ).inv.app M) ≫
    affinePullbackGammaMap ψ ((Scheme.Modules.pushforward (Spec.map φ)).obj M) ≫
      (moduleSpecΓFunctor (R := C)).map τ ≫
        (affineGammaIso γ).hom.app ((Scheme.Modules.pullback (Spec.map δ)).obj M)

private lemma final_generic
    (τ : (Scheme.Modules.pullback (Spec.map ψ)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj M) ⟶
      (Scheme.Modules.pushforward (Spec.map γ)).obj
        ((Scheme.Modules.pullback (Spec.map δ)).obj M))
    (x : (moduleSpecΓFunctor (R := B)).obj M)
    (hFmap : affinePullbackGammaMap ψ ((Scheme.Modules.pushforward (Spec.map φ)).obj M)
      (((ModuleCat.extendScalars ψ.hom).map ((affineGammaIso φ).inv.app M))
        ((1 : C) ⊗ₜ[A,ψ.hom] x)) =
      ((moduleSpecΓFunctor (R := A)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
          ((Scheme.Modules.pushforward (Spec.map φ)).obj M))) x)
    (hunit : ((moduleSpecΓFunctor (R := C)).map
      τ)
        (((moduleSpecΓFunctor (R := A)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
            ((Scheme.Modules.pushforward (Spec.map φ)).obj M))) x) =
      ((moduleSpecΓFunctor (R := B)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)).unit.app M)) x)
    (hH : ((affineGammaIso γ).hom.app ((Scheme.Modules.pullback (Spec.map δ)).obj M))
          (((moduleSpecΓFunctor (R := B)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)).unit.app M)) x) =
        affinePullbackGammaMap δ M ((1 : D) ⊗ₜ[B,δ.hom] x)) :
    affineGammaComposite φ ψ δ γ M τ ((1 : C) ⊗ₜ[A,ψ.hom] x) =
      affinePullbackGammaMap δ M ((1 : D) ⊗ₜ[B,δ.hom] x) := by
  exact extended_comp_one_tmul_map
    (A := A) (C := C)
    (N := (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := B)).obj M))
    (N' := (moduleSpecΓFunctor (R := A)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj M))
    (Q := (moduleSpecΓFunctor (R := C)).obj
      ((Scheme.Modules.pullback (Spec.map ψ)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj M)))
    (R := (moduleSpecΓFunctor (R := C)).obj
      ((Scheme.Modules.pushforward (Spec.map γ)).obj
        ((Scheme.Modules.pullback (Spec.map δ)).obj M)))
    (S := (ModuleCat.restrictScalars γ.hom).obj ((moduleSpecΓFunctor (R := D)).obj
      ((Scheme.Modules.pullback (Spec.map δ)).obj M)))
    (ψ := ψ.hom)
    (i := (affineGammaIso φ).inv.app M)
    (F := affinePullbackGammaMap ψ ((Scheme.Modules.pushforward (Spec.map φ)).obj M))
    (G := (moduleSpecΓFunctor (R := C)).map
      τ)
    (H := (affineGammaIso γ).hom.app ((Scheme.Modules.pullback (Spec.map δ)).obj M))
    (x := (show (ModuleCat.restrictScalars φ.hom).obj
      ((moduleSpecΓFunctor (R := B)).obj M) from x))
    (c := ((moduleSpecΓFunctor (R := A)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
        ((Scheme.Modules.pushforward (Spec.map φ)).obj M))) x)
    (d := ((moduleSpecΓFunctor (R := B)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)).unit.app M)) x)
    (e := affinePullbackGammaMap δ M ((1 : D) ⊗ₜ[B,δ.hom] x))
    (hF := hFmap) (hG := hunit) (hH := hH)

private lemma affineBaseChangeGammaMap_one_tmul_of_endpoints
    (x : (moduleSpecΓFunctor (R := B)).obj M)
    (hFmap : affinePullbackGammaMap ψ ((Scheme.Modules.pushforward (Spec.map φ)).obj M)
      (((ModuleCat.extendScalars ψ.hom).map ((affineGammaIso φ).inv.app M))
        ((1 : C) ⊗ₜ[A,ψ.hom] x)) =
      ((moduleSpecΓFunctor (R := A)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
          ((Scheme.Modules.pushforward (Spec.map φ)).obj M))) x)
    (hunit : ((moduleSpecΓFunctor (R := C)).map
      ((canonicalPushforwardBaseChangeComparison (Spec.map φ) M (Spec.map ψ)
          (Spec.map δ) (Spec.map γ) h)))
        (((moduleSpecΓFunctor (R := A)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
            ((Scheme.Modules.pushforward (Spec.map φ)).obj M))) x) =
      ((moduleSpecΓFunctor (R := B)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)).unit.app M)) x)
    (hH : ((affineGammaIso γ).hom.app ((Scheme.Modules.pullback (Spec.map δ)).obj M))
          (((moduleSpecΓFunctor (R := B)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map δ)).unit.app M)) x) =
        affinePullbackGammaMap δ M ((1 : D) ⊗ₜ[B,δ.hom] x)) :
    affineBaseChangeGammaMap φ ψ δ γ h M ((1 : C) ⊗ₜ[A,ψ.hom] x) =
      affinePullbackGammaMap δ M ((1 : D) ⊗ₜ[B,δ.hom] x) := by
  exact final_generic φ ψ δ γ M
    (canonicalPushforwardBaseChangeComparison (Spec.map φ) M (Spec.map ψ)
      (Spec.map δ) (Spec.map γ) h) x hFmap hunit hH


/-- On tensor generators, the canonical geometric comparison agrees with scalar base change. -/
lemma affineBaseChangeGammaMap_one_tmul
    (x : (moduleSpecΓFunctor (R := B)).obj M) :
    affineBaseChangeGammaMap φ ψ δ γ h M ((1 : C) ⊗ₜ[A,ψ.hom] x) =
      affinePullbackGammaMap δ M ((1 : D) ⊗ₜ[B,δ.hom] x) := by
  exact affineBaseChangeGammaMap_one_tmul_of_endpoints φ ψ δ γ h M x
    (affineBaseChangeGammaMap_hFmap φ ψ M x)
    (affineBaseChangeGammaMap_unit φ ψ δ γ h M x)
    (affineBaseChangeGammaMap_hH δ γ M x)

/-- Canonical base change for a quasi-coherent module in any pullback square of spectra. -/
theorem canonicalPushforwardBaseChangeComparison_spec_isIso [M.IsQuasicoherent] :
    IsIso (canonicalPushforwardBaseChangeComparison (Spec.map φ) M
      (Spec.map ψ) (Spec.map δ) (Spec.map γ) h) := by
  exact moduleBaseChange_spec_isIso_of_generators φ ψ δ γ h M
    (affineBaseChangeGammaMap_one_tmul φ ψ δ γ h M)

end
end GromovWitten.AlgebraicGeometry.Curves
