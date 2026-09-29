/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineBaseChangeReduction
import GromovWitten.AlgebraicGeometry.Curves.AffineBaseChangeCompatibility

/-!
# Canonical base change for affine morphisms

For an affine morphism and a quasi-coherent module, the canonical comparison is
invertible after arbitrary base change. The affine calculation is transported
through affine isomorphisms and checked on compatible affine neighborhoods.
-/

open CategoryTheory Limits TopologicalSpace
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

private lemma isIso_modulePushforwardBaseChangeNatTrans_of_isIso_canonical
    {X S T Z : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X)
    (g : Z ⟶ T) (h : IsPullback p g f b) (M : X.Modules)
    (hcanonical : IsIso (canonicalPushforwardBaseChangeComparison f M b p g h)) :
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  rw [modulePushforwardBaseChangeNatTrans_app_eq_canonical]
  exact hcanonical

/-! Specialize the raw Spec theorem before exposing any concrete scheme terms. -/
private lemma specBaseChange_callback
    (hSpec : ∀ {A B C D : CommRingCat.{u}}
      (φ : A ⟶ B) (ψ : A ⟶ C) (δ : B ⟶ D) (γ : C ⟶ D)
      (h : IsPullback (Scheme.Spec.map (δ.op : Opposite.op D ⟶ Opposite.op B))
        (Scheme.Spec.map (γ.op : Opposite.op D ⟶ Opposite.op C))
        (Scheme.Spec.map (φ.op : Opposite.op B ⟶ Opposite.op A))
        (Scheme.Spec.map (ψ.op : Opposite.op C ⟶ Opposite.op A)))
      (N : (Spec B).Modules) [N.IsQuasicoherent],
      IsIso (canonicalPushforwardBaseChangeComparison
        (Scheme.Spec.map φ.op) N (Scheme.Spec.map ψ.op)
        (Scheme.Spec.map δ.op) (Scheme.Spec.map γ.op) h))
    {A B C D : CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : A ⟶ C) (δ : B ⟶ D) (γ : C ⟶ D) :
    ∀ (h : IsPullback (Scheme.Spec.map (δ.op : Opposite.op D ⟶ Opposite.op B))
      (Scheme.Spec.map (γ.op : Opposite.op D ⟶ Opposite.op C))
      (Scheme.Spec.map (φ.op : Opposite.op B ⟶ Opposite.op A))
      (Scheme.Spec.map (ψ.op : Opposite.op C ⟶ Opposite.op A)))
      (N : (Spec B).Modules), N.IsQuasicoherent →
      IsIso (canonicalPushforwardBaseChangeComparison
        (Scheme.Spec.map φ.op) N (Scheme.Spec.map ψ.op)
        (Scheme.Spec.map δ.op) (Scheme.Spec.map γ.op) h) := by
  intro h N hN
  have : N.IsQuasicoherent := hN
  exact hSpec (A := A) (B := B) (C := C) (D := D) φ ψ δ γ h N

/-! One affine square follows from the specialized Spec callback. -/
set_option backward.isDefEq.respectTransparency false in
private lemma moduleBaseChange_isIso_of_one_affine_square_of_spec
    (hSpec : ∀ {A B C D : CommRingCat.{u}}
      (φ : A ⟶ B) (ψ : A ⟶ C) (δ : B ⟶ D) (γ : C ⟶ D)
      (h : IsPullback (Scheme.Spec.map (δ.op : Opposite.op D ⟶ Opposite.op B))
        (Scheme.Spec.map (γ.op : Opposite.op D ⟶ Opposite.op C))
        (Scheme.Spec.map (φ.op : Opposite.op B ⟶ Opposite.op A))
        (Scheme.Spec.map (ψ.op : Opposite.op C ⟶ Opposite.op A)))
      (N : (Spec B).Modules) [N.IsQuasicoherent],
      IsIso (canonicalPushforwardBaseChangeComparison
        (Scheme.Spec.map φ.op) N (Scheme.Spec.map ψ.op)
        (Scheme.Spec.map δ.op) (Scheme.Spec.map γ.op) h))
    {X S T Z : Scheme.{u}} [IsAffine X] [IsAffine S] [IsAffine T] [IsAffine Z]
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  let hcan := specBaseChange_callback hSpec f.appTop b.appTop p.appTop g.appTop
  let hnat := fun (h' : IsPullback (Spec.map p.appTop) (Spec.map g.appTop)
      (Spec.map f.appTop) (Spec.map b.appTop))
      (N : (Spec (X.presheaf.obj (.op ⊤))).Modules)
      (hN : N.IsQuasicoherent) => by
    have : N.IsQuasicoherent := hN
    exact isIso_modulePushforwardBaseChangeNatTrans_of_isIso_canonical
      (Spec.map f.appTop) (Spec.map b.appTop) (Spec.map p.appTop)
      (Spec.map g.appTop) h' N (hcan h' N hN)
  exact moduleBaseChange_isIso_of_isoSpec f b p g h hnat M

/-! The one-square result supplies the all-affine callback. -/
private lemma moduleBaseChange_isIso_of_affine_squares_of_spec
    (hSpec : ∀ {A B C D : CommRingCat.{u}}
      (φ : A ⟶ B) (ψ : A ⟶ C) (δ : B ⟶ D) (γ : C ⟶ D)
      (h : IsPullback (Scheme.Spec.map (δ.op : Opposite.op D ⟶ Opposite.op B))
        (Scheme.Spec.map (γ.op : Opposite.op D ⟶ Opposite.op C))
        (Scheme.Spec.map (φ.op : Opposite.op B ⟶ Opposite.op A))
        (Scheme.Spec.map (ψ.op : Opposite.op C ⟶ Opposite.op A)))
      (N : (Spec B).Modules) [N.IsQuasicoherent],
      IsIso (canonicalPushforwardBaseChangeComparison
        (Scheme.Spec.map φ.op) N (Scheme.Spec.map ψ.op)
        (Scheme.Spec.map δ.op) (Scheme.Spec.map γ.op) h)) :
    ∀ (X S T Z : Scheme.{u}) [IsAffine X] [IsAffine S] [IsAffine T]
      [IsAffine Z] (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
      (h : IsPullback p g f b) (M : X.Modules) [M.IsQuasicoherent],
      IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  intro X S T Z _ _ _ _ f b p g h M
  exact moduleBaseChange_isIso_of_one_affine_square_of_spec hSpec f b p g h M

/-! The all-affine result feeds the established affine-morphism reduction. -/
set_option backward.isDefEq.respectTransparency false in
private lemma moduleBaseChange_isIso_of_affine_hom_of_spec
    (hSpec : ∀ {A B C D : CommRingCat.{u}}
      (φ : A ⟶ B) (ψ : A ⟶ C) (δ : B ⟶ D) (γ : C ⟶ D)
      (h : IsPullback (Scheme.Spec.map (δ.op : Opposite.op D ⟶ Opposite.op B))
        (Scheme.Spec.map (γ.op : Opposite.op D ⟶ Opposite.op C))
        (Scheme.Spec.map (φ.op : Opposite.op B ⟶ Opposite.op A))
        (Scheme.Spec.map (ψ.op : Opposite.op C ⟶ Opposite.op A)))
      (N : (Spec B).Modules) [N.IsQuasicoherent],
      IsIso (canonicalPushforwardBaseChangeComparison
        (Scheme.Spec.map φ.op) N (Scheme.Spec.map ψ.op)
        (Scheme.Spec.map δ.op) (Scheme.Spec.map γ.op) h))
    {X S T Z : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [IsAffineHom f] (M : X.Modules)
    [M.IsQuasicoherent] :
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  exact moduleBaseChange_isIso_of_affine_squares
    (hAffine := moduleBaseChange_isIso_of_affine_squares_of_spec hSpec)
    f b p g h M


/-- The ordinary module-valued comparison is invertible for an affine morphism
and a quasi-coherent module, after arbitrary base change. -/
theorem moduleBaseChange_isIso_of_isAffineHom
    {X S T Z : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X)
    (g : Z ⟶ T) (h : IsPullback p g f b) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  exact moduleBaseChange_isIso_of_affine_hom_of_spec
    (@canonicalPushforwardBaseChangeComparison_spec_isIso.{u}) f b p g h M

/-- Canonical quasi-coherent base change for an affine morphism. -/
theorem canonicalPushforwardBaseChangeComparison_isIso_of_isAffineHom
    {X S T Z : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X)
    (g : Z ⟶ T) (h : IsPullback p g f b) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (canonicalPushforwardBaseChangeComparison f M b p g h) := by
  have hnat := moduleBaseChange_isIso_of_isAffineHom f b p g h M
  rw [modulePushforwardBaseChangeNatTrans_app_eq_canonical] at hnat
  exact hnat

end
end GromovWitten.AlgebraicGeometry.Curves
