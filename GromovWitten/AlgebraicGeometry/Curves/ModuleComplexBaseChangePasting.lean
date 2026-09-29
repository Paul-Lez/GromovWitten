/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.ComplexBaseChangeHomotopy
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangePasting

/-!
# Pasting ordinary module base change on cochain complexes

The ordinary module base-change pasting law lifts degreewise to the generic
complex base-change map.  This is a chain-level identity and uses no
exactness, flasqueness, Noetherianity, or quasicoherence assumptions.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open _root_.AlgebraicGeometry
open CategoryTheory.NatTrans
open Scheme.Modules
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S T Y V W : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The generic cochain-complex base-change map is compatible with pasting two
Cartesian module squares.  The total coefficient map uses the canonical
pullback-composition comparison for `q ≫ p`. -/
lemma moduleComplexBaseChange_pasting
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Y) (k : W ⟶ V)
    (h₁ : IsPullback p g s b) (h₂ : IsPullback q k g c)
    {K : CochainComplex X.Modules ℕ}
    {J : CochainComplex Y.Modules ℕ}
    {N : CochainComplex W.Modules ℕ}
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (ψ : ((Scheme.Modules.pullback q).mapHomologicalComplex (.up ℕ)).obj J ⟶ N) :
    (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp c b) (.up ℕ)).hom.app
        (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℕ)).obj K) ≫
      complexBaseChangeMap (Scheme.Modules.pushforward s)
        (Scheme.Modules.pullback (c ≫ b)) (Scheme.Modules.pullback (q ≫ p))
        (Scheme.Modules.pushforward k)
        (modulePushforwardBaseChangeNatTrans s (c ≫ b) (q ≫ p) k
          (h₂.paste_horiz h₁))
        ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp q p) (.up ℕ)).inv.app K ≫
          ((Scheme.Modules.pullback q).mapHomologicalComplex (.up ℕ)).map φ ≫ ψ) =
      ((Scheme.Modules.pullback c).mapHomologicalComplex (.up ℕ)).map
          (complexBaseChangeMap (Scheme.Modules.pushforward s)
            (Scheme.Modules.pullback b) (Scheme.Modules.pullback p)
            (Scheme.Modules.pushforward g)
            (modulePushforwardBaseChangeNatTrans s b p g h₁) φ) ≫
        complexBaseChangeMap (Scheme.Modules.pushforward g)
          (Scheme.Modules.pullback c) (Scheme.Modules.pullback q)
          (Scheme.Modules.pushforward k)
          (modulePushforwardBaseChangeNatTrans g c q k h₂) ψ := by
  let F₁ := Scheme.Modules.pullback b
  let L₁ := Scheme.Modules.pullback p
  let P₁ := Scheme.Modules.pushforward g
  let F₂ := Scheme.Modules.pullback c
  let L₂ := Scheme.Modules.pullback q
  let P₂ := Scheme.Modules.pushforward k
  let F₀ := Scheme.Modules.pullback (c ≫ b)
  let L₀ := Scheme.Modules.pullback (q ≫ p)
  let P₀ := Scheme.Modules.pushforward k
  let α₁ := modulePushforwardBaseChangeNatTrans s b p g h₁
  let α₂ := modulePushforwardBaseChangeNatTrans g c q k h₂
  let α₀ := modulePushforwardBaseChangeNatTrans s (c ≫ b) (q ≫ p) k
    (h₂.paste_horiz h₁)
  let φtot : (L₀.mapHomologicalComplex (.up ℕ)).obj K ⟶ N :=
    (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp q p) (.up ℕ)).inv.app K ≫
      (L₂.mapHomologicalComplex (.up ℕ)).map φ ≫ ψ
  apply HomologicalComplex.Hom.ext
  funext n
  let φn : (Scheme.Modules.pullback p).obj (K.X n) ⟶ J.X n := φ.f n
  let ψn : (Scheme.Modules.pullback q).obj (J.X n) ⟶ N.X n := ψ.f n
  change
    (Scheme.Modules.pullbackComp c b).hom.app ((Scheme.Modules.pushforward s).obj (K.X n)) ≫
        α₀.app (K.X n) ≫
      (Scheme.Modules.pushforward k).map
        ((Scheme.Modules.pullbackComp q p).inv.app (K.X n) ≫
          (Scheme.Modules.pullback q).map φn ≫ ψn) =
      (Scheme.Modules.pullback c).map
          (α₁.app (K.X n) ≫ (Scheme.Modules.pushforward g).map φn) ≫
        α₂.app (J.X n) ≫ (Scheme.Modules.pushforward k).map ψn
  have hpq :
      (Scheme.Modules.pullbackComp q p).hom.app (K.X n) ≫
          (Scheme.Modules.pullbackComp q p).inv.app (K.X n) ≫
          (Scheme.Modules.pullback q).map φn ≫ ψn =
        (Scheme.Modules.pullback q).map φn ≫ ψn := by
    rw [← Category.assoc]
    rw [(Scheme.Modules.pullbackComp q p).hom_inv_id_app]
    simp
  have hcancel :
      (Scheme.Modules.pushforward k).map
          ((Scheme.Modules.pullbackComp q p).hom.app (K.X n)) ≫
        (Scheme.Modules.pushforward k).map
          ((Scheme.Modules.pullbackComp q p).inv.app (K.X n)) =
      𝟙 _ := by
    rw [← Functor.map_comp, (Scheme.Modules.pullbackComp q p).hom_inv_id_app]
    simp
  have hcancel_assoc :
      (Scheme.Modules.pushforward k).map
          ((Scheme.Modules.pullbackComp q p).hom.app (K.X n)) ≫
        (Scheme.Modules.pushforward k).map
          ((Scheme.Modules.pullbackComp q p).inv.app (K.X n)) ≫
        (Scheme.Modules.pushforward k).map ((Scheme.Modules.pullback q).map φn) ≫
        (Scheme.Modules.pushforward k).map ψn =
      (Scheme.Modules.pushforward k).map ((Scheme.Modules.pullback q).map φn) ≫
        (Scheme.Modules.pushforward k).map ψn := by
    rw [← Category.assoc, hcancel, Category.id_comp]
  calc
    _ = (Scheme.Modules.pullback c).map (α₁.app (K.X n)) ≫
          α₂.app ((Scheme.Modules.pullback p).obj (K.X n)) ≫
        (Scheme.Modules.pushforward k).map
          ((Scheme.Modules.pullbackComp q p).hom.app (K.X n)) ≫
        (Scheme.Modules.pushforward k).map
          ((Scheme.Modules.pullbackComp q p).inv.app (K.X n)) ≫
        (Scheme.Modules.pushforward k).map ((Scheme.Modules.pullback q).map φn) ≫
        (Scheme.Modules.pushforward k).map ψn := by
      rw [← Category.assoc,
        moduleBaseChange_pasting s b p g c q k h₁ h₂ (K.X n)]
      simp only [α₁, α₂, ← Functor.map_comp, Category.assoc, hpq]
    _ = (Scheme.Modules.pullback c).map (α₁.app (K.X n)) ≫
          (Scheme.Modules.pullback c).map ((Scheme.Modules.pushforward g).map (φ.f n)) ≫
        α₂.app (J.X n) ≫ (Scheme.Modules.pushforward k).map (ψ.f n) := by
      rw [hcancel_assoc]
      have hnat := α₂.naturality φn
      change
        (Scheme.Modules.pullback c).map ((Scheme.Modules.pushforward g).map φn) ≫
            α₂.app (J.X n) =
          α₂.app ((Scheme.Modules.pullback p).obj (K.X n)) ≫
            (Scheme.Modules.pushforward k).map
              ((Scheme.Modules.pullback q).map φn) at hnat
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg
          (fun t => (Scheme.Modules.pullback c).map (α₁.app (K.X n)) ≫
            t ≫ (Scheme.Modules.pushforward k).map ψn) hnat.symm
    _ = (Scheme.Modules.pullback c).map
          (α₁.app (K.X n) ≫ (Scheme.Modules.pushforward g).map φn) ≫
        α₂.app (J.X n) ≫ (Scheme.Modules.pushforward k).map ψn := by
      simp only [φn, ψn, Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The pasted outer complex base-change map is a quasi-isomorphism when the
two inner maps are quasi-isomorphisms and pullback along `c` preserves
homology. -/
lemma moduleComplexBaseChange_pasting_quasiIso_outer
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Y) (k : W ⟶ V)
    (h₁ : IsPullback p g s b) (h₂ : IsPullback q k g c)
    {K : CochainComplex X.Modules ℕ}
    {J : CochainComplex Y.Modules ℕ}
    {N : CochainComplex W.Modules ℕ}
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (ψ : ((Scheme.Modules.pullback q).mapHomologicalComplex (.up ℕ)).obj J ⟶ N)
    [(Scheme.Modules.pullback c).PreservesHomology]
    [QuasiIso (complexBaseChangeMap (Scheme.Modules.pushforward s)
      (Scheme.Modules.pullback b) (Scheme.Modules.pullback p)
      (Scheme.Modules.pushforward g)
      (modulePushforwardBaseChangeNatTrans s b p g h₁) φ)]
    [QuasiIso (complexBaseChangeMap (Scheme.Modules.pushforward g)
      (Scheme.Modules.pullback c) (Scheme.Modules.pullback q)
      (Scheme.Modules.pushforward k)
      (modulePushforwardBaseChangeNatTrans g c q k h₂) ψ)] :
    let φtot :=
      (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp q p) (.up ℕ)).inv.app K ≫
        ((Scheme.Modules.pullback q).mapHomologicalComplex (.up ℕ)).map φ ≫ ψ
    QuasiIso (complexBaseChangeMap (Scheme.Modules.pushforward s)
      (Scheme.Modules.pullback (c ≫ b)) (Scheme.Modules.pullback (q ≫ p))
      (Scheme.Modules.pushforward k)
      (modulePushforwardBaseChangeNatTrans s (c ≫ b) (q ≫ p) k
        (h₂.paste_horiz h₁)) φtot) := by
  dsimp only
  let C :=
    (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp c b) (.up ℕ)).hom.app
      (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℕ)).obj K)
  let β₀ := complexBaseChangeMap (Scheme.Modules.pushforward s)
    (Scheme.Modules.pullback (c ≫ b)) (Scheme.Modules.pullback (q ≫ p))
    (Scheme.Modules.pushforward k)
    (modulePushforwardBaseChangeNatTrans s (c ≫ b) (q ≫ p) k
      (h₂.paste_horiz h₁))
    ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp q p) (.up ℕ)).inv.app K ≫
      ((Scheme.Modules.pullback q).mapHomologicalComplex (.up ℕ)).map φ ≫ ψ)
  let β₁ := complexBaseChangeMap (Scheme.Modules.pushforward s)
    (Scheme.Modules.pullback b) (Scheme.Modules.pullback p)
    (Scheme.Modules.pushforward g)
    (modulePushforwardBaseChangeNatTrans s b p g h₁) φ
  let β₂ := complexBaseChangeMap (Scheme.Modules.pushforward g)
    (Scheme.Modules.pullback c) (Scheme.Modules.pullback q)
    (Scheme.Modules.pushforward k)
    (modulePushforwardBaseChangeNatTrans g c q k h₂) ψ
  have : QuasiIso C := by
    dsimp [C]
    infer_instance
  have : QuasiIso β₁ := by
    dsimp [β₁]
    infer_instance
  have : QuasiIso β₂ := by
    dsimp [β₂]
    infer_instance
  have hcomp : QuasiIso (C ≫ β₀) := by
    dsimp [C, β₀]
    rw [moduleComplexBaseChange_pasting s b p g c q k h₁ h₂ φ ψ]
    infer_instance
  exact quasiIso_of_comp_left C β₀

set_option backward.isDefEq.respectTransparency false in
/-- If the pasted outer map and the second inner map are
quasi-isomorphisms, then the pulled-back first inner map is a
quasi-isomorphism. -/
lemma moduleComplexBaseChange_pasting_quasiIso_inner
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Y) (k : W ⟶ V)
    (h₁ : IsPullback p g s b) (h₂ : IsPullback q k g c)
    {K : CochainComplex X.Modules ℕ}
    {J : CochainComplex Y.Modules ℕ}
    {N : CochainComplex W.Modules ℕ}
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (ψ : ((Scheme.Modules.pullback q).mapHomologicalComplex (.up ℕ)).obj J ⟶ N)
    [QuasiIso (complexBaseChangeMap (Scheme.Modules.pushforward s)
      (Scheme.Modules.pullback (c ≫ b)) (Scheme.Modules.pullback (q ≫ p))
      (Scheme.Modules.pushforward k)
      (modulePushforwardBaseChangeNatTrans s (c ≫ b) (q ≫ p) k
        (h₂.paste_horiz h₁))
      ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp q p) (.up ℕ)).inv.app K ≫
        ((Scheme.Modules.pullback q).mapHomologicalComplex (.up ℕ)).map φ ≫ ψ))]
    [QuasiIso (complexBaseChangeMap (Scheme.Modules.pushforward g)
      (Scheme.Modules.pullback c) (Scheme.Modules.pullback q)
      (Scheme.Modules.pushforward k)
      (modulePushforwardBaseChangeNatTrans g c q k h₂) ψ)] :
    QuasiIso (((Scheme.Modules.pullback c).mapHomologicalComplex (.up ℕ)).map
      (complexBaseChangeMap (Scheme.Modules.pushforward s)
        (Scheme.Modules.pullback b) (Scheme.Modules.pullback p)
        (Scheme.Modules.pushforward g)
        (modulePushforwardBaseChangeNatTrans s b p g h₁) φ)) := by
  let C :=
    (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp c b) (.up ℕ)).hom.app
      (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℕ)).obj K)
  let β₀ := complexBaseChangeMap (Scheme.Modules.pushforward s)
    (Scheme.Modules.pullback (c ≫ b)) (Scheme.Modules.pullback (q ≫ p))
    (Scheme.Modules.pushforward k)
    (modulePushforwardBaseChangeNatTrans s (c ≫ b) (q ≫ p) k
      (h₂.paste_horiz h₁))
    ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp q p) (.up ℕ)).inv.app K ≫
      ((Scheme.Modules.pullback q).mapHomologicalComplex (.up ℕ)).map φ ≫ ψ)
  let β₁ := complexBaseChangeMap (Scheme.Modules.pushforward s)
    (Scheme.Modules.pullback b) (Scheme.Modules.pullback p)
    (Scheme.Modules.pushforward g)
    (modulePushforwardBaseChangeNatTrans s b p g h₁) φ
  let β₂ := complexBaseChangeMap (Scheme.Modules.pushforward g)
    (Scheme.Modules.pullback c) (Scheme.Modules.pullback q)
    (Scheme.Modules.pushforward k)
    (modulePushforwardBaseChangeNatTrans g c q k h₂) ψ
  let F₂ := (Scheme.Modules.pullback c).mapHomologicalComplex (.up ℕ)
  have : QuasiIso C := by
    dsimp [C]
    infer_instance
  have : QuasiIso β₀ := by
    dsimp [β₀]
    infer_instance
  have : QuasiIso β₂ := by
    dsimp [β₂]
    infer_instance
  have hcomp : QuasiIso (F₂.map β₁ ≫ β₂) := by
    dsimp [F₂, β₁, β₂]
    rw [← moduleComplexBaseChange_pasting s b p g c q k h₁ h₂ φ ψ]
    infer_instance
  exact quasiIso_of_comp_right (F₂.map β₁) β₂

end GromovWitten.AlgebraicGeometry.Curves
