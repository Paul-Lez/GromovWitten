/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.TwoPullback

/-!
# The bicategorical universal property of stack two-pullbacks

This file equips the canonical fibrewise categorical pullback from `TwoPullback` with its
full stack-level bilimit property. The lift, its comparison cells, uniqueness isomorphism,
and the reconstruction of modifications from compatible projected pairs are all constructed
from the underlying categorical-pullback data.
-/

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackTwoPullback

variable {X Y Z T : FppfStack.{u}} (f : StackHom X Z) (g : StackHom Y Z)

def stackIso2AppIsoAt {A B : FppfStack.{u}} {p q : StackHom A B}
    (e : StackIso2 p q) (a : LocallyDiscrete Schemeᵒᵖ) :
    (p.app a).toFunctor ≅ (q.app a).toFunctor where
  hom := (e.hom.app a).toNatTrans
  inv := (e.inv.app a).toNatTrans
  hom_inv_id := by
    ext x
    have h := congrArg (fun m => ((m.app a).toNatTrans).app x) e.hom_inv_id
    simpa [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id] using h
  inv_hom_id := by
    ext x
    have h := congrArg (fun m => ((m.app a).toNatTrans).app x) e.inv_hom_id
    simpa [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id] using h

set_option backward.isDefEq.respectTransparency false in
def canonicalLiftComparisonIso
    (c : Cone (f := f) (g := g) T) (a : LocallyDiscrete Schemeᵒᵖ)
    (x : T.toPseudofunctor.obj a) :
    (f.app a).toFunctor.obj ((c.fst.app a).toFunctor.obj x) ≅
      (g.app a).toFunctor.obj ((c.snd.app a).toFunctor.obj x) where
  hom := (c.comparison.hom.app a).toNatTrans.app x
  inv := (c.comparison.inv.app a).toNatTrans.app x
  hom_inv_id := by
    change (c.comparison.hom.app a).toNatTrans.app x ≫
        (c.comparison.inv.app a).toNatTrans.app x =
      𝟙 (((Pseudofunctor.StrongTrans.vcomp c.fst f).app a).toFunctor.obj x)
    have h := congrArg (fun m => ((m.app a).toNatTrans).app x)
      c.comparison.hom_inv_id
    simpa [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id] using h
  inv_hom_id := by
    change (c.comparison.inv.app a).toNatTrans.app x ≫
        (c.comparison.hom.app a).toNatTrans.app x =
      𝟙 (((Pseudofunctor.StrongTrans.vcomp c.snd g).app a).toFunctor.obj x)
    have h := congrArg (fun m => ((m.app a).toNatTrans).app x)
      c.comparison.inv_hom_id
    simpa [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id] using h

set_option backward.isDefEq.respectTransparency false in
noncomputable def canonicalLiftApp
    (c : Cone (f := f) (g := g) T) (a : LocallyDiscrete Schemeᵒᵖ) :
    T.toPseudofunctor.obj a ⥤
      TwoPullback (f.app a).toFunctor (g.app a).toFunctor where
  obj x :=
    { fst := (c.fst.app a).toFunctor.obj x
      snd := (c.snd.app a).toFunctor.obj x
      iso := canonicalLiftComparisonIso f g c a x }
  map {x y} k :=
    { fst := (c.fst.app a).toFunctor.map k
      snd := (c.snd.app a).toFunctor.map k
      w := by
        exact (c.comparison.hom.app a).toNatTrans.naturality k }
  map_id x := by
    apply CategoricalPullback.hom_ext <;> simp
  map_comp k l := by
    apply CategoricalPullback.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
noncomputable def canonicalLiftNaturality
    (c : Cone (f := f) (g := g) T)
    {a b : LocallyDiscrete Schemeᵒᵖ} (h : a ⟶ b) :
    (T.toPseudofunctor.map h).toFunctor ⋙
        canonicalLiftApp f g c b ≅
      canonicalLiftApp f g c a ⋙
        StackInGroupoids.fiberTwoPullbackMap f g h :=
  NatIso.ofComponents
    (fun x ↦ CategoricalPullback.mkIso
      ((Cat.Hom.toNatIso (c.fst.naturality h)).app x)
      ((Cat.Hom.toNatIso (c.snd.naturality h)).app x)
      (by
        dsimp [canonicalLiftApp, StackInGroupoids.fiberTwoPullbackMap]
        have hc := congrArg (fun q => q.toNatTrans.app x)
          (c.comparison.hom.naturality h)
        dsimp [Pseudofunctor.StrongTrans.vcomp,
          Pseudofunctor.StrongTrans.mkOfOplax,
          Pseudofunctor.StrongTrans.toOplax,
          Pseudofunctor.toOplax,
          CategoryTheory.Oplax.StrongTrans.vcomp,
          CategoryTheory.Oplax.StrongTrans.toOplax,
          CategoryTheory.Oplax.StrongTrans.mkOfOplax,
          CategoryTheory.Oplax.OplaxTrans.vcomp] at hc
        simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
          whiskerLeftIso_hom,
          Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
          Cat.whiskerRight_toNatTrans, NatTrans.comp_app,
          Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans,
          Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Functor.associator_hom_app, Functor.associator_inv_app,
          Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
          Cat.associator_hom_app, Cat.associator_inv_app,
          Cat.comp_eq_comp] at hc
        simp only [Category.id_comp] at hc
        rw [← cancel_mono
          ((g.naturality h).hom.toNatTrans.app
            ((c.snd.app a).toFunctor.obj x))]
        simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
        simpa [canonicalLiftComparisonIso] using hc.symm))
    (by
      intro x y k
      apply CategoricalPullback.hom_ext
      · exact (Cat.Hom.toNatIso (c.fst.naturality h)).hom.naturality k
      · exact (Cat.Hom.toNatIso (c.snd.naturality h)).hom.naturality k)

@[simp]
theorem canonicalLiftApp_obj_fst
    (c : Cone (f := f) (g := g) T) (a : LocallyDiscrete Schemeᵒᵖ)
    (x : T.toPseudofunctor.obj a) :
    CategoricalPullback.fst ((canonicalLiftApp f g c a).obj x) =
      (c.fst.app a).toFunctor.obj x := rfl

@[simp]
theorem canonicalLiftApp_obj_snd
    (c : Cone (f := f) (g := g) T) (a : LocallyDiscrete Schemeᵒᵖ)
    (x : T.toPseudofunctor.obj a) :
    CategoricalPullback.snd ((canonicalLiftApp f g c a).obj x) =
      (c.snd.app a).toFunctor.obj x := rfl

@[simp]
theorem canonicalLiftApp_map_fst
    (c : Cone (f := f) (g := g) T) (a : LocallyDiscrete Schemeᵒᵖ)
    {x y : T.toPseudofunctor.obj a} (k : x ⟶ y) :
    ((canonicalLiftApp f g c a).map k).fst =
      (c.fst.app a).toFunctor.map k := rfl

@[simp]
theorem canonicalLiftApp_map_snd
    (c : Cone (f := f) (g := g) T) (a : LocallyDiscrete Schemeᵒᵖ)
    {x y : T.toPseudofunctor.obj a} (k : x ⟶ y) :
    ((canonicalLiftApp f g c a).map k).snd =
      (c.snd.app a).toFunctor.map k := rfl

@[simp]
theorem canonicalLiftNaturality_hom_app_fst
    (c : Cone (f := f) (g := g) T)
    {a b : LocallyDiscrete Schemeᵒᵖ} (h : a ⟶ b)
    (x : T.toPseudofunctor.obj a) :
    ((canonicalLiftNaturality f g c h).hom.app x).fst =
      (c.fst.naturality h).hom.toNatTrans.app x := rfl

@[simp]
theorem canonicalLiftNaturality_hom_app_snd
    (c : Cone (f := f) (g := g) T)
    {a b : LocallyDiscrete Schemeᵒᵖ} (h : a ⟶ b)
    (x : T.toPseudofunctor.obj a) :
    ((canonicalLiftNaturality f g c h).hom.app x).snd =
      (c.snd.naturality h).hom.toNatTrans.app x := rfl

@[simp]
theorem fiberTwoPullbackMapId_hom_app_fst
    (a : LocallyDiscrete Schemeᵒᵖ)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapId a).hom.toNatTrans.app p).fst =
      (X.toPseudofunctor.mapId a).hom.toNatTrans.app
        (CategoricalPullback.fst p) := rfl

@[simp]
theorem fiberTwoPullbackMapId_hom_app_snd
    (a : LocallyDiscrete Schemeᵒᵖ)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapId a).hom.toNatTrans.app p).snd =
      (Y.toPseudofunctor.mapId a).hom.toNatTrans.app
        (CategoricalPullback.snd p) := rfl

@[simp]
theorem fiberTwoPullbackMapComp_hom_app_fst
    {a b d : LocallyDiscrete Schemeᵒᵖ} (h : a ⟶ b) (k : b ⟶ d)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp h k).hom.toNatTrans.app p).fst =
      (X.toPseudofunctor.mapComp h k).hom.toNatTrans.app
        (CategoricalPullback.fst p) := rfl

@[simp]
theorem fiberTwoPullbackMapComp_hom_app_snd
    {a b d : LocallyDiscrete Schemeᵒᵖ} (h : a ⟶ b) (k : b ⟶ d)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp h k).hom.toNatTrans.app p).snd =
      (Y.toPseudofunctor.mapComp h k).hom.toNatTrans.app
        (CategoricalPullback.snd p) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
noncomputable def canonicalLiftRaw
    (c : Cone (f := f) (g := g) T) :
    Pseudofunctor.StrongTrans T.toPseudofunctor
      (StackInGroupoids.fiberTwoPullbackPseudofunctor f g) where
  app a := (canonicalLiftApp f g c a).toCatHom
  naturality h := Cat.Hom.isoMk (canonicalLiftNaturality f g c h)
  naturality_naturality {a b h k} eta := by
    have e : h = k := LocallyDiscrete.eq_of_hom eta
    subst k
    rw [Subsingleton.elim eta (𝟙 h)]
    cat_disch
  naturality_id a := by
    apply Cat.Hom₂.ext
    apply CategoricalPullback.natTrans_ext
    · ext x
      simp [canonicalLiftNaturality, canonicalLiftApp,
        StackInGroupoids.fiberTwoPullbackPseudofunctor]
      have hx := congrArg (fun q => q.toNatTrans.app x)
        (c.fst.naturality_id a)
      simpa only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
        Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
        Cat.rightUnitor_inv_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
        eqToHom_refl, StackInGroupoids.fiberTwoPullbackMapId,
        NatIso.ofComponents_hom_app, CategoricalPullback.mkIso_hom_fst,
        Cat.Hom.toNatIso_app_hom, Cat.Hom.comp_obj, Cat.Hom.id_obj] using hx
    · ext x
      simp [canonicalLiftNaturality, canonicalLiftApp,
        StackInGroupoids.fiberTwoPullbackPseudofunctor]
      have hx := congrArg (fun q => q.toNatTrans.app x)
        (c.snd.naturality_id a)
      simpa only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
        Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
        Cat.rightUnitor_inv_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
        eqToHom_refl, StackInGroupoids.fiberTwoPullbackMapId,
        NatIso.ofComponents_hom_app, CategoricalPullback.mkIso_hom_snd,
        Cat.Hom.toNatIso_app_hom, Cat.Hom.comp_obj, Cat.Hom.id_obj] using hx
  naturality_comp h k := by
    apply Cat.Hom₂.ext
    apply CategoricalPullback.natTrans_ext
    · ext x
      simp [canonicalLiftNaturality, canonicalLiftApp,
        StackInGroupoids.fiberTwoPullbackPseudofunctor]
      have hx := congrArg (fun q => q.toNatTrans.app x)
        (c.fst.naturality_comp h k)
      simpa only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
        Cat.whiskerRight_app, Cat.associator_hom_app,
        Cat.associator_inv_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
        eqToHom_refl, StackInGroupoids.fiberTwoPullbackMapComp,
        NatIso.ofComponents_hom_app, CategoricalPullback.mkIso_hom_fst,
        Cat.Hom.toNatIso_app_hom, Cat.Hom.comp_obj] using hx
    · ext x
      simp [canonicalLiftNaturality, canonicalLiftApp,
        StackInGroupoids.fiberTwoPullbackPseudofunctor]
      have hx := congrArg (fun q => q.toNatTrans.app x)
        (c.snd.naturality_comp h k)
      simpa only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
        Cat.whiskerRight_app, Cat.associator_hom_app,
        Cat.associator_inv_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
        eqToHom_refl, StackInGroupoids.fiberTwoPullbackMapComp,
        NatIso.ofComponents_hom_app, CategoricalPullback.mkIso_hom_snd,
        Cat.Hom.toNatIso_app_hom, Cat.Hom.comp_obj] using hx

/-- The universal pointwise lift, viewed as a morphism to the stack already proved by descent. -/
noncomputable def canonicalLift
    (c : Cone (f := f) (g := g) T) :
    StackHom T (fiberTwoPullbackStack f g) :=
  canonicalLiftRaw f g c

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
theorem canonicalLiftFstNaturality_hom_app
    (c : Cone (f := f) (g := g) T)
    {a b : LocallyDiscrete Schemeᵒᵖ} (h : a ⟶ b)
    (x : T.toPseudofunctor.obj a) :
    ((Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
      (fiberTwoPullbackFst f g)).naturality h).hom.toNatTrans.app x =
      (c.fst.naturality h).hom.toNatTrans.app x := by
  dsimp [Pseudofunctor.StrongTrans.vcomp,
    Pseudofunctor.StrongTrans.mkOfOplax,
    Pseudofunctor.StrongTrans.toOplax,
    Pseudofunctor.toOplax,
    CategoryTheory.Oplax.StrongTrans.vcomp,
    CategoryTheory.Oplax.StrongTrans.toOplax,
    CategoryTheory.Oplax.StrongTrans.mkOfOplax,
    CategoryTheory.Oplax.OplaxTrans.vcomp]
  simp only [Iso.trans_hom, whiskerRightIso_hom,
    whiskerLeftIso_hom, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Cat.comp_eq_comp, Cat.Hom.isoMk_hom,
    NatTrans.toCatHom₂_toNatTrans,
    canonicalLiftNaturality_hom_app_fst]
  simp only [Category.id_comp, Category.comp_id]
  dsimp only [fiberTwoPullbackFst, canonicalLiftRaw,
    Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans,
    CategoricalPullback.π₁_map]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem canonicalLiftFstRaw_app
    (c : Cone (f := f) (g := g) T) (a : LocallyDiscrete Schemeᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
      (fiberTwoPullbackFst f g)).app a = c.fst.app a := rfl

set_option backward.isDefEq.respectTransparency false in
theorem canonicalLiftFstNaturality_hom
    (c : Cone (f := f) (g := g) T)
    {a b : LocallyDiscrete Schemeᵒᵖ} (h : a ⟶ b) :
    ((Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
      (fiberTwoPullbackFst f g)).naturality h).hom =
        (c.fst.naturality h).hom := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  exact canonicalLiftFstNaturality_hom_app f g c h x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
noncomputable def canonicalLiftFstHomRaw
    (c : Cone (f := f) (g := g) T) :
    Pseudofunctor.StrongTrans.Modification
      (Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
        (fiberTwoPullbackFst f g)) c.fst where
  app _ := 𝟙 _
  naturality {a b} h := by
    rw [canonicalLiftFstNaturality_hom f g c h]
    cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def canonicalLiftFstInvRaw
    (c : Cone (f := f) (g := g) T) :
    Pseudofunctor.StrongTrans.Modification c.fst
      (Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
        (fiberTwoPullbackFst f g)) where
  app _ := 𝟙 _
  naturality {a b} h := by
    rw [canonicalLiftFstNaturality_hom f g c h]
    cat_disch

set_option backward.isDefEq.respectTransparency false in
noncomputable def canonicalLiftFstIsoRaw
    (c : Cone (f := f) (g := g) T) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
        (fiberTwoPullbackFst f g)) c.fst where
  hom := canonicalLiftFstHomRaw f g c
  inv := canonicalLiftFstInvRaw f g c
  hom_inv_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    simp [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id,
      canonicalLiftFstHomRaw, canonicalLiftFstInvRaw]
  inv_hom_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    simp [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id,
      canonicalLiftFstHomRaw, canonicalLiftFstInvRaw]

set_option backward.isDefEq.respectTransparency false in
noncomputable def canonicalLiftFstIso
    (c : Cone (f := f) (g := g) T) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (canonicalLift f g c)
        (fiberTwoPullbackFst f g)) c.fst :=
  canonicalLiftFstIsoRaw f g c

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
theorem canonicalLiftSndNaturality_hom_app
    (c : Cone (f := f) (g := g) T)
    {a b : LocallyDiscrete Schemeᵒᵖ} (h : a ⟶ b)
    (x : T.toPseudofunctor.obj a) :
    ((Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
      (fiberTwoPullbackSnd f g)).naturality h).hom.toNatTrans.app x =
      (c.snd.naturality h).hom.toNatTrans.app x := by
  dsimp [Pseudofunctor.StrongTrans.vcomp,
    Pseudofunctor.StrongTrans.mkOfOplax,
    Pseudofunctor.StrongTrans.toOplax,
    Pseudofunctor.toOplax,
    CategoryTheory.Oplax.StrongTrans.vcomp,
    CategoryTheory.Oplax.StrongTrans.toOplax,
    CategoryTheory.Oplax.StrongTrans.mkOfOplax,
    CategoryTheory.Oplax.OplaxTrans.vcomp]
  simp only [Iso.trans_hom, whiskerRightIso_hom,
    whiskerLeftIso_hom, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Cat.comp_eq_comp, Cat.Hom.isoMk_hom,
    NatTrans.toCatHom₂_toNatTrans,
    canonicalLiftNaturality_hom_app_snd]
  simp only [Category.id_comp, Category.comp_id]
  dsimp only [fiberTwoPullbackSnd, canonicalLiftRaw,
    Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans,
    CategoricalPullback.π₂_map]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem canonicalLiftSndRaw_app
    (c : Cone (f := f) (g := g) T) (a : LocallyDiscrete Schemeᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
      (fiberTwoPullbackSnd f g)).app a = c.snd.app a := rfl

set_option backward.isDefEq.respectTransparency false in
theorem canonicalLiftSndNaturality_hom
    (c : Cone (f := f) (g := g) T)
    {a b : LocallyDiscrete Schemeᵒᵖ} (h : a ⟶ b) :
    ((Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
      (fiberTwoPullbackSnd f g)).naturality h).hom =
        (c.snd.naturality h).hom := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  exact canonicalLiftSndNaturality_hom_app f g c h x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def canonicalLiftSndHomRaw
    (c : Cone (f := f) (g := g) T) :
    Pseudofunctor.StrongTrans.Modification
      (Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
        (fiberTwoPullbackSnd f g)) c.snd where
  app _ := 𝟙 _
  naturality {a b} h := by
    rw [canonicalLiftSndNaturality_hom f g c h]
    cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def canonicalLiftSndInvRaw
    (c : Cone (f := f) (g := g) T) :
    Pseudofunctor.StrongTrans.Modification c.snd
      (Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
        (fiberTwoPullbackSnd f g)) where
  app _ := 𝟙 _
  naturality {a b} h := by
    rw [canonicalLiftSndNaturality_hom f g c h]
    cat_disch

set_option backward.isDefEq.respectTransparency false in
noncomputable def canonicalLiftSndIsoRaw
    (c : Cone (f := f) (g := g) T) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (canonicalLiftRaw f g c)
        (fiberTwoPullbackSnd f g)) c.snd where
  hom := canonicalLiftSndHomRaw f g c
  inv := canonicalLiftSndInvRaw f g c
  hom_inv_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    simp [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id,
      canonicalLiftSndHomRaw, canonicalLiftSndInvRaw]
  inv_hom_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    simp [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id,
      canonicalLiftSndHomRaw, canonicalLiftSndInvRaw]

set_option backward.isDefEq.respectTransparency false in
noncomputable def canonicalLiftSndIso
    (c : Cone (f := f) (g := g) T) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (canonicalLift f g c)
        (fiberTwoPullbackSnd f g)) c.snd :=
  canonicalLiftSndIsoRaw f g c

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
theorem canonicalLift_compatible
    (c : Cone (f := f) (g := g) T) :
    ConeLiftClassifies (canonical f g) c (canonicalLift f g c)
      (canonicalLiftFstIso f g c) (canonicalLiftSndIso f g c) := by
  intro U x
  apply Iso.ext
  suffices
      (c.comparison.hom.app
          (LocallyDiscrete.mk (Opposite.op U))).toNatTrans.app x =
        (c.comparison.hom.app
            (LocallyDiscrete.mk (Opposite.op U))).toNatTrans.app x ≫
          (g.app (LocallyDiscrete.mk (Opposite.op U))).toFunctor.map
            (𝟙 (((Pseudofunctor.StrongTrans.vcomp
                (canonicalLift f g c) (fiberTwoPullbackSnd f g)).app
              (LocallyDiscrete.mk (Opposite.op U))).toFunctor.obj x)) by
    simpa [canonical, canonicalLift, canonicalLiftFstIso,
      canonicalLiftFstIsoRaw, canonicalLiftFstHomRaw,
      canonicalLiftSndIso, canonicalLiftSndIsoRaw,
      canonicalLiftSndHomRaw, canonicalLiftRaw, canonicalLiftApp,
      canonicalLiftComparisonIso, fiberTwoPullbackComparisonHom,
      fiberTwoPullbackComparisonApp, StackIso2.appIso,
      StackHom.appFunctor] using this
  let q := (c.comparison.hom.app
    (LocallyDiscrete.mk (Opposite.op U))).toNatTrans.app x
  let G := (g.app (LocallyDiscrete.mk (Opposite.op U))).toFunctor
  let y := ((Pseudofunctor.StrongTrans.vcomp
    (canonicalLift f g c) (fiberTwoPullbackSnd f g)).app
      (LocallyDiscrete.mk (Opposite.op U))).toFunctor.obj x
  calc
    q = q ≫ 𝟙 _ := (Category.comp_id q).symm
    _ = q ≫ G.map (𝟙 y) :=
      congrArg (fun z ↦ q ≫ z) (G.map_id y).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
noncomputable def canonicalUnproject
    {T : FppfStack.{u}} {h k : StackHom T (fiberTwoPullbackStack f g)}
    (p : ProjectionTwoCell (canonical f g) h k) :
    Pseudofunctor.StrongTrans.Modification h k where
  app a := NatTrans.toCatHom₂
    { app := fun x ↦
        { fst := (p.fst.app a).toNatTrans.app x
          snd := (p.snd.app a).toNatTrans.app x
          w := by
            rcases a with ⟨⟨U⟩⟩
            exact p.compatibility U x }
      naturality := by
        intro x y q
        apply CategoricalPullback.hom_ext
        · exact (p.fst.app a).toNatTrans.naturality q
        · exact (p.snd.app a).toNatTrans.naturality q }
  naturality {a b} q := by
    apply Cat.Hom₂.ext
    apply CategoricalPullback.natTrans_ext
    · ext x
      have hx0 := congrArg (fun m ↦ m.toNatTrans.app x)
        (p.fst.naturality q)
      have hx :
          (p.fst.app b).toNatTrans.app
                ((T.toPseudofunctor.map q).toFunctor.obj x) ≫
              (((k.naturality q).hom.toNatTrans.app x).fst ≫
                𝟙 ((X.toPseudofunctor.map q).toFunctor.obj
                  (CategoricalPullback.fst ((k.app a).toFunctor.obj x)))) =
            ((h.naturality q).hom.toNatTrans.app x).fst ≫
              (𝟙 ((X.toPseudofunctor.map q).toFunctor.obj
                  (CategoricalPullback.fst ((h.app a).toFunctor.obj x))) ≫
                (X.toPseudofunctor.map q).toFunctor.map
                  ((p.fst.app a).toNatTrans.app x)) := by
        simpa [whiskerRightModification, canonical, fiberTwoPullbackFst,
          StackInGroupoids.fiberTwoPullbackPseudofunctor,
          Pseudofunctor.StrongTrans.vcomp,
          Pseudofunctor.StrongTrans.mkOfOplax,
          Pseudofunctor.StrongTrans.toOplax,
          Pseudofunctor.toOplax,
          CategoryTheory.Oplax.StrongTrans.vcomp,
          CategoryTheory.Oplax.StrongTrans.toOplax,
          CategoryTheory.Oplax.StrongTrans.mkOfOplax,
          CategoryTheory.Oplax.OplaxTrans.vcomp] using hx0
      change
        (p.fst.app b).toNatTrans.app
              ((T.toPseudofunctor.map q).toFunctor.obj x) ≫
            ((k.naturality q).hom.toNatTrans.app x).fst =
          ((h.naturality q).hom.toNatTrans.app x).fst ≫
            (X.toPseudofunctor.map q).toFunctor.map
              ((p.fst.app a).toNatTrans.app x)
      calc
        _ = (p.fst.app b).toNatTrans.app
                ((T.toPseudofunctor.map q).toFunctor.obj x) ≫
              (((k.naturality q).hom.toNatTrans.app x).fst ≫
                𝟙 ((X.toPseudofunctor.map q).toFunctor.obj
                  (CategoricalPullback.fst ((k.app a).toFunctor.obj x)))) := by
          exact congrArg
            (fun z ↦ (p.fst.app b).toNatTrans.app
              ((T.toPseudofunctor.map q).toFunctor.obj x) ≫ z)
            (Category.comp_id
              (((k.naturality q).hom.toNatTrans.app x).fst)).symm
        _ = ((h.naturality q).hom.toNatTrans.app x).fst ≫
              (𝟙 ((X.toPseudofunctor.map q).toFunctor.obj
                  (CategoricalPullback.fst ((h.app a).toFunctor.obj x))) ≫
                (X.toPseudofunctor.map q).toFunctor.map
                  ((p.fst.app a).toNatTrans.app x)) := hx
        _ = _ := congrArg
          (fun z ↦ ((h.naturality q).hom.toNatTrans.app x).fst ≫ z)
          (Category.id_comp
            ((X.toPseudofunctor.map q).toFunctor.map
              ((p.fst.app a).toNatTrans.app x)))
    · ext x
      have hx0 := congrArg (fun m ↦ m.toNatTrans.app x)
        (p.snd.naturality q)
      have hx :
          (p.snd.app b).toNatTrans.app
                ((T.toPseudofunctor.map q).toFunctor.obj x) ≫
              (((k.naturality q).hom.toNatTrans.app x).snd ≫
                𝟙 ((Y.toPseudofunctor.map q).toFunctor.obj
                  (CategoricalPullback.snd ((k.app a).toFunctor.obj x)))) =
            ((h.naturality q).hom.toNatTrans.app x).snd ≫
              (𝟙 ((Y.toPseudofunctor.map q).toFunctor.obj
                  (CategoricalPullback.snd ((h.app a).toFunctor.obj x))) ≫
                (Y.toPseudofunctor.map q).toFunctor.map
                  ((p.snd.app a).toNatTrans.app x)) := by
        simpa [whiskerRightModification, canonical, fiberTwoPullbackSnd,
          StackInGroupoids.fiberTwoPullbackPseudofunctor,
          Pseudofunctor.StrongTrans.vcomp,
          Pseudofunctor.StrongTrans.mkOfOplax,
          Pseudofunctor.StrongTrans.toOplax,
          Pseudofunctor.toOplax,
          CategoryTheory.Oplax.StrongTrans.vcomp,
          CategoryTheory.Oplax.StrongTrans.toOplax,
          CategoryTheory.Oplax.StrongTrans.mkOfOplax,
          CategoryTheory.Oplax.OplaxTrans.vcomp] using hx0
      change
        (p.snd.app b).toNatTrans.app
              ((T.toPseudofunctor.map q).toFunctor.obj x) ≫
            ((k.naturality q).hom.toNatTrans.app x).snd =
          ((h.naturality q).hom.toNatTrans.app x).snd ≫
            (Y.toPseudofunctor.map q).toFunctor.map
              ((p.snd.app a).toNatTrans.app x)
      calc
        _ = (p.snd.app b).toNatTrans.app
                ((T.toPseudofunctor.map q).toFunctor.obj x) ≫
              (((k.naturality q).hom.toNatTrans.app x).snd ≫
                𝟙 ((Y.toPseudofunctor.map q).toFunctor.obj
                  (CategoricalPullback.snd ((k.app a).toFunctor.obj x)))) := by
          exact congrArg
            (fun z ↦ (p.snd.app b).toNatTrans.app
              ((T.toPseudofunctor.map q).toFunctor.obj x) ≫ z)
            (Category.comp_id
              (((k.naturality q).hom.toNatTrans.app x).snd)).symm
        _ = ((h.naturality q).hom.toNatTrans.app x).snd ≫
              (𝟙 ((Y.toPseudofunctor.map q).toFunctor.obj
                  (CategoricalPullback.snd ((h.app a).toFunctor.obj x))) ≫
                (Y.toPseudofunctor.map q).toFunctor.map
                  ((p.snd.app a).toNatTrans.app x)) := hx
        _ = _ := congrArg
          (fun z ↦ ((h.naturality q).hom.toNatTrans.app x).snd ≫ z)
          (Category.id_comp
            ((Y.toPseudofunctor.map q).toFunctor.map
              ((p.snd.app a).toNatTrans.app x)))

set_option backward.isDefEq.respectTransparency false in
theorem canonicalUnproject_projected
    {T : FppfStack.{u}} {h k : StackHom T (fiberTwoPullbackStack f g)}
    (p : ProjectionTwoCell (canonical f g) h k) :
    projectedTwoCell (canonical f g) (canonicalUnproject f g p) = p := by
  apply ProjectionTwoCell.ext
  · apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    rfl
  · apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem canonicalUnproject_projectedTwoCell
    {T : FppfStack.{u}} {h k : StackHom T (fiberTwoPullbackStack f g)}
    (eta : Pseudofunctor.StrongTrans.Modification h k) :
    canonicalUnproject f g (projectedTwoCell (canonical f g) eta) = eta := by
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext a
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  apply CategoricalPullback.hom_ext <;> rfl

/-- For the canonical fibrewise pullback, a modification is exactly a compatible pair of
projected modifications. -/
theorem canonicalProjectedTwoCell_bijective
    {T : FppfStack.{u}}
    (h k : StackHom T (fiberTwoPullbackStack f g)) :
    Function.Bijective
      (projectedTwoCell (canonical f g) (h := h) (k := k)) := by
  constructor
  · intro eta theta heq
    rw [← canonicalUnproject_projectedTwoCell f g eta,
      ← canonicalUnproject_projectedTwoCell f g theta, heq]
  · intro p
    exact ⟨canonicalUnproject f g p, canonicalUnproject_projected f g p⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
noncomputable def canonicalUniqueProjectedHom
    {T : FppfStack.{u}} (c : Cone (f := f) (g := g) T)
    (h : StackHom T (fiberTwoPullbackStack f g))
    (hfst : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackFst f g)) c.fst)
    (hsnd : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackSnd f g)) c.snd)
    (hcompatible : ConeLiftClassifies (canonical f g) c h hfst hsnd) :
    ProjectionTwoCell (canonical f g) h (canonicalLift f g c) where
  fst := Pseudofunctor.StrongTrans.Modification.vcomp hfst.hom
    (canonicalLiftFstIso f g c).inv
  snd := Pseudofunctor.StrongTrans.Modification.vcomp hsnd.hom
    (canonicalLiftSndIso f g c).inv
  compatibility U x := by
    have hc := congrArg Iso.hom (hcompatible U x)
    simpa [canonical, canonicalLift, canonicalLiftFstIso,
      canonicalLiftFstIsoRaw, canonicalLiftFstInvRaw,
      canonicalLiftSndIso, canonicalLiftSndIsoRaw,
      canonicalLiftSndInvRaw, canonicalLiftRaw, canonicalLiftApp,
      canonicalLiftComparisonIso, fiberTwoPullbackComparisonHom,
      fiberTwoPullbackComparisonApp, StackIso2.appIso,
      StackHom.appFunctor,
      Pseudofunctor.StrongTrans.Modification.vcomp] using hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def canonicalUniqueAppIso
    {T : FppfStack.{u}} (c : Cone (f := f) (g := g) T)
    (h : StackHom T (fiberTwoPullbackStack f g))
    (hfst : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackFst f g)) c.fst)
    (hsnd : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackSnd f g)) c.snd)
    (hcompatible : ConeLiftClassifies (canonical f g) c h hfst hsnd)
    (a : LocallyDiscrete Schemeᵒᵖ) :
    (h.app a).toFunctor ≅ ((canonicalLift f g c).app a).toFunctor :=
  NatIso.ofComponents
    (fun x ↦ CategoricalPullback.mkIso
      ((stackIso2AppIsoAt
        (hfst.trans (canonicalLiftFstIso f g c).symm) a).app x)
      ((stackIso2AppIsoAt
        (hsnd.trans (canonicalLiftSndIso f g c).symm) a).app x)
      (by
        rcases a with ⟨⟨U⟩⟩
        exact (canonicalUniqueProjectedHom f g c h hfst hsnd hcompatible).compatibility U x))
    (by
      intro x y q
      apply CategoricalPullback.hom_ext
      · exact (stackIso2AppIsoAt
          (hfst.trans (canonicalLiftFstIso f g c).symm) a).hom.naturality q
      · exact (stackIso2AppIsoAt
          (hsnd.trans (canonicalLiftSndIso f g c).symm) a).hom.naturality q)

noncomputable def canonicalUniqueHom
    {T : FppfStack.{u}} (c : Cone (f := f) (g := g) T)
    (h : StackHom T (fiberTwoPullbackStack f g))
    (hfst : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackFst f g)) c.fst)
    (hsnd : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackSnd f g)) c.snd)
    (hcompatible : ConeLiftClassifies (canonical f g) c h hfst hsnd) :
    Pseudofunctor.StrongTrans.Modification h (canonicalLift f g c) :=
  canonicalUnproject f g
    (canonicalUniqueProjectedHom f g c h hfst hsnd hcompatible)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalUniqueHom_app
    {T : FppfStack.{u}} (c : Cone (f := f) (g := g) T)
    (h : StackHom T (fiberTwoPullbackStack f g))
    (hfst : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackFst f g)) c.fst)
    (hsnd : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackSnd f g)) c.snd)
    (hcompatible : ConeLiftClassifies (canonical f g) c h hfst hsnd)
    (a : LocallyDiscrete Schemeᵒᵖ) :
    (canonicalUniqueHom f g c h hfst hsnd hcompatible).app a =
      (Cat.Hom.isoMk
        (canonicalUniqueAppIso f g c h hfst hsnd hcompatible a)).hom := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  apply CategoricalPullback.hom_ext <;> rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
noncomputable def canonicalUniqueInv
    {T : FppfStack.{u}} (c : Cone (f := f) (g := g) T)
    (h : StackHom T (fiberTwoPullbackStack f g))
    (hfst : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackFst f g)) c.fst)
    (hsnd : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackSnd f g)) c.snd)
    (hcompatible : ConeLiftClassifies (canonical f g) c h hfst hsnd) :
    Pseudofunctor.StrongTrans.Modification (canonicalLift f g c) h where
  app a := (Cat.Hom.isoMk
    (canonicalUniqueAppIso f g c h hfst hsnd hcompatible a)).inv
  naturality {a b} q := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    let ea := canonicalUniqueAppIso f g c h hfst hsnd hcompatible a
    let eb := canonicalUniqueAppIso f g c h hfst hsnd hcompatible b
    have hx := congrArg (fun m ↦ m.toNatTrans.app x)
      ((canonicalUniqueHom f g c h hfst hsnd hcompatible).naturality q)
    rw [canonicalUniqueHom_app f g c h hfst hsnd hcompatible a,
      canonicalUniqueHom_app f g c h hfst hsnd hcompatible b] at hx
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
      Cat.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Cat.Hom.isoMk_hom,
      Cat.Hom.isoMk_inv, NatTrans.toCatHom₂_toNatTrans] at hx ⊢
    change eb.inv.app ((T.toPseudofunctor.map q).toFunctor.obj x) ≫
        (h.naturality q).hom.toNatTrans.app x =
      ((canonicalLift f g c).naturality q).hom.toNatTrans.app x ≫
        ((fiberTwoPullbackStack f g).toPseudofunctor.map q).toFunctor.map
          (ea.inv.app x)
    change eb.hom.app ((T.toPseudofunctor.map q).toFunctor.obj x) ≫
        ((canonicalLift f g c).naturality q).hom.toNatTrans.app x =
      (h.naturality q).hom.toNatTrans.app x ≫
        ((fiberTwoPullbackStack f g).toPseudofunctor.map q).toFunctor.map
          (ea.hom.app x) at hx
    rw [← cancel_epi (eb.hom.app
      ((T.toPseudofunctor.map q).toFunctor.obj x))]
    rw [← Category.assoc, eb.hom_inv_id_app, Category.id_comp]
    rw [← Category.assoc]
    rw [hx]
    rw [Category.assoc, ← Functor.map_comp, ea.hom_inv_id_app]
    rw [((fiberTwoPullbackStack f g).toPseudofunctor.map q).toFunctor.map_id
      ((h.app a).toFunctor.obj x)]
    exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
noncomputable def canonicalLift_unique
    {T : FppfStack.{u}} (c : Cone (f := f) (g := g) T)
    (h : StackHom T (fiberTwoPullbackStack f g))
    (hfst : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackFst f g)) c.fst)
    (hsnd : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h (fiberTwoPullbackSnd f g)) c.snd)
    (hcompatible : ConeLiftClassifies (canonical f g) c h hfst hsnd) :
    StackIso2 h (canonicalLift f g c) where
  hom := canonicalUniqueHom f g c h hfst hsnd hcompatible
  inv := canonicalUniqueInv f g c h hfst hsnd hcompatible
  hom_inv_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    simp only [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id]
    rw [canonicalUniqueHom_app f g c h hfst hsnd hcompatible a]
    dsimp only [canonicalUniqueInv, Cat.Hom.isoMk_inv]
    exact congrArg NatTrans.toCatHom₂
      (canonicalUniqueAppIso f g c h hfst hsnd hcompatible a).hom_inv_id
  inv_hom_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    simp only [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id]
    rw [canonicalUniqueHom_app f g c h hfst hsnd hcompatible a]
    dsimp only [canonicalUniqueInv, Cat.Hom.isoMk_inv]
    exact congrArg NatTrans.toCatHom₂
      (canonicalUniqueAppIso f g c h hfst hsnd hcompatible a).inv_hom_id

/-- The canonical fibrewise categorical pullback satisfies the full bicategorical universal
property. Every field is populated by the explicit constructions above. -/
noncomputable def canonicalIsBilimit :
    IsBilimit (canonical f g) where
  lift := fun c ↦ canonicalLift f g c
  lift_fst := fun c ↦ canonicalLiftFstIso f g c
  lift_snd := fun c ↦ canonicalLiftSndIso f g c
  lift_compatible := fun c ↦ canonicalLift_compatible f g c
  lift_unique := fun c h hfst hsnd hcompatible ↦
    canonicalLift_unique f g c h hfst hsnd hcompatible
  projectedTwoCell_bijective := fun h k ↦
    canonicalProjectedTwoCell_bijective f g h k

/-- The canonical stack two-pullback, now equipped with its constructed bilimit proof. -/
noncomputable def canonicalGenuine : Genuine f g where
  toStackTwoPullback := canonical f g
  bilimit := canonicalIsBilimit f g

end StackTwoPullback
end GromovWitten.AlgebraicGeometry
