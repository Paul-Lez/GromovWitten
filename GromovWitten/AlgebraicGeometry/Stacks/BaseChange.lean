/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.PresentationTransport
import GromovWitten.AlgebraicGeometry.Stacks.TwoPullback

/-!
# Canonical base change of representable stack morphisms

This file constructs presentations for the second projection from the canonical genuine
two-pullback of stack morphisms.  The representing scheme map is inherited from the original
presentation, while the universal object, comparison cell, classifying object isomorphism,
and both uniqueness laws are reconstructed in the categorical pullback.

In particular, uniqueness is proved projection-by-projection.  The second projection is
recovered from the full comparison equation by cancellation of canonical isomorphisms, rather
than by truncating stack fibres or assuming their morphisms are subsingletons.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackMorphismPresentation

variable {X Y Z : FppfStack.{u}} (f : StackHom X Z) (g : StackHom Y Z)

set_option backward.isDefEq.respectTransparency false in
theorem stackHomNaturality_changeMap
    {S T : Scheme.{u}} {a b : S ⟶ T} (hab : a = b)
    (y : StackFiber Y T) :
    (Cat.Hom.toNatIso (g.naturality ⟨a.op⟩)).hom.app y ≫
        (stackPullbackObjIsoOfEq Z hab
          ((g.appFunctor T).obj y)).hom =
      (g.appFunctor S).map
          (stackPullbackObjIsoOfEq Y hab y).hom ≫
        (Cat.Hom.toNatIso (g.naturality ⟨b.op⟩)).hom.app y := by
  subst b
  simp [stackPullbackObjIsoOfEq]

set_option backward.isDefEq.respectTransparency false in
theorem stackHomNaturalityInv_changeMap
    {S T : Scheme.{u}} {a b : S ⟶ T} (hab : a = b)
    (y : StackFiber Y T) :
    (stackPullbackObjIsoOfEq Z hab ((g.appFunctor T).obj y)).hom ≫
        (Cat.Hom.toNatIso (g.naturality ⟨b.op⟩)).inv.app y ≫
        (g.appFunctor S).map
          (stackPullbackObjIsoOfEq Y hab.symm y).hom =
      (Cat.Hom.toNatIso (g.naturality ⟨a.op⟩)).inv.app y := by
  subst b
  simp [stackPullbackObjIsoOfEq]

theorem stackPullbackObjIsoOfEq_symm
    (W : FppfStack.{u}) {S T : Scheme.{u}} {a b : S ⟶ T}
    (hab : a = b) (z : StackFiber W T) :
    stackPullbackObjIsoOfEq W hab.symm z =
      (stackPullbackObjIsoOfEq W hab z).symm := by
  subst b
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem stackHomNaturalityCompPullback_inv
    {S U V : Scheme.{u}} (h : S ⟶ U) (qMap : U ⟶ V)
    (y : StackFiber Y V) :
    (stackPullback Z h).map
          ((Cat.Hom.toNatIso (g.naturality ⟨qMap.op⟩)).inv.app y) ≫
        (Cat.Hom.toNatIso (g.naturality ⟨h.op⟩)).inv.app
          ((stackPullback Y qMap).obj y) =
      (stackPullbackCompIso Z h qMap ((g.appFunctor V).obj y)).hom ≫
        (Cat.Hom.toNatIso (g.naturality ⟨(h ≫ qMap).op⟩)).inv.app y ≫
        (g.appFunctor S).map (stackPullbackCompIso Y h qMap y).inv := by
  let A := ((g.appFunctor S).mapIso (stackPullbackCompIso Y h qMap y)).trans
    ((Cat.Hom.toNatIso (g.naturality ⟨(h ≫ qMap).op⟩)).app y)
  let B := ((Cat.Hom.toNatIso (g.naturality ⟨h.op⟩)).app
      ((stackPullback Y qMap).obj y)).trans
    (((stackPullback Z h).mapIso
      ((Cat.Hom.toNatIso (g.naturality ⟨qMap.op⟩)).app y)).trans
        (stackPullbackCompIso Z h qMap ((g.appFunctor V).obj y)))
  have hhom : A.hom = B.hom := by
    exact stackHomNaturalityCompPullback g h qMap y
  have hinv : A.inv = B.inv := congrArg Iso.inv (Iso.ext hhom)
  dsimp only [A, B] at hinv
  simp only [Iso.trans_inv, Functor.mapIso_inv] at hinv
  rw [← cancel_epi
    (stackPullbackCompIso Z h qMap ((g.appFunctor V).obj y)).inv]
  simp only [Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, Iso.app_inv, Cat.comp_eq_comp,
    Functor.comp_obj] using hinv.symm

@[simp]
theorem stackPullback_fiberTwoPullback_iso_hom
    {S U : Scheme.{u}} (l : S ⟶ U)
    (x : StackFiber (fiberTwoPullbackStack f g) U) :
    (CategoricalPullback.iso
      ((stackPullback (fiberTwoPullbackStack f g) l).obj x)).hom =
      (Cat.Hom.toNatIso (f.naturality ⟨l.op⟩)).hom.app
          (CategoricalPullback.fst x) ≫
        (stackPullback Z l).map (CategoricalPullback.iso x).hom ≫
        (Cat.Hom.toNatIso (g.naturality ⟨l.op⟩)).inv.app
          (CategoricalPullback.snd x) := rfl

@[simp]
theorem stackPullback_fiberTwoPullback_fst
    {S U : Scheme.{u}} (l : S ⟶ U)
    (x : StackFiber (fiberTwoPullbackStack f g) U) :
    CategoricalPullback.fst
        ((stackPullback (fiberTwoPullbackStack f g) l).obj x) =
      (stackPullback X l).obj (CategoricalPullback.fst x) := rfl

@[simp]
theorem stackPullback_fiberTwoPullback_snd
    {S U : Scheme.{u}} (l : S ⟶ U)
    (x : StackFiber (fiberTwoPullbackStack f g) U) :
    CategoricalPullback.snd
        ((stackPullback (fiberTwoPullbackStack f g) l).obj x) =
      (stackPullback Y l).obj (CategoricalPullback.snd x) := rfl

@[simp]
theorem fiberTwoPullbackSnd_appFunctor_obj
    (S : Scheme.{u}) (x : StackFiber (fiberTwoPullbackStack f g) S) :
    (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x =
      CategoricalPullback.snd x := rfl

@[simp]
theorem fiberTwoPullbackSnd_appFunctor_map
    (S : Scheme.{u}) {x x' : StackFiber (fiberTwoPullbackStack f g) S}
    (h : x ⟶ x') :
    (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).map h = h.snd := rfl

@[simp]
theorem fiberTwoPullbackSnd_naturality_hom_app
    {S U : Scheme.{u}} (l : S ⟶ U)
    (x : StackFiber (fiberTwoPullbackStack f g) U) :
    (Cat.Hom.toNatIso ((fiberTwoPullbackSnd f g).naturality
      ⟨l.op⟩)).hom.app x = 𝟙 _ := rfl

@[simp]
theorem fiberTwoPullbackSnd_naturality_app_hom
    {S U : Scheme.{u}} (l : S ⟶ U)
    (x : StackFiber (fiberTwoPullbackStack f g) U) :
    ((Cat.Hom.toNatIso ((fiberTwoPullbackSnd f g).naturality
      ⟨l.op⟩)).app x).hom = 𝟙 _ := rfl

noncomputable def canonicalBaseChangeObject
    {T : Scheme.{u}} (y : StackFiber Y T)
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y)) :
    StackFiber (fiberTwoPullbackStack f g) p.space where
  fst := p.object
  snd := (stackPullback Y p.map).obj y
  iso := p.comparison.trans
    ((Cat.Hom.toNatIso (g.naturality ⟨p.map.op⟩)).symm.app y)

noncomputable def canonicalBaseChangeComparison
    {T S : Scheme.{u}} (y : StackFiber Y T) (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y) :
    (StackHom.appFunctor f S).obj (CategoricalPullback.fst x) ≅
      (stackPullback Z toBase).obj ((StackHom.appFunctor g T).obj y) :=
  (CategoricalPullback.iso x).trans (((StackHom.appFunctor g S).mapIso c).trans
    ((Cat.Hom.toNatIso (g.naturality ⟨toBase.op⟩)).app y))

noncomputable def canonicalBaseChangeLift
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y) : S ⟶ p.space :=
  p.lift toBase (CategoricalPullback.fst x)
    (canonicalBaseChangeComparison f g y toBase x c)

noncomputable def canonicalBaseChangeLiftFstIso
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y) :
    CategoricalPullback.fst x ≅ (stackPullback X
      (canonicalBaseChangeLift f g p toBase x c)).obj p.object :=
  p.liftObjectIso toBase (CategoricalPullback.fst x)
    (canonicalBaseChangeComparison f g y toBase x c)

noncomputable def canonicalBaseChangeLiftSndIso
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y) :
    CategoricalPullback.snd x ≅ (stackPullback Y
      (canonicalBaseChangeLift f g p toBase x c)).obj
        ((stackPullback Y p.map).obj y) :=
  c |>.trans
    (stackPullbackObjIsoOfEq Y
      (p.lift_map toBase (CategoricalPullback.fst x)
        (canonicalBaseChangeComparison f g y toBase x c)).symm y) |>.trans
    (stackPullbackCompIso Y
      (canonicalBaseChangeLift f g p toBase x c) p.map y).symm

set_option backward.isDefEq.respectTransparency false in
theorem canonicalBaseChangeLiftObjectIso_w
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y) :
    (f.appFunctor S).map
          (canonicalBaseChangeLiftFstIso f g p toBase x c).hom ≫
        (CategoricalPullback.iso
          ((stackPullback (fiberTwoPullbackStack f g)
            (canonicalBaseChangeLift f g p toBase x c)).obj
              (canonicalBaseChangeObject f g y p))).hom =
      (CategoricalPullback.iso x).hom ≫
        (g.appFunctor S).map
          (canonicalBaseChangeLiftSndIso f g p toBase x c).hom := by
  obtain ⟨hmap, hcomp⟩ := p.lift_compatible toBase
    (CategoricalPullback.fst x)
    (canonicalBaseChangeComparison f g y toBase x c)
  rw [stackPullback_fiberTwoPullback_iso_hom]
  dsimp only [canonicalBaseChangeLiftFstIso, canonicalBaseChangeLiftSndIso,
    canonicalBaseChangeLift, canonicalBaseChangeObject,
    StackInGroupoids.fiberTwoPullbackPseudofunctor,
    StackInGroupoids.fiberTwoPullbackMap,
    fiberTwoPullbackSnd, canonicalBaseChangeComparison]
  simp only [Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  change
    (f.appFunctor S).map
          (p.liftObjectIso toBase (CategoricalPullback.fst x)
            (canonicalBaseChangeComparison f g y toBase x c)).hom ≫
        (Cat.Hom.toNatIso (f.naturality
          ⟨(canonicalBaseChangeLift f g p toBase x c).op⟩)).hom.app p.object ≫
        (stackPullback Z (canonicalBaseChangeLift f g p toBase x c)).map
          p.comparison.hom ≫
        (stackPullback Z (canonicalBaseChangeLift f g p toBase x c)).map
          ((Cat.Hom.toNatIso (g.naturality ⟨p.map.op⟩)).inv.app y) ≫
        (Cat.Hom.toNatIso (g.naturality
          ⟨(canonicalBaseChangeLift f g p toBase x c).op⟩)).inv.app
            ((stackPullback Y p.map).obj y) =
      (CategoricalPullback.iso x).hom ≫
        (g.appFunctor S).map c.hom ≫
        (g.appFunctor S).map
          (stackPullbackObjIsoOfEq Y hmap.symm y).hom ≫
        (g.appFunctor S).map
          (stackPullbackCompIso Y
            (canonicalBaseChangeLift f g p toBase x c) p.map y).inv
  have hcompHom := congrArg Iso.hom hcomp
  simp only [stackMorphismInducedComparison, canonicalBaseChangeComparison,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc] at hcompHom
  rw [stackHomNaturalityCompPullback_inv g
    (canonicalBaseChangeLift f g p toBase x c) p.map y]
  unfold canonicalBaseChangeLift
  rw [← stackHomNaturalityInv_changeMap g hmap y]
  unfold canonicalBaseChangeComparison
  simp only [Iso.app_hom] at hcompHom ⊢
  simp only [Category.assoc]
  rw [reassoc_of% hcompHom]
  simp

/-- The isomorphism in the categorical pullback assembled from the two component
isomorphisms and the proved comparison-face equation. -/
noncomputable def canonicalBaseChangeLiftObjectIso
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y) :
    x ≅ (stackPullback (fiberTwoPullbackStack f g)
      (canonicalBaseChangeLift f g p toBase x c)).obj
        (canonicalBaseChangeObject f g y p) :=
  CategoricalPullback.mkIso
    (canonicalBaseChangeLiftFstIso f g p toBase x c)
    (canonicalBaseChangeLiftSndIso f g p toBase x c)
    (canonicalBaseChangeLiftObjectIso_w f g p toBase x c)

theorem canonicalBaseChangeLiftObjectIso_hom_snd_heq
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y) :
    HEq (canonicalBaseChangeLiftObjectIso f g p toBase x c).hom.snd
      (canonicalBaseChangeLiftSndIso f g p toBase x c).hom := by
  rfl

theorem canonicalBaseChangeLiftObjectIso_hom_fst_heq
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y) :
    HEq (canonicalBaseChangeLiftObjectIso f g p toBase x c).hom.fst
      (canonicalBaseChangeLiftFstIso f g p toBase x c).hom := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
theorem canonicalBaseChangeInducedComparison_hom
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}}
    (l : S ⟶ p.space) (x : StackFiber (fiberTwoPullbackStack f g) S)
    (e : x ≅ (stackPullback (fiberTwoPullbackStack f g) l).obj
      (canonicalBaseChangeObject f g y p)) :
    (stackMorphismInducedComparison (fiberTwoPullbackSnd f g) p.map
      (canonicalBaseChangeObject f g y p) y (Iso.refl _) l x e).hom =
      e.hom.snd ≫ (stackPullbackCompIso Y l p.map y).hom := by
  simp only [stackMorphismInducedComparison, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [fiberTwoPullbackSnd_appFunctor_map]
  rw [fiberTwoPullbackSnd_naturality_app_hom]
  simp
  exact (Category.assoc e.hom.snd (𝟙 _)
    (stackPullbackCompIso Y l p.map y).hom).symm.trans
      (congrArg (fun q ↦ q ≫ (stackPullbackCompIso Y l p.map y).hom)
        (Category.comp_id e.hom.snd))

theorem canonicalBaseChangeLift_compatible
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y) :
    StackMorphismClassifies (fiberTwoPullbackSnd f g) p.map
      (canonicalBaseChangeObject f g y p) y (Iso.refl _)
      toBase x c (canonicalBaseChangeLift f g p toBase x c)
      (canonicalBaseChangeLiftObjectIso f g p toBase x c) := by
  let hmap := p.lift_map toBase (CategoricalPullback.fst x)
    (canonicalBaseChangeComparison f g y toBase x c)
  refine ⟨hmap, ?_⟩
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [canonicalBaseChangeInducedComparison_hom]
  have hsnd :
      (canonicalBaseChangeLiftObjectIso f g p toBase x c).hom.snd =
        (canonicalBaseChangeLiftSndIso f g p toBase x c).hom :=
    eq_of_heq (canonicalBaseChangeLiftObjectIso_hom_snd_heq
      f g p toBase x c)
  rw [hsnd]
  unfold canonicalBaseChangeLift at *
  let aInv := stackPullbackObjIsoOfEq Y hmap.symm y
  let a := stackPullbackObjIsoOfEq Y hmap y
  let b := stackPullbackCompIso Y
    (p.lift toBase (CategoricalPullback.fst x)
      (canonicalBaseChangeComparison f g y toBase x c)) p.map y
  have hsndValue : canonicalBaseChangeLiftSndIso f g p toBase x c =
      (c.trans aInv).trans b.symm := rfl
  rw [hsndValue]
  have ha : aInv = a.symm := stackPullbackObjIsoOfEq_symm Y hmap y
  rw [ha]
  have hIso : (((c.trans a.symm).trans b.symm).trans b).trans a = c := by
    calc
      _ = ((c.trans a.symm).trans (b.symm.trans b)).trans a := by
        exact congrArg (fun q ↦ q.trans a)
          (Iso.trans_assoc (c.trans a.symm) b.symm b)
      _ = ((c.trans a.symm).trans (Iso.refl _)).trans a := by
        rw [Iso.symm_self_id b]
      _ = (c.trans a.symm).trans a := by rw [Iso.trans_refl]
      _ = c.trans (a.symm.trans a) := by rw [Iso.trans_assoc]
      _ = c.trans (Iso.refl _) := by rw [Iso.symm_self_id a]
      _ = c := Iso.trans_refl c
  change ((((c.trans a.symm).trans b.symm).trans b).trans a).hom = c.hom
  exact congrArg Iso.hom hIso

set_option backward.isDefEq.respectTransparency false in
/-- The first projection of an isomorphism in the canonical fibrewise
two-pullback is an isomorphism of the corresponding source-stack objects. -/
noncomputable def canonicalBaseChangeFstIso
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (l : S ⟶ p.space)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (e : x ≅ (stackPullback (fiberTwoPullbackStack f g) l).obj
      (canonicalBaseChangeObject f g y p)) :
    CategoricalPullback.fst x ≅
      (stackPullback X l).obj p.object :=
  (CategoricalPullback.π₁ _ _).mapIso e

set_option backward.isDefEq.respectTransparency false in
theorem canonicalBaseChangeCandidateComparison
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (l : S ⟶ p.space)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (e : x ≅ (stackPullback (fiberTwoPullbackStack f g) l).obj
      (canonicalBaseChangeObject f g y p))
    (hmap : l ≫ p.map = toBase) :
    (stackMorphismInducedComparison f p.map p.object
        ((StackHom.appFunctor g T).obj y) p.comparison l
        (CategoricalPullback.fst x)
        (canonicalBaseChangeFstIso f g p l x e)).trans
      (stackPullbackObjIsoOfEq Z hmap
        ((StackHom.appFunctor g T).obj y)) =
    canonicalBaseChangeComparison f g y toBase x
      ((stackMorphismInducedComparison (fiberTwoPullbackSnd f g) p.map
          (canonicalBaseChangeObject f g y p) y (Iso.refl _) l x e).trans
        (stackPullbackObjIsoOfEq Y hmap y)) := by
  apply Iso.ext
  unfold canonicalBaseChangeComparison
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [canonicalBaseChangeInducedComparison_hom]
  dsimp only [stackMorphismInducedComparison,
    canonicalBaseChangeFstIso,
    canonicalBaseChangeObject]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  have he := e.hom.w
  rw [stackPullback_fiberTwoPullback_iso_hom] at he
  dsimp only [canonicalBaseChangeObject,
    StackInGroupoids.fiberTwoPullbackPseudofunctor,
    StackInGroupoids.fiberTwoPullbackMap] at he
  simp only [Iso.trans_hom, Functor.map_comp,
    Category.assoc] at he
  simp only [Iso.app_hom] at he
  have hsymm :
      ((Cat.Hom.toNatIso
        (g.naturality ⟨p.map.op⟩)).symm.hom.app y) =
        (Cat.Hom.toNatIso
          (g.naturality ⟨p.map.op⟩)).inv.app y := rfl
  rw [hsymm] at he
  rw [stackHomNaturalityCompPullback_inv g l p.map y] at he
  rw [← cancel_mono
    ((Cat.Hom.toNatIso (g.naturality ⟨toBase.op⟩)).inv.app y)]
  rw [← cancel_mono
    ((g.appFunctor S).map
      (stackPullbackObjIsoOfEq Y hmap y).inv)]
  rw [← cancel_mono
    ((g.appFunctor S).map
      (stackPullbackCompIso Y l p.map y).inv)]
  have heqInv :
      (stackPullbackObjIsoOfEq Y hmap y).inv =
        (stackPullbackObjIsoOfEq Y hmap.symm y).hom := by
    rw [stackPullbackObjIsoOfEq_symm Y hmap y]
    rfl
  rw [heqInv]
  simp only [Category.assoc]
  rw [reassoc_of% stackHomNaturalityInv_changeMap g hmap y]
  simp only [Functor.map_comp, Category.assoc]
  simp only [Iso.app_hom]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [stackPullbackObjIsoOfEq_symm Y hmap y]
  simp only [Iso.symm_hom]
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  simp only [Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id]
  exact he

theorem canonicalBaseChangeCandidateClassifies
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y)
    (l : S ⟶ p.space)
    (e : x ≅ (stackPullback (fiberTwoPullbackStack f g) l).obj
      (canonicalBaseChangeObject f g y p))
    (compatible : StackMorphismClassifies (fiberTwoPullbackSnd f g)
      p.map (canonicalBaseChangeObject f g y p) y (Iso.refl _)
      toBase x c l e) :
    StackMorphismClassifies f p.map p.object
      ((StackHom.appFunctor g T).obj y) p.comparison toBase
      (CategoricalPullback.fst x)
      (canonicalBaseChangeComparison f g y toBase x c) l
      (canonicalBaseChangeFstIso f g p l x e) := by
  rcases compatible with ⟨hmap, hcomparison⟩
  refine ⟨hmap, ?_⟩
  rw [canonicalBaseChangeCandidateComparison f g p toBase l x e hmap]
  rw [hcomparison]

theorem canonicalBaseChangeLift_unique
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y)
    (l : S ⟶ p.space)
    (e : x ≅ (stackPullback (fiberTwoPullbackStack f g) l).obj
      (canonicalBaseChangeObject f g y p))
    (compatible : StackMorphismClassifies (fiberTwoPullbackSnd f g)
      p.map (canonicalBaseChangeObject f g y p) y (Iso.refl _)
      toBase x c l e) :
    l = canonicalBaseChangeLift f g p toBase x c := by
  exact p.lift_unique toBase (CategoricalPullback.fst x)
    (canonicalBaseChangeComparison f g y toBase x c) l
    (canonicalBaseChangeFstIso f g p l x e)
    (canonicalBaseChangeCandidateClassifies f g p toBase x c l e
      compatible)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalBaseChangeCompatible_hom_snd_unique
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y)
    (l : S ⟶ p.space)
    (e e' : x ≅ (stackPullback (fiberTwoPullbackStack f g) l).obj
      (canonicalBaseChangeObject f g y p))
    (compatible : StackMorphismClassifies (fiberTwoPullbackSnd f g)
      p.map (canonicalBaseChangeObject f g y p) y (Iso.refl _)
      toBase x c l e)
    (compatible' : StackMorphismClassifies (fiberTwoPullbackSnd f g)
      p.map (canonicalBaseChangeObject f g y p) y (Iso.refl _)
      toBase x c l e') :
    e.hom.snd = e'.hom.snd := by
  rcases compatible with ⟨hmap, hcomparison⟩
  rcases compatible' with ⟨hmap', hcomparison'⟩
  have hmapProof : hmap = hmap' := Subsingleton.elim _ _
  subst hmap'
  have htotal :
      (stackMorphismInducedComparison (fiberTwoPullbackSnd f g) p.map
          (canonicalBaseChangeObject f g y p) y (Iso.refl _) l x e).trans
          (stackPullbackObjIsoOfEq Y hmap y) =
        (stackMorphismInducedComparison (fiberTwoPullbackSnd f g) p.map
          (canonicalBaseChangeObject f g y p) y (Iso.refl _) l x e').trans
          (stackPullbackObjIsoOfEq Y hmap y) :=
    hcomparison.trans hcomparison'.symm
  have hhom := congrArg Iso.hom htotal
  simp only [Iso.trans_hom] at hhom
  rw [canonicalBaseChangeInducedComparison_hom,
    canonicalBaseChangeInducedComparison_hom] at hhom
  simp only [Category.assoc] at hhom
  have hhomAssoc :
      (e.hom.snd ≫ (stackPullbackCompIso Y l p.map y).hom) ≫
          (stackPullbackObjIsoOfEq Y hmap y).hom =
        (e'.hom.snd ≫ (stackPullbackCompIso Y l p.map y).hom) ≫
          (stackPullbackObjIsoOfEq Y hmap y).hom := by
    simpa only [Category.assoc] using hhom
  have hwithoutBaseChange :
      e.hom.snd ≫ (stackPullbackCompIso Y l p.map y).hom =
        e'.hom.snd ≫ (stackPullbackCompIso Y l p.map y).hom :=
    (cancel_mono (stackPullbackObjIsoOfEq Y hmap y).hom).mp hhomAssoc
  exact (cancel_mono (stackPullbackCompIso Y l p.map y).hom).mp
    hwithoutBaseChange

set_option backward.isDefEq.respectTransparency false in
theorem canonicalBaseChangeLiftObjectIso_unique
    {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y))
    {S : Scheme.{u}} (toBase : S ⟶ T)
    (x : StackFiber (fiberTwoPullbackStack f g) S)
    (c : (StackHom.appFunctor (fiberTwoPullbackSnd f g) S).obj x ≅
      (stackPullback Y toBase).obj y)
    (e : x ≅ (stackPullback (fiberTwoPullbackStack f g)
      (canonicalBaseChangeLift f g p toBase x c)).obj
        (canonicalBaseChangeObject f g y p))
    (compatible : StackMorphismClassifies (fiberTwoPullbackSnd f g)
      p.map (canonicalBaseChangeObject f g y p) y (Iso.refl _)
      toBase x c (canonicalBaseChangeLift f g p toBase x c) e) :
    e = canonicalBaseChangeLiftObjectIso f g p toBase x c := by
  apply Iso.ext
  apply CategoricalPullback.hom_ext
  · have hfstIso := p.liftObjectIso_unique toBase
      (CategoricalPullback.fst x)
      (canonicalBaseChangeComparison f g y toBase x c)
      (canonicalBaseChangeFstIso f g p
        (canonicalBaseChangeLift f g p toBase x c) x e)
      (canonicalBaseChangeCandidateClassifies f g p toBase x c
        (canonicalBaseChangeLift f g p toBase x c) e compatible)
    have hfst := congrArg Iso.hom hfstIso
    change e.hom.fst =
      (canonicalBaseChangeLiftFstIso f g p toBase x c).hom at hfst
    have hcanonical :
        (canonicalBaseChangeLiftObjectIso f g p toBase x c).hom.fst =
          (canonicalBaseChangeLiftFstIso f g p toBase x c).hom :=
      eq_of_heq (canonicalBaseChangeLiftObjectIso_hom_fst_heq
        f g p toBase x c)
    exact hfst.trans hcanonical.symm
  · exact canonicalBaseChangeCompatible_hom_snd_unique f g p toBase x c
      (canonicalBaseChangeLift f g p toBase x c) e
      (canonicalBaseChangeLiftObjectIso f g p toBase x c) compatible
      (canonicalBaseChangeLift_compatible f g p toBase x c)

set_option backward.isDefEq.respectTransparency false in
/-- Pulling an explicit presentation of `f` back along `g` gives an explicit
presentation of the canonical second projection.  All universal-property and
stabilizer-uniqueness fields are derived from the original presentation. -/
noncomputable def canonicalBaseChange
    {T : Scheme.{u}} (y : StackFiber Y T)
    (p : StackMorphismPresentation f T ((StackHom.appFunctor g T).obj y)) :
    @StackMorphismPresentation (fiberTwoPullbackStack f g) Y
      (fiberTwoPullbackSnd f g) T y where
  space := p.space
  map := p.map
  object := canonicalBaseChangeObject f g y p
  comparison := Iso.refl _
  lift := canonicalBaseChangeLift f g p
  lift_map := fun toBase x c ↦
    p.lift_map toBase (CategoricalPullback.fst x)
      (canonicalBaseChangeComparison f g y toBase x c)
  liftObjectIso := canonicalBaseChangeLiftObjectIso f g p
  lift_compatible := canonicalBaseChangeLift_compatible f g p
  liftObjectIso_unique := canonicalBaseChangeLiftObjectIso_unique f g p
  lift_unique := canonicalBaseChangeLift_unique f g p

end StackMorphismPresentation

namespace StackHom

variable {X Y Z : FppfStack.{u}} (f : StackHom X Z) (g : StackHom Y Z)

set_option backward.isDefEq.respectTransparency false in
/-- Raw representable properties are stable under the canonical genuine
two-pullback projection.  The representing scheme and its morphism are reused
from the corresponding presentation of `f`; only the stack-valued universal
object and its coherence are reconstructed. -/
theorem fiberTwoPullbackSnd_hasRepresentablePropertyRaw
    (P : MorphismProperty Scheme.{u})
    (hf : f.HasRepresentablePropertyRaw P) :
    @HasRepresentablePropertyRaw (fiberTwoPullbackStack f g) Y
      (fiberTwoPullbackSnd f g) P := by
  intro T y
  obtain ⟨⟨p, hp⟩⟩ := hf T ((g.appFunctor T).obj y)
  exact ⟨⟨StackMorphismPresentation.canonicalBaseChange f g y p, hp⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Representable properties, with their public 2-isomorphism-invariant
meaning, are stable under the canonical genuine two-pullback projection. -/
theorem fiberTwoPullbackSnd_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u})
    (hf : f.HasRepresentableProperty P) :
    @HasRepresentableProperty (fiberTwoPullbackStack f g) Y
      (fiberTwoPullbackSnd f g) P := by
  apply (hasRepresentableProperty_iff_raw P).mpr
  exact fiberTwoPullbackSnd_hasRepresentablePropertyRaw f g P
    ((hasRepresentableProperty_iff_raw P).mp hf)

end StackHom

end GromovWitten.AlgebraicGeometry
