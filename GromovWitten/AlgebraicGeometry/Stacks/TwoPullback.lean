/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.Algebraic
import GromovWitten.AlgebraicGeometry.Stacks.Descent
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Genuine two-pullbacks of groupoids

The categorical pullback of `F : A ⟤ S` and `G : B ⟤ S` has objects `(a, b, α)`, where
`α : F a ≅ G b`.  In particular, it retains the comparison isomorphism and is not the strict
equalizer of the two object maps.  Mathlib proves its two-dimensional universal property as an
equivalence between functor categories.

This file records that this construction stays inside groupoids and specializes it to every
fibre of a cospan of strong morphisms between groupoid-valued stacks.  These fibrewise objects
are the local model required of any exported stack two-pullback.
-/

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe v v₁ v₂ v₃ u u₁ u₂ u₃

/-- The genuine two-pullback category of a cospan of functors. -/
abbrev TwoPullback {A : Type u₁} {B : Type u₂} {S : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} S]
    (F : A ⥤ S) (G : B ⥤ S) :=
  CategoricalPullback F G

namespace TwoPullback

variable {A : Type u₁} {B : Type u₂} {S : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} S]
  (F : A ⥤ S) (G : B ⥤ S)

/-- First projection from a two-pullback. -/
abbrev fst : TwoPullback F G ⥤ A := CategoricalPullback.π₁ F G

/-- Second projection from a two-pullback. -/
abbrev snd : TwoPullback F G ⥤ B := CategoricalPullback.π₂ F G

/-- The specified invertible comparison 2-cell between the two composites. -/
abbrev comparison : fst F G ⋙ F ≅ snd F G ⋙ G :=
  CatCommSq.iso (fst F G) (snd F G) F G

/-- The two-dimensional universal property of the categorical pullback. -/
noncomputable abbrev universal (T : Type u) [Category.{v} T] :
    (T ⥤ TwoPullback F G) ≌ CategoricalPullback.CatCommSqOver F G T :=
  CategoricalPullback.functorEquiv F G T

/-- A genuine two-pullback of groupoids is again a groupoid. -/
noncomputable instance [IsGroupoid A] [IsGroupoid B] : IsGroupoid (TwoPullback F G) where
  all_isIso f := (CategoricalPullback.isIso_iff F G f).2 ⟨inferInstance, inferInstance⟩

/-- Swapping the two legs of a genuine categorical pullback retains the same two objects and
inverts the specified comparison isomorphism. -/
noncomputable def swapFunctor : TwoPullback F G ⥤ TwoPullback G F where
  obj p :=
    { fst := CategoricalPullback.snd p
      snd := CategoricalPullback.fst p
      iso := (CategoricalPullback.iso p).symm }
  map h :=
    { fst := h.snd
      snd := h.fst
      w := h.w' }
  map_id _ := by
    apply CategoricalPullback.hom_ext <;> simp
  map_comp _ _ := by
    apply CategoricalPullback.hom_ext <;> simp

@[simp]
theorem swapFunctor_obj_fst (p : TwoPullback F G) :
    CategoricalPullback.fst ((swapFunctor F G).obj p) =
      CategoricalPullback.snd p := rfl

@[simp]
theorem swapFunctor_obj_snd (p : TwoPullback F G) :
    CategoricalPullback.snd ((swapFunctor F G).obj p) =
      CategoricalPullback.fst p := rfl

@[simp]
theorem swapFunctor_map_fst {p q : TwoPullback F G} (h : p ⟶ q) :
    ((swapFunctor F G).map h).fst = h.snd := rfl

@[simp]
theorem swapFunctor_map_snd {p q : TwoPullback F G} (h : p ⟶ q) :
    ((swapFunctor F G).map h).snd = h.fst := rfl

/-- Categorical two-pullbacks are symmetric.  This equivalence is involutive: applying its
functor twice is naturally isomorphic to the identity by componentwise identity arrows. -/
noncomputable def swapEquivalence : TwoPullback F G ≌ TwoPullback G F where
  functor := swapFunctor F G
  inverse := swapFunctor G F
  unitIso := NatIso.ofComponents
    (fun _ ↦ CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
      dsimp [swapFunctor]
      simp))
    (by
      intro _ _ h
      apply CategoricalPullback.hom_ext
      · change h.fst ≫ 𝟙 _ = 𝟙 _ ≫ h.fst
        simp
      · change h.snd ≫ 𝟙 _ = 𝟙 _ ≫ h.snd
        simp)
  counitIso := NatIso.ofComponents
    (fun _ ↦ CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
      dsimp [swapFunctor]
      simp))
    (by
      intro _ _ h
      apply CategoricalPullback.hom_ext
      · change h.fst ≫ 𝟙 _ = 𝟙 _ ≫ h.fst
        simp
      · change h.snd ≫ 𝟙 _ = 𝟙 _ ≫ h.snd
        simp)
  functor_unitIso_comp := by
    intro p
    apply CategoricalPullback.hom_ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp

/-- Pulling a functor back along the identity functor on its target recovers its source.  This
is an actual equivalence with the categorical pullback, including the comparison isomorphism
stored in every pullback object. -/
noncomputable def rightIdentityEquivalence :
    A ≌ TwoPullback F (𝟭 S) where
  functor :=
    { obj := fun a ↦
        { fst := a
          snd := F.obj a
          iso := Iso.refl _ }
      map := fun h ↦
        { fst := h
          snd := F.map h
          w := by simp }
      map_id := fun _ ↦ by ext <;> simp
      map_comp := fun _ _ ↦ by ext <;> simp }
  inverse := CategoricalPullback.π₁ F (𝟭 S)
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun p ↦ CategoricalPullback.mkIso
      (Iso.refl _) (CategoricalPullback.iso p)
        (by
          dsimp only [Functor.comp_obj, Functor.id_obj,
            CategoricalPullback.π₁, Iso.refl_hom]
          rw [F.map_id, Functor.id_map, Category.id_comp]))
    (by
      intro p q h
      apply CategoricalPullback.hom_ext
      · change h.fst ≫ 𝟙 _ = 𝟙 _ ≫ h.fst
        simp
      · change F.map h.fst ≫ q.iso.hom = p.iso.hom ≫ h.snd
        simpa only [Functor.id_map] using h.w)
  functor_unitIso_comp := by
    intro a
    apply CategoricalPullback.hom_ext
    · change 𝟙 a ≫ 𝟙 a = 𝟙 a
      simp
    · change F.map (𝟙 a) ≫ 𝟙 (F.obj a) = 𝟙 (F.obj a)
      rw [F.map_id]
      simp

end TwoPullback

namespace CategoricalPullback

variable {A : Type u₁} {B : Type u₂} {S : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} S]
  {F : A ⥤ S} {G : B ⥤ S}

@[simp]
theorem eqToHom_fst {p q : CategoricalPullback F G} (e : p = q) :
    (eqToHom e : p ⟶ q).fst =
      eqToHom (congrArg CategoricalPullback.fst e) := by
  subst e
  rfl

@[simp]
theorem eqToHom_snd {p q : CategoricalPullback F G} (e : p = q) :
    (eqToHom e : p ⟶ q).snd =
      eqToHom (congrArg CategoricalPullback.snd e) := by
  subst e
  rfl

/-- If the second cospan functor is fully faithful, a morphism of categorical pullbacks is
determined by its first projection.  The comparison-square equations determine the second
projection, so no extra compatibility can be chosen independently. -/
theorem hom_ext_of_fst_of_fullyFaithfulSecond
    {p q : CategoricalPullback F G} {h k : p ⟶ q}
    (hG : G.FullyFaithful) (hfst : h.fst = k.fst) : h = k := by
  apply CategoricalPullback.hom_ext
  · exact hfst
  · apply hG.map_injective
    rw [← cancel_epi (CategoricalPullback.iso p).hom]
    rw [← h.w, ← k.w, hfst]

universe v₄ v₅ v₆ u₄ u₅ u₆

variable {C : Type u₃} [Category.{v₃} C]
  {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
  [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
  {F₀ : A ⥤ C} {G₀ : B ⥤ C} {F₁ : A' ⥤ C'} {G₁ : B' ⥤ C'}
  (left : A ⥤ A') (base : C ⥤ C') (right : B ⥤ B')
  (alpha : left ⋙ F₁ ≅ F₀ ⋙ base) (beta : G₀ ⋙ base ≅ right ⋙ G₁)

/-- A compatible triple of functors sends genuine categorical pullbacks to genuine
categorical pullbacks.  The comparison isomorphism in every source object is transported
through the two cospan squares rather than replaced by an equality. -/
noncomputable def mapCospan :
    CategoricalPullback F₀ G₀ ⥤ CategoricalPullback F₁ G₁ where
  obj p :=
    { fst := left.obj p.fst
      snd := right.obj p.snd
      iso := alpha.app p.fst ≪≫ base.mapIso p.iso ≪≫ beta.app p.snd }
  map {p q} h :=
    { fst := left.map h.fst
      snd := right.map h.snd
      w := by
        dsimp
        rw [Category.assoc, Category.assoc, ← Functor.comp_map,
          alpha.hom.naturality_assoc, ← Functor.comp_map,
          ← beta.hom.naturality]
        dsimp
        rw [← base.map_comp_assoc, ← base.map_comp_assoc, h.w] }
  map_id p := by
    apply CategoryTheory.Limits.CategoricalPullback.hom_ext <;> simp
  map_comp h k := by
    apply CategoryTheory.Limits.CategoricalPullback.hom_ext <;> simp

instance mapCospan_faithful [left.Faithful] [right.Faithful] :
    (mapCospan left base right alpha beta).Faithful where
  map_injective {p q} h k e := by
    apply CategoryTheory.Limits.CategoricalPullback.hom_ext
    · exact left.map_injective
        (congrArg CategoryTheory.Limits.CategoricalPullback.Hom.fst e)
    · exact right.map_injective
        (congrArg CategoryTheory.Limits.CategoricalPullback.Hom.snd e)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance mapCospan_full [base.Faithful] [left.Full] [right.Full] :
    (mapCospan left base right alpha beta).Full where
  map_surjective {p q} h :=
    ⟨{ fst := left.preimage h.fst
       snd := right.preimage h.snd
       w := base.map_injective (by
         rw [← cancel_mono (beta.hom.app _), ← cancel_epi (alpha.hom.app _),
           base.map_comp, base.map_comp, Category.assoc, Category.assoc]
         calc
           _ = (left ⋙ F₁).map (left.preimage h.fst) ≫
                 alpha.hom.app q.fst ≫ base.map q.iso.hom ≫ beta.hom.app q.snd := by
               rw [← Functor.comp_map, ← alpha.hom.naturality_assoc]
           _ = alpha.hom.app p.fst ≫ base.map p.iso.hom ≫ beta.hom.app p.snd ≫
                 (right ⋙ G₁).map (right.preimage h.snd) := by
               simp only [Functor.comp_map, Functor.map_preimage]
               simpa only [mapCospan, Iso.trans_hom, Functor.mapIso_hom,
                 Iso.app_hom, Category.assoc] using h.w
           _ = _ := by
               rw [← Functor.comp_map, beta.hom.naturality]) },
      by
        apply CategoryTheory.Limits.CategoricalPullback.hom_ext
        · exact Functor.map_preimage _ _
        · exact Functor.map_preimage _ _⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance mapCospan_essSurj
    [left.EssSurj] [right.EssSurj] [base.Full] [base.Faithful] :
    (mapCospan left base right alpha beta).EssSurj where
  mem_essImage q := by
    let eleft : left.obj (left.objPreimage q.fst) ≅ q.fst :=
      left.objObjPreimageIso q.fst
    let eright : right.obj (right.objPreimage q.snd) ≅ q.snd :=
      right.objObjPreimageIso q.snd
    let ebase :
        base.obj (F₀.obj (left.objPreimage q.fst)) ≅
          base.obj (G₀.obj (right.objPreimage q.snd)) :=
      (alpha.app _).symm ≪≫ F₁.mapIso eleft ≪≫ q.iso ≪≫
        G₁.mapIso eright.symm ≪≫ (beta.app _).symm
    let p : CategoricalPullback F₀ G₀ :=
      { fst := left.objPreimage q.fst
        snd := right.objPreimage q.snd
        iso := (Functor.FullyFaithful.ofFullyFaithful base).preimageIso ebase }
    refine ⟨p, ⟨CategoryTheory.Limits.CategoricalPullback.mkIso eleft eright ?_⟩⟩
    dsimp [p, ebase, eleft, eright, mapCospan]
    simp

noncomputable instance mapCospan_isEquivalence
    [left.IsEquivalence] [base.IsEquivalence] [right.IsEquivalence] :
    (mapCospan left base right alpha beta).IsEquivalence where

end CategoricalPullback

namespace Cat.Hom

@[simp]
theorem toNatIso_app_hom {A B : Cat.{v, u}} {F G : A ⟶ B} (e : F ≅ G) (p : A) :
    ((Cat.Hom.toNatIso e).app p).hom = e.hom.toNatTrans.app p := rfl

@[simp]
theorem toNatIso_app_inv {A B : Cat.{v, u}} {F G : A ⟶ B} (e : F ≅ G) (p : A) :
    ((Cat.Hom.toNatIso e).app p).inv = e.inv.toNatTrans.app p := rfl

end Cat.Hom

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {X Y Z : StackInGroupoids.{v, v₁, u, u₁} C J}

/-- The genuine two-pullback groupoid of a cospan of stack morphisms over one test object.

The third component of an object is an isomorphism in the fibre of `Z`; it is never replaced by
an equality. -/
abbrev FiberTwoPullback
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    (U : C) :=
  TwoPullback (f.app ⟨Opposite.op U⟩).toFunctor (g.app ⟨Opposite.op U⟩).toFunctor

noncomputable instance fiberTwoPullbackIsGroupoid
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    (U : C) : IsGroupoid (FiberTwoPullback f g U) := by
  dsimp only [FiberTwoPullback, TwoPullback]
  infer_instance

/-- Universal property of the two-pullback groupoid in a test fibre. -/
noncomputable abbrev fiberTwoPullbackUniversal
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    (U : C) (T : Type u₂) [Category.{v₂} T] :
    (T ⥤ FiberTwoPullback f g U) ≌
      CategoricalPullback.CatCommSqOver
        (f.app ⟨Opposite.op U⟩).toFunctor (g.app ⟨Opposite.op U⟩).toFunctor T :=
  TwoPullback.universal _ _ T

/-- Reindex the genuine fibrewise two-pullback along a morphism in the base site.

The comparison isomorphism is transported through the strong-naturality cells of both legs;
this is the point at which a strict objectwise pullback would lose essential 2-categorical
information. -/
noncomputable def fiberTwoPullbackMap
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    {a b : LocallyDiscrete Cᵒᵖ} (h : a ⟶ b) :
    TwoPullback (f.app a).toFunctor (g.app a).toFunctor ⥤
      TwoPullback (f.app b).toFunctor (g.app b).toFunctor where
  obj p :=
    { fst := (X.toPseudofunctor.map h).toFunctor.obj (CategoricalPullback.fst p)
      snd := (Y.toPseudofunctor.map h).toFunctor.obj (CategoricalPullback.snd p)
      iso := (Cat.Hom.toNatIso (f.naturality h)).app (CategoricalPullback.fst p) ≪≫
        (Z.toPseudofunctor.map h).toFunctor.mapIso (CategoricalPullback.iso p) ≪≫
        (Cat.Hom.toNatIso (g.naturality h)).symm.app (CategoricalPullback.snd p) }
  map {p q} k :=
    { fst := (X.toPseudofunctor.map h).toFunctor.map k.fst
      snd := (Y.toPseudofunctor.map h).toFunctor.map k.snd
      w := by
        dsimp
        calc
          _ = (Cat.Hom.toNatIso (f.naturality h)).hom.app
                (CategoricalPullback.fst p) ≫
              (Z.toPseudofunctor.map h).toFunctor.map
                ((f.app a).toFunctor.map k.fst) ≫
              (Z.toPseudofunctor.map h).toFunctor.map
                (CategoricalPullback.iso q).hom ≫
              (Cat.Hom.toNatIso (g.naturality h)).inv.app
                (CategoricalPullback.snd q) := by
            simpa only [Cat.comp_eq_comp, Functor.comp_map, Category.assoc] using
              ((Cat.Hom.toNatIso (f.naturality h)).hom.naturality_assoc k.fst
                ((Z.toPseudofunctor.map h).toFunctor.map
                  (CategoricalPullback.iso q).hom ≫
                  (Cat.Hom.toNatIso (g.naturality h)).inv.app
                    (CategoricalPullback.snd q)))
          _ = (Cat.Hom.toNatIso (f.naturality h)).hom.app
                (CategoricalPullback.fst p) ≫
              (Z.toPseudofunctor.map h).toFunctor.map
                (CategoricalPullback.iso p).hom ≫
              (Z.toPseudofunctor.map h).toFunctor.map
                ((g.app a).toFunctor.map k.snd) ≫
              (Cat.Hom.toNatIso (g.naturality h)).inv.app
                (CategoricalPullback.snd q) := by
            rw [← Functor.map_comp_assoc, k.w, Functor.map_comp_assoc]
          _ = _ := by
            have hg_nat :=
              (Cat.Hom.toNatIso (g.naturality h)).inv.naturality k.snd
            simp only [Cat.comp_eq_comp, Functor.comp_map] at hg_nat
            simpa only [Category.assoc] using congrArg
              (fun t =>
                (Cat.Hom.toNatIso (f.naturality h)).hom.app
                    (CategoricalPullback.fst p) ≫
                  (Z.toPseudofunctor.map h).toFunctor.map
                    (CategoricalPullback.iso p).hom ≫ t)
              hg_nat }

@[simp]
theorem fiberTwoPullbackMap_obj_fst
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    {a b : LocallyDiscrete Cᵒᵖ} (h : a ⟶ b)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    CategoricalPullback.fst ((fiberTwoPullbackMap f g h).obj p) =
      (X.toPseudofunctor.map h).toFunctor.obj (CategoricalPullback.fst p) := rfl

@[simp]
theorem fiberTwoPullbackMap_obj_snd
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    {a b : LocallyDiscrete Cᵒᵖ} (h : a ⟶ b)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    CategoricalPullback.snd ((fiberTwoPullbackMap f g h).obj p) =
      (Y.toPseudofunctor.map h).toFunctor.obj (CategoricalPullback.snd p) := rfl

@[simp]
theorem fiberTwoPullbackMap_map_fst
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    {a b : LocallyDiscrete Cᵒᵖ} (h : a ⟶ b)
    {p q : TwoPullback (f.app a).toFunctor (g.app a).toFunctor} (l : p ⟶ q) :
    ((fiberTwoPullbackMap f g h).map l).fst =
      (X.toPseudofunctor.map h).toFunctor.map l.fst := rfl

@[simp]
theorem fiberTwoPullbackMap_map_snd
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    {a b : LocallyDiscrete Cᵒᵖ} (h : a ⟶ b)
    {p q : TwoPullback (f.app a).toFunctor (g.app a).toFunctor} (l : p ⟶ q) :
    ((fiberTwoPullbackMap f g h).map l).snd =
      (Y.toPseudofunctor.map h).toFunctor.map l.snd := rfl

@[simp]
theorem fiberTwoPullbackMap_toCatHom_obj_fst
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    {a b : LocallyDiscrete Cᵒᵖ} (h : a ⟶ b)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    CategoricalPullback.fst ((fiberTwoPullbackMap f g h).toCatHom.toFunctor.obj p) =
      (X.toPseudofunctor.map h).toFunctor.obj (CategoricalPullback.fst p) := rfl

@[simp]
theorem fiberTwoPullbackMap_toCatHom_obj_snd
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    {a b : LocallyDiscrete Cᵒᵖ} (h : a ⟶ b)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    CategoricalPullback.snd ((fiberTwoPullbackMap f g h).toCatHom.toFunctor.obj p) =
      (Y.toPseudofunctor.map h).toFunctor.obj (CategoricalPullback.snd p) := rfl

@[simp]
theorem fiberTwoPullbackMap_toCatHom_map_fst
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    {a b : LocallyDiscrete Cᵒᵖ} (h : a ⟶ b)
    {p q : TwoPullback (f.app a).toFunctor (g.app a).toFunctor} (l : p ⟶ q) :
    ((fiberTwoPullbackMap f g h).toCatHom.toFunctor.map l).fst =
      (X.toPseudofunctor.map h).toFunctor.map l.fst := rfl

@[simp]
theorem fiberTwoPullbackMap_toCatHom_map_snd
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    {a b : LocallyDiscrete Cᵒᵖ} (h : a ⟶ b)
    {p q : TwoPullback (f.app a).toFunctor (g.app a).toFunctor} (l : p ⟶ q) :
    ((fiberTwoPullbackMap f g h).toCatHom.toFunctor.map l).snd =
      (Y.toPseudofunctor.map h).toFunctor.map l.snd := rfl

/-- The identity coherence for `fiberTwoPullbackMap`. -/
noncomputable def fiberTwoPullbackMapId
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    (a : LocallyDiscrete Cᵒᵖ) :
    fiberTwoPullbackMap f g (𝟙 a) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun p =>
    CategoricalPullback.mkIso
      ((Cat.Hom.toNatIso (X.toPseudofunctor.mapId a)).app (CategoricalPullback.fst p))
      ((Cat.Hom.toNatIso (Y.toPseudofunctor.mapId a)).app (CategoricalPullback.snd p))
      (by
        have hf := congrArg
          (fun q => q.toNatTrans.app (CategoricalPullback.fst p))
          (f.naturality_id a)
        have hg := congrArg
          (fun q => q.toNatTrans.app (CategoricalPullback.snd p))
          (g.naturality_id a)
        have hf_id :
            (f.naturality (𝟙 a)).hom.toNatTrans.app
                (CategoricalPullback.fst p) ≫
              (Z.toPseudofunctor.mapId a).hom.toNatTrans.app
                ((f.app a).toFunctor.obj (CategoricalPullback.fst p)) =
              (f.app a).toFunctor.map
                ((X.toPseudofunctor.mapId a).hom.toNatTrans.app
                  (CategoricalPullback.fst p)) := by
          simpa only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
            Cat.whiskerRight_toNatTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
            Functor.whiskerRight_app, Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app,
            Cat.comp_eq_comp, Cat.id_eq_id, Functor.comp_obj, Functor.id_obj,
            eqToHom_refl, Category.comp_id, Category.id_comp] using hf
        have hg_id :
            (g.naturality (𝟙 a)).hom.toNatTrans.app
                (CategoricalPullback.snd p) ≫
              (Z.toPseudofunctor.mapId a).hom.toNatTrans.app
                ((g.app a).toFunctor.obj (CategoricalPullback.snd p)) =
              (g.app a).toFunctor.map
                ((Y.toPseudofunctor.mapId a).hom.toNatTrans.app
                  (CategoricalPullback.snd p)) := by
          simpa only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
            Cat.whiskerRight_toNatTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
            Functor.whiskerRight_app, Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app,
            Cat.comp_eq_comp, Cat.id_eq_id, Functor.comp_obj, Functor.id_obj,
            eqToHom_refl, Category.comp_id, Category.id_comp] using hg
        dsimp [fiberTwoPullbackMap]
        dsimp only [Cat.Hom.toNatIso]
        simp only [Category.assoc]
        calc
          _ = (f.naturality (𝟙 a)).hom.toNatTrans.app (CategoricalPullback.fst p) ≫
              (Z.toPseudofunctor.mapId a).hom.toNatTrans.app
                ((f.app a).toFunctor.obj (CategoricalPullback.fst p)) ≫
              (CategoricalPullback.iso p).hom := by
            simpa only [Cat.comp_eq_comp, Cat.id_eq_id, Functor.comp_obj,
              Functor.id_obj, Category.assoc] using congrArg
              (fun t => t ≫ (CategoricalPullback.iso p).hom) hf_id.symm
          _ = (f.naturality (𝟙 a)).hom.toNatTrans.app (CategoricalPullback.fst p) ≫
              (Z.toPseudofunctor.map (𝟙 a)).toFunctor.map
                (CategoricalPullback.iso p).hom ≫
              (Z.toPseudofunctor.mapId a).hom.toNatTrans.app
                ((g.app a).toFunctor.obj (CategoricalPullback.snd p)) := by
            simpa only [Cat.comp_eq_comp, Cat.id_eq_id, Functor.comp_obj,
              Functor.id_obj, Functor.id_map, Category.assoc] using congrArg
              (fun t => (f.naturality (𝟙 a)).hom.toNatTrans.app
                (CategoricalPullback.fst p) ≫ t)
              ((Z.toPseudofunctor.mapId a).hom.toNatTrans.naturality
                (CategoricalPullback.iso p).hom).symm
          _ = _ := by
            have hg_inv :
                (Z.toPseudofunctor.mapId a).hom.toNatTrans.app
                    ((g.app a).toFunctor.obj (CategoricalPullback.snd p)) =
                  (g.naturality (𝟙 a)).inv.toNatTrans.app
                      (CategoricalPullback.snd p) ≫
                    (g.app a).toFunctor.map
                      ((Y.toPseudofunctor.mapId a).hom.toNatTrans.app
                        (CategoricalPullback.snd p)) := by
              rw [← cancel_epi
                ((g.naturality (𝟙 a)).hom.toNatTrans.app
                  (CategoricalPullback.snd p))]
              simpa only [Category.assoc,
                Cat.Hom.hom_inv_id_toNatTrans_app_assoc] using hg_id
            simpa only [Category.assoc] using congrArg
              (fun t =>
                (f.naturality (𝟙 a)).hom.toNatTrans.app
                    (CategoricalPullback.fst p) ≫
                  (Z.toPseudofunctor.map (𝟙 a)).toFunctor.map
                    (CategoricalPullback.iso p).hom ≫ t)
              hg_inv))
    (by
      intro p q k
      apply CategoricalPullback.hom_ext
      · change (X.toPseudofunctor.map (𝟙 a)).toFunctor.map k.fst ≫
            (Cat.Hom.toNatIso (X.toPseudofunctor.mapId a)).hom.app
              (CategoricalPullback.fst q) =
          (Cat.Hom.toNatIso (X.toPseudofunctor.mapId a)).hom.app
              (CategoricalPullback.fst p) ≫ k.fst
        exact (Cat.Hom.toNatIso (X.toPseudofunctor.mapId a)).hom.naturality k.fst
      · change (Y.toPseudofunctor.map (𝟙 a)).toFunctor.map k.snd ≫
            (Cat.Hom.toNatIso (Y.toPseudofunctor.mapId a)).hom.app
              (CategoricalPullback.snd q) =
          (Cat.Hom.toNatIso (Y.toPseudofunctor.mapId a)).hom.app
              (CategoricalPullback.snd p) ≫ k.snd
        exact (Cat.Hom.toNatIso (Y.toPseudofunctor.mapId a)).hom.naturality k.snd)

/-- The composition coherence for `fiberTwoPullbackMap`. -/
noncomputable def fiberTwoPullbackMapComp
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor)
    {a b c : LocallyDiscrete Cᵒᵖ} (h : a ⟶ b) (k : b ⟶ c) :
    fiberTwoPullbackMap f g (h ≫ k) ≅
      fiberTwoPullbackMap f g h ⋙ fiberTwoPullbackMap f g k :=
  NatIso.ofComponents (fun p =>
    CategoricalPullback.mkIso
      ((Cat.Hom.toNatIso (X.toPseudofunctor.mapComp h k)).app (CategoricalPullback.fst p))
      ((Cat.Hom.toNatIso (Y.toPseudofunctor.mapComp h k)).app (CategoricalPullback.snd p))
      (by
        dsimp [fiberTwoPullbackMap]
        simp only [Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv]
        rw [Pseudofunctor.StrongTrans.naturality_comp_hom_app,
          Pseudofunctor.StrongTrans.naturality_comp_inv_app]
        simp only [Category.assoc, ← Functor.map_comp]
        rw [← NatTrans.naturality_assoc]
        simp))
    (by
      intro p q l
      apply CategoricalPullback.hom_ext
      · change (X.toPseudofunctor.map (h ≫ k)).toFunctor.map l.fst ≫
              (Cat.Hom.toNatIso (X.toPseudofunctor.mapComp h k)).hom.app
                (CategoricalPullback.fst q) =
            (Cat.Hom.toNatIso (X.toPseudofunctor.mapComp h k)).hom.app
                (CategoricalPullback.fst p) ≫
              ((X.toPseudofunctor.map h).toFunctor ⋙
                (X.toPseudofunctor.map k).toFunctor).map l.fst
        exact (Cat.Hom.toNatIso
          (X.toPseudofunctor.mapComp h k)).hom.naturality l.fst
      · change (Y.toPseudofunctor.map (h ≫ k)).toFunctor.map l.snd ≫
              (Cat.Hom.toNatIso (Y.toPseudofunctor.mapComp h k)).hom.app
                (CategoricalPullback.snd q) =
            (Cat.Hom.toNatIso (Y.toPseudofunctor.mapComp h k)).hom.app
                (CategoricalPullback.snd p) ≫
              ((Y.toPseudofunctor.map h).toFunctor ⋙
                (Y.toPseudofunctor.map k).toFunctor).map l.snd
        exact (Cat.Hom.toNatIso
          (Y.toPseudofunctor.mapComp h k)).hom.naturality l.snd)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- The objectwise genuine two-pullbacks, assembled into a pseudofunctor. -/
noncomputable def fiberTwoPullbackPseudofunctor
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor) :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₁, max u₁ v₁} :=
  LocallyDiscrete.mkPseudofunctor
    (fun a => Cat.of (TwoPullback (f.app ⟨a⟩).toFunctor (g.app ⟨a⟩).toFunctor))
    (fun h => (fiberTwoPullbackMap f g ⟨h⟩).toCatHom)
    (fun a => Cat.Hom.isoMk (fiberTwoPullbackMapId f g ⟨a⟩))
    (fun h k => Cat.Hom.isoMk (fiberTwoPullbackMapComp f g ⟨h⟩ ⟨k⟩))
    (by
      intro b₀ b₁ b₂ b₃ h k l
      apply Cat.Hom₂.ext
      apply CategoricalPullback.natTrans_ext
      · ext p
        change
          (X.toPseudofunctor.mapComp (⟨h⟩ ≫ ⟨k⟩) ⟨l⟩).hom.toNatTrans.app
              (CategoricalPullback.fst p) ≫
              (X.toPseudofunctor.map ⟨l⟩).toFunctor.map
                ((X.toPseudofunctor.mapComp ⟨h⟩ ⟨k⟩).hom.toNatTrans.app
                  (CategoricalPullback.fst p)) ≫
              eqToHom (by simp) ≫
              (X.toPseudofunctor.mapComp ⟨k⟩ ⟨l⟩).inv.toNatTrans.app
                ((X.toPseudofunctor.map ⟨h⟩).toFunctor.obj
                  (CategoricalPullback.fst p)) ≫
              (X.toPseudofunctor.mapComp ⟨h⟩ (⟨k⟩ ≫ ⟨l⟩)).inv.toNatTrans.app
                (CategoricalPullback.fst p) = _
        apply (congrArg
          (fun η => η.toNatTrans.app (CategoricalPullback.fst p))
          (X.toPseudofunctor.map₂_associator ⟨h⟩ ⟨k⟩ ⟨l⟩).symm).trans
        simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom,
          PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans,
          eqToHom_app, Functor.whiskerRight_app, CategoricalPullback.π₁_map,
          CategoricalPullback.eqToHom_fst]
      · ext p
        change
          (Y.toPseudofunctor.mapComp (⟨h⟩ ≫ ⟨k⟩) ⟨l⟩).hom.toNatTrans.app
              (CategoricalPullback.snd p) ≫
              (Y.toPseudofunctor.map ⟨l⟩).toFunctor.map
                ((Y.toPseudofunctor.mapComp ⟨h⟩ ⟨k⟩).hom.toNatTrans.app
                  (CategoricalPullback.snd p)) ≫
              eqToHom (by simp) ≫
              (Y.toPseudofunctor.mapComp ⟨k⟩ ⟨l⟩).inv.toNatTrans.app
                ((Y.toPseudofunctor.map ⟨h⟩).toFunctor.obj
                  (CategoricalPullback.snd p)) ≫
              (Y.toPseudofunctor.mapComp ⟨h⟩ (⟨k⟩ ≫ ⟨l⟩)).inv.toNatTrans.app
                (CategoricalPullback.snd p) = _
        apply (congrArg
          (fun η => η.toNatTrans.app (CategoricalPullback.snd p))
          (Y.toPseudofunctor.map₂_associator ⟨h⟩ ⟨k⟩ ⟨l⟩).symm).trans
        simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom,
          PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans,
          eqToHom_app, Functor.whiskerRight_app, CategoricalPullback.π₂_map,
          CategoricalPullback.eqToHom_snd]
      )
    (by
      intro b₀ b₁ h
      apply Cat.Hom₂.ext
      apply CategoricalPullback.natTrans_ext
      · ext p
        simp only [fiberTwoPullbackMapComp, fiberTwoPullbackMapId,
          Functor.whiskerRight_app, Cat.Hom₂.comp_app,
          Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
          Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
          NatIso.ofComponents_hom_app, CategoricalPullback.mkIso_hom_fst,
          CategoricalPullback.π₁_map, CategoricalPullback.comp_fst,
          CategoricalPullback.eqToHom_fst, Cat.Hom.isoMk,
          NatTrans.toCatHom₂_toNatTrans, Cat.Hom.toNatIso_hom]
        rw [CategoricalPullback.comp_fst, CategoricalPullback.comp_fst]
        simp only [CategoricalPullback.mkIso_hom_fst,
          Cat.Hom.toNatIso_app_hom, fiberTwoPullbackMap_toCatHom_map_fst,
          CategoricalPullback.eqToHom_fst, Category.comp_id]
        rw [GromovWitten.AlgebraicGeometry.CategoricalPullback.eqToHom_fst]
        change
          (X.toPseudofunctor.mapComp (𝟙 _) ⟨h⟩).hom.toNatTrans.app
                (CategoricalPullback.fst p) ≫
              (X.toPseudofunctor.map ⟨h⟩).toFunctor.map
                ((X.toPseudofunctor.mapId ⟨b₀⟩).hom.toNatTrans.app
                  (CategoricalPullback.fst p)) ≫ eqToHom (by simp) = _
        have hx := congrArg
          (fun η => η.toNatTrans.app (CategoricalPullback.fst p))
          (X.toPseudofunctor.map₂_left_unitor ⟨h⟩).symm
        apply hx.trans
        simp only [Bicategory.Strict.leftUnitor_eqToIso, eqToIso.hom,
          PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans,
          eqToHom_app, Functor.whiskerRight_app, CategoricalPullback.π₁_map,
          CategoricalPullback.eqToHom_fst]
      · ext p
        simp only [fiberTwoPullbackMapComp, fiberTwoPullbackMapId,
          Functor.whiskerRight_app, Cat.Hom₂.comp_app,
          Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
          Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
          NatIso.ofComponents_hom_app, CategoricalPullback.π₂_map,
          CategoricalPullback.eqToHom_snd, Cat.Hom.isoMk,
          NatTrans.toCatHom₂_toNatTrans, Cat.Hom.toNatIso_hom]
        rw [CategoricalPullback.comp_snd, CategoricalPullback.comp_snd]
        simp only [CategoricalPullback.mkIso_hom_snd,
          Cat.Hom.toNatIso_app_hom, fiberTwoPullbackMap_toCatHom_map_snd]
        rw [GromovWitten.AlgebraicGeometry.CategoricalPullback.eqToHom_snd]
        change
          (Y.toPseudofunctor.mapComp (𝟙 _) ⟨h⟩).hom.toNatTrans.app
                (CategoricalPullback.snd p) ≫
              (Y.toPseudofunctor.map ⟨h⟩).toFunctor.map
                ((Y.toPseudofunctor.mapId ⟨b₀⟩).hom.toNatTrans.app
                  (CategoricalPullback.snd p)) ≫ eqToHom (by simp) = _
        have hy := congrArg
          (fun η => η.toNatTrans.app (CategoricalPullback.snd p))
          (Y.toPseudofunctor.map₂_left_unitor ⟨h⟩).symm
        apply hy.trans
        simp only [Bicategory.Strict.leftUnitor_eqToIso, eqToIso.hom,
          PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans,
          eqToHom_app, Functor.whiskerRight_app, CategoricalPullback.π₂_map,
          CategoricalPullback.eqToHom_snd]
      )
    (by
      intro b₀ b₁ h
      apply Cat.Hom₂.ext
      apply CategoricalPullback.natTrans_ext
      · ext p
        simp only [fiberTwoPullbackMapComp, fiberTwoPullbackMapId,
          Functor.whiskerRight_app, Cat.Hom₂.comp_app,
          Cat.whiskerLeft_app, Cat.rightUnitor_hom_app,
          Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
          NatIso.ofComponents_hom_app, CategoricalPullback.π₁_map,
          CategoricalPullback.eqToHom_fst, Cat.Hom.isoMk,
          NatTrans.toCatHom₂_toNatTrans, Cat.Hom.toNatIso_hom]
        rw [CategoricalPullback.comp_fst, CategoricalPullback.comp_fst]
        simp only [CategoricalPullback.mkIso_hom_fst,
          Cat.Hom.toNatIso_app_hom, fiberTwoPullbackMap_toCatHom_obj_fst]
        rw [GromovWitten.AlgebraicGeometry.CategoricalPullback.eqToHom_fst]
        change
          (X.toPseudofunctor.mapComp ⟨h⟩ (𝟙 _)).hom.toNatTrans.app
                (CategoricalPullback.fst p) ≫
              (X.toPseudofunctor.mapId ⟨b₁⟩).hom.toNatTrans.app
                ((X.toPseudofunctor.map ⟨h⟩).toFunctor.obj
                  (CategoricalPullback.fst p)) ≫ eqToHom (by simp) = _
        have hx := congrArg
          (fun η => η.toNatTrans.app (CategoricalPullback.fst p))
          (X.toPseudofunctor.map₂_right_unitor ⟨h⟩).symm
        apply hx.trans
        simp only [Bicategory.Strict.rightUnitor_eqToIso, eqToIso.hom,
          PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans,
          eqToHom_app, Functor.whiskerRight_app, CategoricalPullback.π₁_map,
          CategoricalPullback.eqToHom_fst]
      · ext p
        simp only [fiberTwoPullbackMapComp, fiberTwoPullbackMapId,
          Functor.whiskerRight_app, Cat.Hom₂.comp_app,
          Cat.whiskerLeft_app, Cat.rightUnitor_hom_app,
          Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
          NatIso.ofComponents_hom_app, CategoricalPullback.π₂_map,
          CategoricalPullback.eqToHom_snd, Cat.Hom.isoMk,
          NatTrans.toCatHom₂_toNatTrans, Cat.Hom.toNatIso_hom]
        rw [CategoricalPullback.comp_snd, CategoricalPullback.comp_snd]
        simp only [CategoricalPullback.mkIso_hom_snd,
          Cat.Hom.toNatIso_app_hom, fiberTwoPullbackMap_toCatHom_obj_snd]
        rw [GromovWitten.AlgebraicGeometry.CategoricalPullback.eqToHom_snd]
        change
          (Y.toPseudofunctor.mapComp ⟨h⟩ (𝟙 _)).hom.toNatTrans.app
                (CategoricalPullback.snd p) ≫
              (Y.toPseudofunctor.mapId ⟨b₁⟩).hom.toNatTrans.app
                ((Y.toPseudofunctor.map ⟨h⟩).toFunctor.obj
                  (CategoricalPullback.snd p)) ≫ eqToHom (by simp) = _
        have hy := congrArg
          (fun η => η.toNatTrans.app (CategoricalPullback.snd p))
          (Y.toPseudofunctor.map₂_right_unitor ⟨h⟩).symm
        apply hy.trans
        simp only [Bicategory.Strict.rightUnitor_eqToIso, eqToIso.hom,
          PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans,
          eqToHom_app, Functor.whiskerRight_app, CategoricalPullback.π₂_map,
          CategoricalPullback.eqToHom_snd]
      )

/-- The fibrewise two-pullback pseudofunctor is groupoid-valued. -/
noncomputable instance fiberTwoPullbackPseudofunctorIsGroupoidValued
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (g : Pseudofunctor.StrongTrans Y.toPseudofunctor Z.toPseudofunctor) :
    (fiberTwoPullbackPseudofunctor f g).IsGroupoidValued where
  fiber U := by
    change IsGroupoid
      (TwoPullback (f.app ⟨Opposite.op U⟩).toFunctor
        (g.app ⟨Opposite.op U⟩).toFunctor)
    infer_instance

end StackInGroupoids

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- The first projection from the fibrewise two-pullback pseudofunctor on the big fppf site.
Its naturality cell is the identity because `fiberTwoPullbackMap` was defined componentwise
using reindexing in the first stack. -/
noncomputable def fiberTwoPullbackFst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z) :
    Pseudofunctor.StrongTrans
      (StackInGroupoids.fiberTwoPullbackPseudofunctor f g)
      X.toPseudofunctor where
  app a := (TwoPullback.fst (f.app a).toFunctor (g.app a).toFunctor).toCatHom
  naturality _ := Cat.Hom.isoMk (Iso.refl _)
  naturality_naturality {a b h k} η := by
    have e : h = k := LocallyDiscrete.eq_of_hom η
    subst k
    rw [Subsingleton.elim η (𝟙 h)]
    cat_disch
  naturality_id a := by
    apply Cat.Hom₂.ext
    ext p
    dsimp only [StackInGroupoids.fiberTwoPullbackPseudofunctor]
    simp only [LocallyDiscrete.mkPseudofunctor_mapId]
    simp only [Cat.Hom₂.comp_app,
      Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app]
    simp only [Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans]
    simp only [StackInGroupoids.fiberTwoPullbackMapId,
      NatIso.ofComponents_hom_app,
      CategoricalPullback.mkIso_hom_fst,
      Cat.Hom.toNatIso_app_hom, CategoricalPullback.π₁_map,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id]
    simp
  naturality_comp h k := by
    apply Cat.Hom₂.ext
    ext p
    dsimp only [StackInGroupoids.fiberTwoPullbackPseudofunctor]
    simp only [LocallyDiscrete.mkPseudofunctor_mapComp]
    simp only [Cat.Hom₂.comp_app,
      Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_app, Cat.associator_inv_app]
    simp only [Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans]
    simp only [StackInGroupoids.fiberTwoPullbackMapComp,
      NatIso.ofComponents_hom_app,
      CategoricalPullback.mkIso_hom_fst,
      Cat.Hom.toNatIso_app_hom, CategoricalPullback.π₁_map,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.map_id, Category.id_comp, Category.comp_id]
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- The second projection from the fibrewise two-pullback pseudofunctor on the big fppf site. -/
noncomputable def fiberTwoPullbackSnd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z) :
    Pseudofunctor.StrongTrans
      (StackInGroupoids.fiberTwoPullbackPseudofunctor f g)
      Y.toPseudofunctor where
  app a := (TwoPullback.snd (f.app a).toFunctor (g.app a).toFunctor).toCatHom
  naturality _ := Cat.Hom.isoMk (Iso.refl _)
  naturality_naturality {a b h k} η := by
    have e : h = k := LocallyDiscrete.eq_of_hom η
    subst k
    rw [Subsingleton.elim η (𝟙 h)]
    cat_disch
  naturality_id a := by
    apply Cat.Hom₂.ext
    ext p
    dsimp only [StackInGroupoids.fiberTwoPullbackPseudofunctor]
    simp only [LocallyDiscrete.mkPseudofunctor_mapId]
    simp only [Cat.Hom₂.comp_app,
      Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app]
    simp only [Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans]
    simp only [StackInGroupoids.fiberTwoPullbackMapId,
      NatIso.ofComponents_hom_app,
      CategoricalPullback.mkIso_hom_snd,
      Cat.Hom.toNatIso_app_hom, CategoricalPullback.π₂_map,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id]
    simp
  naturality_comp h k := by
    apply Cat.Hom₂.ext
    ext p
    dsimp only [StackInGroupoids.fiberTwoPullbackPseudofunctor]
    simp only [LocallyDiscrete.mkPseudofunctor_mapComp]
    simp only [Cat.Hom₂.comp_app,
      Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_app, Cat.associator_inv_app]
    simp only [Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans]
    simp only [StackInGroupoids.fiberTwoPullbackMapComp,
      NatIso.ofComponents_hom_app,
      CategoricalPullback.mkIso_hom_snd,
      Cat.Hom.toNatIso_app_hom, CategoricalPullback.π₂_map,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.map_id, Category.id_comp, Category.comp_id]
    simp

/-- Descent data in the fibrewise two-pullback, projected functorially to descent data in the
first stack.  All pseudofunctorial coherence is supplied by `StrongTrans.mapDescentDataFunctor`. -/
noncomputable def fiberTwoPullbackDescentFst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    Functor
      ((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover)
      (X.toPseudofunctor.DescentData cover) :=
  (fiberTwoPullbackFst f g).mapDescentDataFunctor cover

/-- Descent data in the fibrewise two-pullback, projected functorially to descent data in the
second stack. -/
noncomputable def fiberTwoPullbackDescentSnd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    Functor
      ((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover)
      (Y.toPseudofunctor.DescentData cover) :=
  (fiberTwoPullbackSnd f g).mapDescentDataFunctor cover

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The objectwise canonical comparison between the two composites from the fibrewise
two-pullback to the target stack. Its component at `(x, y, α)` is exactly `α`. -/
noncomputable def fiberTwoPullbackComparisonApp
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z) :
    ∀ a, (Pseudofunctor.StrongTrans.vcomp (fiberTwoPullbackFst f g) f).app a ≅
      (Pseudofunctor.StrongTrans.vcomp (fiberTwoPullbackSnd f g) g).app a :=
  fun a ↦ Cat.Hom.isoMk
      (CatCommSq.iso
        (TwoPullback.fst (f.app a).toFunctor (g.app a).toFunctor)
        (TwoPullback.snd (f.app a).toFunctor (g.app a).toFunctor)
        (f.app a).toFunctor (g.app a).toFunctor)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- The forward canonical comparison modification. -/
noncomputable def fiberTwoPullbackComparisonHom
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z) :
    Pseudofunctor.StrongTrans.Modification
      (Pseudofunctor.StrongTrans.vcomp (fiberTwoPullbackFst f g) f)
      (Pseudofunctor.StrongTrans.vcomp (fiberTwoPullbackSnd f g) g) where
  app a := (fiberTwoPullbackComparisonApp f g a).hom
  naturality {a b} h := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext p
    simp [fiberTwoPullbackComparisonApp, fiberTwoPullbackFst,
      fiberTwoPullbackSnd, StackInGroupoids.fiberTwoPullbackPseudofunctor,
      StackInGroupoids.fiberTwoPullbackMap,
      Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
      Oplax.StrongTrans.vcomp, Oplax.StrongTrans.mkOfOplax,
      Oplax.OplaxTrans.vcomp]

@[simp]
theorem fiberTwoPullbackComparisonHom_app
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z) (a) :
    (fiberTwoPullbackComparisonHom f g).app a =
      (fiberTwoPullbackComparisonApp f g a).hom := rfl

/-- The inverse canonical comparison modification. Its naturality follows from the forward
comparison by cancellation with the objectwise isomorphisms. -/
noncomputable def fiberTwoPullbackComparisonInv
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z) :
    Pseudofunctor.StrongTrans.Modification
      (Pseudofunctor.StrongTrans.vcomp (fiberTwoPullbackSnd f g) g)
      (Pseudofunctor.StrongTrans.vcomp (fiberTwoPullbackFst f g) f) where
  app a := (fiberTwoPullbackComparisonApp f g a).inv
  naturality {a b} h := by
    simpa [fiberTwoPullbackComparisonHom_app] using
      _ ◁ (fiberTwoPullbackComparisonApp f g b).inv ≫=
        ((fiberTwoPullbackComparisonHom f g).naturality h).symm =≫
          (fiberTwoPullbackComparisonApp f g a).inv ▷ _

/-- The forward and inverse comparison modifications compose to the identity. -/
theorem fiberTwoPullbackComparison_hom_inv_id
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z) :
    Pseudofunctor.StrongTrans.Modification.vcomp
        (fiberTwoPullbackComparisonHom f g)
        (fiberTwoPullbackComparisonInv f g) =
      Pseudofunctor.StrongTrans.Modification.id
        (Pseudofunctor.StrongTrans.vcomp (fiberTwoPullbackFst f g) f) := by
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext a
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  change p.iso.hom ≫ p.iso.inv = 𝟙 _
  simp

/-- The inverse and forward comparison modifications compose to the identity. -/
theorem fiberTwoPullbackComparison_inv_hom_id
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z) :
    Pseudofunctor.StrongTrans.Modification.vcomp
        (fiberTwoPullbackComparisonInv f g)
        (fiberTwoPullbackComparisonHom f g) =
      Pseudofunctor.StrongTrans.Modification.id
        (Pseudofunctor.StrongTrans.vcomp (fiberTwoPullbackSnd f g) g) := by
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext a
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  change p.iso.inv ≫ p.iso.hom = 𝟙 _
  simp

/-- The canonical comparison also descends: applying the two composite legs to any descent datum
for the fibrewise pullback gives canonically isomorphic descent data in the target stack. -/
noncomputable def fiberTwoPullbackCompositeDescentComparison
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    (Pseudofunctor.StrongTrans.vcomp
        (fiberTwoPullbackFst f g) f).mapDescentDataFunctor cover ≅
      (Pseudofunctor.StrongTrans.vcomp
        (fiberTwoPullbackSnd f g) g).mapDescentDataFunctor cover where
  hom := (fiberTwoPullbackComparisonHom f g).mapDescentDataNatTrans cover
  inv := (fiberTwoPullbackComparisonInv f g).mapDescentDataNatTrans cover
  hom_inv_id := by
    rw [← Pseudofunctor.StrongTrans.Modification.mapDescentDataNatTrans_vcomp,
      fiberTwoPullbackComparison_hom_inv_id,
      Pseudofunctor.StrongTrans.Modification.mapDescentDataNatTrans_id]
  inv_hom_id := by
    rw [← Pseudofunctor.StrongTrans.Modification.mapDescentDataNatTrans_vcomp,
      fiberTwoPullbackComparison_inv_hom_id,
      Pseudofunctor.StrongTrans.Modification.mapDescentDataNatTrans_id]

/-- The comparison isomorphism carried by a descent datum in the fibrewise two-pullback,
expressed between the descent data obtained by first projecting and then applying the two
legs.  The two `mapDescentDataVcompIso` factors record the required non-strict coherence
between successive transport and transport along a composite. -/
noncomputable def fiberTwoPullbackDescentComparisonViaComposite
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    fiberTwoPullbackDescentFst f g cover ⋙ f.mapDescentDataFunctor cover ≅
      fiberTwoPullbackDescentSnd f g cover ⋙ g.mapDescentDataFunctor cover :=
  (Pseudofunctor.StrongTrans.mapDescentDataVcompIso
      (fiberTwoPullbackFst f g) f cover).symm ≪≫
    fiberTwoPullbackCompositeDescentComparison f g cover ≪≫
    Pseudofunctor.StrongTrans.mapDescentDataVcompIso
      (fiberTwoPullbackSnd f g) g cover

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- The descent comparison read directly from the isomorphism in each local two-pullback
object.  Its compatibility is forced by the commutative square in each overlap morphism.
Thus the comparison contains no separately supplied descent or coherence witness. -/
noncomputable def fiberTwoPullbackDescentComparison
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    fiberTwoPullbackDescentFst f g cover ⋙ f.mapDescentDataFunctor cover ≅
      fiberTwoPullbackDescentSnd f g cover ⋙ g.mapDescentDataFunctor cover := by
  fapply NatIso.ofComponents
  · intro D
    refine Pseudofunctor.DescentData.isoMk (fun i ↦ (D.obj i).iso) ?_
    intro T q i₁ i₂ h₁ h₂ hh₁ hh₂
    have h := (D.hom q h₁ h₂ hh₁ hh₂).w
    dsimp [fiberTwoPullbackDescentFst, fiberTwoPullbackDescentSnd,
      Pseudofunctor.StrongTrans.mapDescentDataFunctor,
      Pseudofunctor.StrongTrans.mapDescentData,
      fiberTwoPullbackFst, fiberTwoPullbackSnd,
      StackInGroupoids.fiberTwoPullbackPseudofunctor,
      StackInGroupoids.fiberTwoPullbackMap] at h ⊢
    simpa [Quiver.Hom.toLoc, Category.assoc] using (congrArg
      (fun k ↦
        (f.naturality h₁.op.toLoc).inv.toNatTrans.app
            (CategoricalPullback.fst (D.obj i₁)) ≫
          k ≫
        (g.naturality h₂.op.toLoc).hom.toNatTrans.app
            (CategoricalPullback.snd (D.obj i₂))) h).symm
  · intro D₁ D₂ phi
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact (phi.hom i).w

@[simp]
theorem fiberTwoPullbackDescentComparison_hom_hom
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover)
    (i : ι) :
    ((fiberTwoPullbackDescentComparison f g cover).app D).hom.hom i =
      (D.obj i).iso.hom := rfl

/-- The target-stack descent comparison attached to one fibre-product descent datum. -/
noncomputable def fiberTwoPullbackDescentComparisonObj
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover) :
    (f.mapDescentDataFunctor cover).obj
        ((fiberTwoPullbackDescentFst f g cover).obj D) ≅
      (g.mapDescentDataFunctor cover).obj
        ((fiberTwoPullbackDescentSnd f g cover).obj D) :=
  (fiberTwoPullbackDescentComparison f g cover).app D

/-- A descent datum in the fibrewise two-pullback determines a genuine categorical
two-pullback of descent data: its two projections and the descended comparison isomorphism.
The comparison is retained as data and is not replaced by an equality. -/
noncomputable def fiberTwoPullbackDescentToPullback
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover ⥤
      TwoPullback (f.mapDescentDataFunctor cover) (g.mapDescentDataFunctor cover) where
  obj D :=
    { fst := (fiberTwoPullbackDescentFst f g cover).obj D
      snd := (fiberTwoPullbackDescentSnd f g cover).obj D
      iso := fiberTwoPullbackDescentComparisonObj f g cover D }
  map {D₁ D₂} phi :=
    { fst := (fiberTwoPullbackDescentFst f g cover).map phi
      snd := (fiberTwoPullbackDescentSnd f g cover).map phi
      w := (fiberTwoPullbackDescentComparison f g cover).hom.naturality phi }
  map_id D := by
    apply CategoricalPullback.hom_ext <;> simp
  map_comp phi psi := by
    apply CategoricalPullback.hom_ext <;> simp

@[simp]
theorem fiberTwoPullbackDescentToPullback_obj_fst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover) :
    CategoricalPullback.fst ((fiberTwoPullbackDescentToPullback f g cover).obj D) =
      (fiberTwoPullbackDescentFst f g cover).obj D := rfl

@[simp]
theorem fiberTwoPullbackDescentToPullback_obj_snd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover) :
    CategoricalPullback.snd ((fiberTwoPullbackDescentToPullback f g cover).obj D) =
      (fiberTwoPullbackDescentSnd f g cover).obj D := rfl

private theorem fiberTwoPullbackMapComp_hom_fst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {a b c : LocallyDiscrete Scheme.{u₁}ᵒᵖ} (h : a ⟶ b) (k : b ⟶ c)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp h k).hom.toNatTrans.app p).fst =
      (X.toPseudofunctor.mapComp h k).hom.toNatTrans.app
        (CategoricalPullback.fst p) := rfl

private theorem fiberTwoPullbackMapComp_inv_fst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {a b c : LocallyDiscrete Scheme.{u₁}ᵒᵖ} (h : a ⟶ b) (k : b ⟶ c)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp h k).inv.toNatTrans.app p).fst =
      (X.toPseudofunctor.mapComp h k).inv.toNatTrans.app
        (CategoricalPullback.fst p) := rfl

private theorem fiberTwoPullbackMapComp_hom_snd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {a b c : LocallyDiscrete Scheme.{u₁}ᵒᵖ} (h : a ⟶ b) (k : b ⟶ c)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp h k).hom.toNatTrans.app p).snd =
      (Y.toPseudofunctor.mapComp h k).hom.toNatTrans.app
        (CategoricalPullback.snd p) := rfl

private theorem fiberTwoPullbackMapComp_inv_snd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {a b c : LocallyDiscrete Scheme.{u₁}ᵒᵖ} (h : a ⟶ b) (k : b ⟶ c)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp h k).inv.toNatTrans.app p).snd =
      (Y.toPseudofunctor.mapComp h k).inv.toNatTrans.app
        (CategoricalPullback.snd p) := rfl

private theorem fiberTwoPullbackMapComp'_hom_fst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {a b c : LocallyDiscrete Scheme.{u₁}ᵒᵖ} (h : a ⟶ b) (k : b ⟶ c)
    (hk : a ⟶ c) (e : h ≫ k = hk)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp'
      h k hk e).hom.toNatTrans.app p).fst =
      (X.toPseudofunctor.mapComp' h k hk e).hom.toNatTrans.app
        (CategoricalPullback.fst p) := by
  subst hk
  rw [(StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp'_eq_mapComp,
    X.toPseudofunctor.mapComp'_eq_mapComp]
  exact fiberTwoPullbackMapComp_hom_fst f g h k p

private theorem fiberTwoPullbackMapComp'_inv_fst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {a b c : LocallyDiscrete Scheme.{u₁}ᵒᵖ} (h : a ⟶ b) (k : b ⟶ c)
    (hk : a ⟶ c) (e : h ≫ k = hk)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp'
      h k hk e).inv.toNatTrans.app p).fst =
      (X.toPseudofunctor.mapComp' h k hk e).inv.toNatTrans.app
        (CategoricalPullback.fst p) := by
  subst hk
  rw [(StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp'_eq_mapComp,
    X.toPseudofunctor.mapComp'_eq_mapComp]
  exact fiberTwoPullbackMapComp_inv_fst f g h k p

private theorem fiberTwoPullbackMapComp'_hom_snd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {a b c : LocallyDiscrete Scheme.{u₁}ᵒᵖ} (h : a ⟶ b) (k : b ⟶ c)
    (hk : a ⟶ c) (e : h ≫ k = hk)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp'
      h k hk e).hom.toNatTrans.app p).snd =
      (Y.toPseudofunctor.mapComp' h k hk e).hom.toNatTrans.app
        (CategoricalPullback.snd p) := by
  subst hk
  rw [(StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp'_eq_mapComp,
    Y.toPseudofunctor.mapComp'_eq_mapComp]
  exact fiberTwoPullbackMapComp_hom_snd f g h k p

private theorem fiberTwoPullbackMapComp'_inv_snd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {a b c : LocallyDiscrete Scheme.{u₁}ᵒᵖ} (h : a ⟶ b) (k : b ⟶ c)
    (hk : a ⟶ c) (e : h ≫ k = hk)
    (p : TwoPullback (f.app a).toFunctor (g.app a).toFunctor) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp'
      h k hk e).inv.toNatTrans.app p).snd =
      (Y.toPseudofunctor.mapComp' h k hk e).inv.toNatTrans.app
        (CategoricalPullback.snd p) := by
  subst hk
  rw [(StackInGroupoids.fiberTwoPullbackPseudofunctor f g).mapComp'_eq_mapComp,
    Y.toPseudofunctor.mapComp'_eq_mapComp]
  exact fiberTwoPullbackMapComp_inv_snd f g h k p

private theorem fiberTwoPullbackPseudofunctor_map_fst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {a b : LocallyDiscrete Scheme.{u₁}ᵒᵖ} (h : a ⟶ b)
    {p q : TwoPullback (f.app a).toFunctor (g.app a).toFunctor} (l : p ⟶ q) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).map h).toFunctor.map l).fst =
      (X.toPseudofunctor.map h).toFunctor.map l.fst := rfl

private theorem fiberTwoPullbackPseudofunctor_map_snd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {a b : LocallyDiscrete Scheme.{u₁}ᵒᵖ} (h : a ⟶ b)
    {p q : TwoPullback (f.app a).toFunctor (g.app a).toFunctor} (l : p ⟶ q) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).map h).toFunctor.map l).snd =
      (Y.toPseudofunctor.map h).toFunctor.map l.snd := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- Reconstruct fibre-product descent data from its two projected descent data and their
specified comparison isomorphism.  Every local object and overlap arrow is obtained
componentwise from that categorical-pullback object. -/
noncomputable def fiberTwoPullbackDescentOfPullbackObj
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (Q : TwoPullback (f.mapDescentDataFunctor cover)
      (g.mapDescentDataFunctor cover)) :
    (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover where
  obj i :=
    { fst := (CategoricalPullback.fst Q).obj i
      snd := (CategoricalPullback.snd Q).obj i
      iso :=
        { hom := Q.iso.hom.hom i
          inv := Q.iso.inv.hom i
          hom_inv_id := congrArg (fun k ↦ k.hom i) Q.iso.hom_inv_id
          inv_hom_id := congrArg (fun k ↦ k.hom i) Q.iso.inv_hom_id } }
  hom T q i₁ i₂ h₁ h₂ hh₁ hh₂ :=
    { fst := (CategoricalPullback.fst Q).hom q h₁ h₂ hh₁ hh₂
      snd := (CategoricalPullback.snd Q).hom q h₁ h₂ hh₁ hh₂
      w := by
        have h := Q.iso.hom.comm q h₁ h₂ hh₁ hh₂
        dsimp [Pseudofunctor.StrongTrans.mapDescentDataFunctor,
          Pseudofunctor.StrongTrans.mapDescentData] at h
        dsimp [StackInGroupoids.fiberTwoPullbackPseudofunctor,
          StackInGroupoids.fiberTwoPullbackMap]
        simpa [Quiver.Hom.toLoc] using (congrArg
            (fun k ↦
              (f.naturality h₁.op.toLoc).hom.toNatTrans.app
                  ((CategoricalPullback.fst Q).obj i₁) ≫
                k ≫
              (g.naturality h₂.op.toLoc).inv.toNatTrans.app
                  ((CategoricalPullback.snd Q).obj i₂)) h).symm }
  pullHom_hom T' T h q q' hq i₁ i₂ h₁ h₂ hh₁ hh₂ hh₁' hh₂' hhh₁ hhh₂ := by
    subst hh₁'
    subst hh₂'
    apply CategoricalPullback.hom_ext
    · dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
      rw [CategoricalPullback.comp_fst, CategoricalPullback.comp_fst]
      simp only [fiberTwoPullbackMapComp'_hom_fst,
        fiberTwoPullbackMapComp'_inv_fst, fiberTwoPullbackPseudofunctor_map_fst]
      exact (CategoricalPullback.fst Q).pullHom_hom h q q' hq h₁ h₂ hh₁ hh₂
        (h ≫ h₁) (h ≫ h₂) rfl rfl
    · dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
      rw [CategoricalPullback.comp_snd, CategoricalPullback.comp_snd]
      simp only [fiberTwoPullbackMapComp'_hom_snd,
        fiberTwoPullbackMapComp'_inv_snd, fiberTwoPullbackPseudofunctor_map_snd]
      exact (CategoricalPullback.snd Q).pullHom_hom h q q' hq h₁ h₂ hh₁ hh₂
        (h ≫ h₁) (h ≫ h₂) rfl rfl
  hom_self T q i h hh := by
    apply CategoricalPullback.hom_ext
    · exact (CategoricalPullback.fst Q).hom_self q h hh
    · exact (CategoricalPullback.snd Q).hom_self q h hh
  hom_comp T q i₁ i₂ i₃ h₁ h₂ h₃ hh₁ hh₂ hh₃ := by
    apply CategoricalPullback.hom_ext
    · exact (CategoricalPullback.fst Q).hom_comp q h₁ h₂ h₃ hh₁ hh₂ hh₃
    · exact (CategoricalPullback.snd Q).hom_comp q h₁ h₂ h₃ hh₁ hh₂ hh₃

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
private noncomputable def fiberTwoPullbackDescentOfPullbackMap
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    {Q R : TwoPullback (f.mapDescentDataFunctor cover)
      (g.mapDescentDataFunctor cover)} (phi : Q ⟶ R) :
    fiberTwoPullbackDescentOfPullbackObj f g cover Q ⟶
      fiberTwoPullbackDescentOfPullbackObj f g cover R where
  hom i :=
    { fst := phi.fst.hom i
      snd := phi.snd.hom i
      w := by
        have h := congrArg (fun k ↦ k.hom i) phi.w
        change
          (f.app (.mk (Opposite.op (U i)))).toFunctor.map (phi.fst.hom i) ≫
              R.iso.hom.hom i =
            Q.iso.hom.hom i ≫
              (g.app (.mk (Opposite.op (U i)))).toFunctor.map (phi.snd.hom i)
        simpa [Pseudofunctor.StrongTrans.mapDescentDataFunctor,
          Pseudofunctor.StrongTrans.mapDescentData] using h }
  comm T q i₁ i₂ h₁ h₂ hh₁ hh₂ := by
    apply CategoricalPullback.hom_ext
    · simp only [fiberTwoPullbackPseudofunctor_map_fst,
        CategoricalPullback.comp_fst]
      exact phi.fst.comm q h₁ h₂ hh₁ hh₂
    · simp only [fiberTwoPullbackPseudofunctor_map_snd,
        CategoricalPullback.comp_snd]
      exact phi.snd.comm q h₁ h₂ hh₁ hh₂

/-- The inverse descent functor: a genuine two-pullback of component descent categories
reconstructs descent data in the fibrewise two-pullback. -/
noncomputable def fiberTwoPullbackDescentOfPullback
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    TwoPullback (f.mapDescentDataFunctor cover)
        (g.mapDescentDataFunctor cover) ⥤
      (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover where
  obj := fiberTwoPullbackDescentOfPullbackObj f g cover
  map := fiberTwoPullbackDescentOfPullbackMap f g cover
  map_id Q := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    apply CategoricalPullback.hom_ext <;> rfl
  map_comp phi psi := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    apply CategoricalPullback.hom_ext <;> rfl

@[simp]
theorem fiberTwoPullbackDescentFst_obj_hom
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover)
    {T : Scheme.{u₁}} (q : T ⟶ S) {i₁ i₂ : ι} (h₁ : T ⟶ U i₁) (h₂ : T ⟶ U i₂)
    (hh₁ : h₁ ≫ cover i₁ = q) (hh₂ : h₂ ≫ cover i₂ = q) :
    ((fiberTwoPullbackDescentFst f g cover).obj D).hom q h₁ h₂ hh₁ hh₂ =
      (D.hom q h₁ h₂ hh₁ hh₂).fst := by
  change 𝟙 _ ≫ (D.hom q h₁ h₂ hh₁ hh₂).fst ≫ 𝟙 _ = _
  simp

@[simp]
theorem fiberTwoPullbackDescentSnd_obj_hom
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover)
    {T : Scheme.{u₁}} (q : T ⟶ S) {i₁ i₂ : ι} (h₁ : T ⟶ U i₁) (h₂ : T ⟶ U i₂)
    (hh₁ : h₁ ≫ cover i₁ = q) (hh₂ : h₂ ≫ cover i₂ = q) :
    ((fiberTwoPullbackDescentSnd f g cover).obj D).hom q h₁ h₂ hh₁ hh₂ =
      (D.hom q h₁ h₂ hh₁ hh₂).snd := by
  change 𝟙 _ ≫ (D.hom q h₁ h₂ hh₁ hh₂).snd ≫ 𝟙 _ = _
  simp

private theorem fiberTwoPullbackDescent_roundTrip_hom_fst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover)
    {T : Scheme.{u₁}} (q : T ⟶ S) {i₁ i₂ : ι} (h₁ : T ⟶ U i₁) (h₂ : T ⟶ U i₂)
    (hh₁ : h₁ ≫ cover i₁ = q) (hh₂ : h₂ ≫ cover i₂ = q) :
    (((fiberTwoPullbackDescentOfPullback f g cover).obj
      ((fiberTwoPullbackDescentToPullback f g cover).obj D)).hom
        q h₁ h₂ hh₁ hh₂).fst =
      (D.hom q h₁ h₂ hh₁ hh₂).fst :=
  fiberTwoPullbackDescentFst_obj_hom f g cover D q h₁ h₂ hh₁ hh₂

private theorem fiberTwoPullbackDescent_roundTrip_hom_snd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover)
    {T : Scheme.{u₁}} (q : T ⟶ S) {i₁ i₂ : ι} (h₁ : T ⟶ U i₁) (h₂ : T ⟶ U i₂)
    (hh₁ : h₁ ≫ cover i₁ = q) (hh₂ : h₂ ≫ cover i₂ = q) :
    (((fiberTwoPullbackDescentOfPullback f g cover).obj
      ((fiberTwoPullbackDescentToPullback f g cover).obj D)).hom
        q h₁ h₂ hh₁ hh₂).snd =
      (D.hom q h₁ h₂ hh₁ hh₂).snd :=
  fiberTwoPullbackDescentSnd_obj_hom f g cover D q h₁ h₂ hh₁ hh₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
private noncomputable def fiberTwoPullbackDescentUnitIsoApp
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover) :
    D ≅ (fiberTwoPullbackDescentOfPullback f g cover).obj
      ((fiberTwoPullbackDescentToPullback f g cover).obj D) :=
  Pseudofunctor.DescentData.isoMk
    (fun i ↦ CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
      dsimp [fiberTwoPullbackDescentOfPullback,
        fiberTwoPullbackDescentOfPullbackObj,
        fiberTwoPullbackDescentToPullback,
        fiberTwoPullbackDescentComparisonObj,
        fiberTwoPullbackDescentComparison,
        fiberTwoPullbackDescentFst, fiberTwoPullbackDescentSnd,
        Pseudofunctor.StrongTrans.mapDescentDataFunctor,
        Pseudofunctor.StrongTrans.mapDescentData,
        fiberTwoPullbackFst, fiberTwoPullbackSnd]
      simp))
    (by
      intro T q i₁ i₂ h₁ h₂ hh₁ hh₂
      apply CategoricalPullback.hom_ext
      · rw [CategoricalPullback.comp_fst, CategoricalPullback.comp_fst]
        simp only [fiberTwoPullbackPseudofunctor_map_fst,
          CategoricalPullback.mkIso_hom_fst]
        rw [fiberTwoPullbackDescent_roundTrip_hom_fst]
        exact (by
          let m := (D.hom q h₁ h₂ hh₁ hh₂).fst
          calc
            (X.toPseudofunctor.map h₁.op.toLoc).toFunctor.map
                  (𝟙 (CategoricalPullback.fst (D.obj i₁))) ≫ m =
                𝟙 _ ≫ m := congrArg (fun k ↦ k ≫ m)
                  ((X.toPseudofunctor.map h₁.op.toLoc).toFunctor.map_id _)
            _ = m := Category.id_comp m
            _ = m ≫ 𝟙 _ := (Category.comp_id m).symm
            _ = m ≫ (X.toPseudofunctor.map h₂.op.toLoc).toFunctor.map
                  (𝟙 (CategoricalPullback.fst (D.obj i₂))) :=
              congrArg (fun k ↦ m ≫ k)
                ((X.toPseudofunctor.map h₂.op.toLoc).toFunctor.map_id _).symm)
      · rw [CategoricalPullback.comp_snd, CategoricalPullback.comp_snd]
        simp only [fiberTwoPullbackPseudofunctor_map_snd,
          CategoricalPullback.mkIso_hom_snd]
        rw [fiberTwoPullbackDescent_roundTrip_hom_snd]
        exact (by
          let m := (D.hom q h₁ h₂ hh₁ hh₂).snd
          calc
            (Y.toPseudofunctor.map h₁.op.toLoc).toFunctor.map
                  (𝟙 (CategoricalPullback.snd (D.obj i₁))) ≫ m =
                𝟙 _ ≫ m := congrArg (fun k ↦ k ≫ m)
                  ((Y.toPseudofunctor.map h₁.op.toLoc).toFunctor.map_id _)
            _ = m := Category.id_comp m
            _ = m ≫ 𝟙 _ := (Category.comp_id m).symm
            _ = m ≫ (Y.toPseudofunctor.map h₂.op.toLoc).toFunctor.map
                  (𝟙 (CategoricalPullback.snd (D.obj i₂))) :=
              congrArg (fun k ↦ m ≫ k)
                ((Y.toPseudofunctor.map h₂.op.toLoc).toFunctor.map_id _).symm))

private theorem fiberTwoPullbackDescentUnitIsoApp_hom_fst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover)
    (i : ι) :
    ((fiberTwoPullbackDescentUnitIsoApp f g cover D).hom.hom i).fst = 𝟙 _ := rfl

private theorem fiberTwoPullbackDescentUnitIsoApp_hom_snd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (D : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover)
    (i : ι) :
    ((fiberTwoPullbackDescentUnitIsoApp f g cover D).hom.hom i).snd = 𝟙 _ := rfl

private theorem fiberTwoPullbackDescent_roundTrip_map_fst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    {D₁ D₂ : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover}
    (phi : D₁ ⟶ D₂) (i : ι) :
    (((fiberTwoPullbackDescentOfPullback f g cover).map
      ((fiberTwoPullbackDescentToPullback f g cover).map phi)).hom i).fst =
      (phi.hom i).fst := rfl

private theorem fiberTwoPullbackDescent_roundTrip_map_snd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    {D₁ D₂ : (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover}
    (phi : D₁ ⟶ D₂) (i : ι) :
    (((fiberTwoPullbackDescentOfPullback f g cover).map
      ((fiberTwoPullbackDescentToPullback f g cover).map phi)).hom i).snd =
      (phi.hom i).snd := rfl

private noncomputable def fiberTwoPullbackDescentUnitIso
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    𝟭 ((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover) ≅
      fiberTwoPullbackDescentToPullback f g cover ⋙
        fiberTwoPullbackDescentOfPullback f g cover :=
  NatIso.ofComponents (fiberTwoPullbackDescentUnitIsoApp f g cover) (by
    intro D₁ D₂ phi
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    apply CategoricalPullback.hom_ext
    · change (phi.hom i).fst ≫ 𝟙 _ = 𝟙 _ ≫ (phi.hom i).fst
      simp
    · change (phi.hom i).snd ≫ 𝟙 _ = 𝟙 _ ≫ (phi.hom i).snd
      simp)

private theorem fiberTwoPullbackDescentOfPullback_obj_hom_fst
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (Q : TwoPullback (f.mapDescentDataFunctor cover)
      (g.mapDescentDataFunctor cover))
    {T : Scheme.{u₁}} (q : T ⟶ S) {i₁ i₂ : ι} (h₁ : T ⟶ U i₁) (h₂ : T ⟶ U i₂)
    (hh₁ : h₁ ≫ cover i₁ = q) (hh₂ : h₂ ≫ cover i₂ = q) :
    (((fiberTwoPullbackDescentOfPullback f g cover).obj Q).hom
      q h₁ h₂ hh₁ hh₂).fst =
      (CategoricalPullback.fst Q).hom q h₁ h₂ hh₁ hh₂ := rfl

private theorem fiberTwoPullbackDescentOfPullback_obj_hom_snd
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (Q : TwoPullback (f.mapDescentDataFunctor cover)
      (g.mapDescentDataFunctor cover))
    {T : Scheme.{u₁}} (q : T ⟶ S) {i₁ i₂ : ι} (h₁ : T ⟶ U i₁) (h₂ : T ⟶ U i₂)
    (hh₁ : h₁ ≫ cover i₁ = q) (hh₂ : h₂ ≫ cover i₂ = q) :
    (((fiberTwoPullbackDescentOfPullback f g cover).obj Q).hom
      q h₁ h₂ hh₁ hh₂).snd =
      (CategoricalPullback.snd Q).hom q h₁ h₂ hh₁ hh₂ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def fiberTwoPullbackDescentCounitFstIso
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (Q : TwoPullback (f.mapDescentDataFunctor cover)
      (g.mapDescentDataFunctor cover)) :
    (fiberTwoPullbackDescentFst f g cover).obj
        ((fiberTwoPullbackDescentOfPullback f g cover).obj Q) ≅
      CategoricalPullback.fst Q :=
  Pseudofunctor.DescentData.isoMk (fun _ ↦ Iso.refl _) (by
    intro T q i₁ i₂ h₁ h₂ hh₁ hh₂
    rw [fiberTwoPullbackDescentFst_obj_hom,
      fiberTwoPullbackDescentOfPullback_obj_hom_fst]
    let m := (CategoricalPullback.fst Q).hom q h₁ h₂ hh₁ hh₂
    exact (by
      calc
        (X.toPseudofunctor.map h₁.op.toLoc).toFunctor.map
              (𝟙 ((CategoricalPullback.fst Q).obj i₁)) ≫ m =
            𝟙 _ ≫ m := congrArg (fun k ↦ k ≫ m)
              ((X.toPseudofunctor.map h₁.op.toLoc).toFunctor.map_id _)
        _ = m := Category.id_comp m
        _ = m ≫ 𝟙 _ := (Category.comp_id m).symm
        _ = m ≫ (X.toPseudofunctor.map h₂.op.toLoc).toFunctor.map
              (𝟙 ((CategoricalPullback.fst Q).obj i₂)) :=
          congrArg (fun k ↦ m ≫ k)
            ((X.toPseudofunctor.map h₂.op.toLoc).toFunctor.map_id _).symm))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def fiberTwoPullbackDescentCounitSndIso
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (Q : TwoPullback (f.mapDescentDataFunctor cover)
      (g.mapDescentDataFunctor cover)) :
    (fiberTwoPullbackDescentSnd f g cover).obj
        ((fiberTwoPullbackDescentOfPullback f g cover).obj Q) ≅
      CategoricalPullback.snd Q :=
  Pseudofunctor.DescentData.isoMk (fun _ ↦ Iso.refl _) (by
    intro T q i₁ i₂ h₁ h₂ hh₁ hh₂
    rw [fiberTwoPullbackDescentSnd_obj_hom,
      fiberTwoPullbackDescentOfPullback_obj_hom_snd]
    let m := (CategoricalPullback.snd Q).hom q h₁ h₂ hh₁ hh₂
    exact (by
      calc
        (Y.toPseudofunctor.map h₁.op.toLoc).toFunctor.map
              (𝟙 ((CategoricalPullback.snd Q).obj i₁)) ≫ m =
            𝟙 _ ≫ m := congrArg (fun k ↦ k ≫ m)
              ((Y.toPseudofunctor.map h₁.op.toLoc).toFunctor.map_id _)
        _ = m := Category.id_comp m
        _ = m ≫ 𝟙 _ := (Category.comp_id m).symm
        _ = m ≫ (Y.toPseudofunctor.map h₂.op.toLoc).toFunctor.map
              (𝟙 ((CategoricalPullback.snd Q).obj i₂)) :=
          congrArg (fun k ↦ m ≫ k)
            ((Y.toPseudofunctor.map h₂.op.toLoc).toFunctor.map_id _).symm))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def fiberTwoPullbackDescentCounitIsoApp
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (Q : TwoPullback (f.mapDescentDataFunctor cover)
      (g.mapDescentDataFunctor cover)) :
    (fiberTwoPullbackDescentToPullback f g cover).obj
        ((fiberTwoPullbackDescentOfPullback f g cover).obj Q) ≅ Q :=
  CategoricalPullback.mkIso (fiberTwoPullbackDescentCounitFstIso f g cover Q)
    (fiberTwoPullbackDescentCounitSndIso f g cover Q) (by
      apply Pseudofunctor.DescentData.hom_ext
      intro i
      change
        (f.app (.mk (Opposite.op (U i)))).toFunctor.map (𝟙 _) ≫
            Q.iso.hom.hom i =
          Q.iso.hom.hom i ≫
            (g.app (.mk (Opposite.op (U i)))).toFunctor.map (𝟙 _)
      let m := Q.iso.hom.hom i
      exact (by
        calc
          (f.app (.mk (Opposite.op (U i)))).toFunctor.map
                (𝟙 ((CategoricalPullback.fst Q).obj i)) ≫ m =
              𝟙 _ ≫ m := congrArg (fun k ↦ k ≫ m)
                ((f.app (.mk (Opposite.op (U i)))).toFunctor.map_id _)
          _ = m := Category.id_comp m
          _ = m ≫ 𝟙 _ := (Category.comp_id m).symm
          _ = m ≫ (g.app (.mk (Opposite.op (U i)))).toFunctor.map
                (𝟙 ((CategoricalPullback.snd Q).obj i)) :=
            congrArg (fun k ↦ m ≫ k)
              ((g.app (.mk (Opposite.op (U i)))).toFunctor.map_id _).symm))

private noncomputable def fiberTwoPullbackDescentCounitIso
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    fiberTwoPullbackDescentOfPullback f g cover ⋙
        fiberTwoPullbackDescentToPullback f g cover ≅
      𝟭 (TwoPullback (f.mapDescentDataFunctor cover)
        (g.mapDescentDataFunctor cover)) :=
  NatIso.ofComponents (fiberTwoPullbackDescentCounitIsoApp f g cover) (by
    intro Q R phi
    apply CategoricalPullback.hom_ext
    · apply Pseudofunctor.DescentData.hom_ext
      intro i
      change phi.fst.hom i ≫ 𝟙 _ = 𝟙 _ ≫ phi.fst.hom i
      simp
    · apply Pseudofunctor.DescentData.hom_ext
      intro i
      change phi.snd.hom i ≫ 𝟙 _ = 𝟙 _ ≫ phi.snd.hom i
      simp)

/-- Descent data in the fibrewise genuine two-pullback are equivalent to the genuine
two-pullback of the component descent categories.  Both directions and both natural
isomorphisms are constructed componentwise. -/
noncomputable def fiberTwoPullbackDescentEquivalence
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).DescentData cover ≌
      TwoPullback (f.mapDescentDataFunctor cover)
        (g.mapDescentDataFunctor cover) where
  functor := fiberTwoPullbackDescentToPullback f g cover
  inverse := fiberTwoPullbackDescentOfPullback f g cover
  unitIso := fiberTwoPullbackDescentUnitIso f g cover
  counitIso := fiberTwoPullbackDescentCounitIso f g cover
  functor_unitIso_comp D := by
    apply CategoricalPullback.hom_ext
    · apply Pseudofunctor.DescentData.hom_ext
      intro i
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp
    · apply Pseudofunctor.DescentData.hom_ext
      intro i
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp

/-- The functor obtained by applying the three canonical global-to-descent functors to a
genuine fibrewise two-pullback. -/
noncomputable def fiberTwoPullbackGlobalToDescentPullback
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    StackInGroupoids.FiberTwoPullback f g S ⥤
      TwoPullback (f.mapDescentDataFunctor cover)
        (g.mapDescentDataFunctor cover) :=
  CategoricalPullback.mapCospan
    (X.toPseudofunctor.toDescentData cover)
    (Z.toPseudofunctor.toDescentData cover)
    (Y.toPseudofunctor.toDescentData cover)
    (f.toDescentDataMapIso cover)
    (g.toDescentDataMapIso cover).symm

set_option linter.style.haveILetI false in
/-- On an fppf cover, applying global-to-descent to all three terms of a cospan induces an
equivalence on their genuine categorical pullbacks. -/
theorem fiberTwoPullbackGlobalToDescentPullback_isEquivalence
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (hcover : Sieve.ofArrows U cover ∈
      (_root_.AlgebraicGeometry.Scheme.fppfTopology :
        GrothendieckTopology Scheme.{u₁}) S) :
    (fiberTwoPullbackGlobalToDescentPullback f g cover).IsEquivalence := by
  haveI : (X.toPseudofunctor.toDescentData cover).IsEquivalence :=
    X.toPseudofunctor.isEquivalence_toDescentData cover hcover
  haveI : (Y.toPseudofunctor.toDescentData cover).IsEquivalence :=
    Y.toPseudofunctor.isEquivalence_toDescentData cover hcover
  haveI : (Z.toPseudofunctor.toDescentData cover).IsEquivalence :=
    Z.toPseudofunctor.isEquivalence_toDescentData cover hcover
  unfold fiberTwoPullbackGlobalToDescentPullback
  infer_instance

private noncomputable def fiberTwoPullbackGlobalToDescentPullbackFstIso
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (p : StackInGroupoids.FiberTwoPullback f g S) :
    CategoricalPullback.fst
        (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).toDescentData cover ⋙
          fiberTwoPullbackDescentToPullback f g cover).obj p) ≅
      CategoricalPullback.fst
        ((fiberTwoPullbackGlobalToDescentPullback f g cover).obj p) :=
  ((fiberTwoPullbackFst f g).toDescentDataMapIso cover).app p

private noncomputable def fiberTwoPullbackGlobalToDescentPullbackSndIso
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (p : StackInGroupoids.FiberTwoPullback f g S) :
    CategoricalPullback.snd
        (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).toDescentData cover ⋙
          fiberTwoPullbackDescentToPullback f g cover).obj p) ≅
      CategoricalPullback.snd
        ((fiberTwoPullbackGlobalToDescentPullback f g cover).obj p) :=
  ((fiberTwoPullbackSnd f g).toDescentDataMapIso cover).app p

@[simp]
private theorem fiberTwoPullbackGlobalToDescentPullbackFstIso_hom_hom
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (p : StackInGroupoids.FiberTwoPullback f g S) (i : ι) :
    (fiberTwoPullbackGlobalToDescentPullbackFstIso f g cover p).hom.hom i =
      𝟙 _ := rfl

@[simp]
private theorem fiberTwoPullbackGlobalToDescentPullbackSndIso_hom_hom
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (p : StackInGroupoids.FiberTwoPullback f g S) (i : ι) :
    (fiberTwoPullbackGlobalToDescentPullbackSndIso f g cover p).hom.hom i =
      𝟙 _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def fiberTwoPullbackGlobalToDescentPullbackIsoApp
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (p : StackInGroupoids.FiberTwoPullback f g S) :
    (((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).toDescentData cover ⋙
        fiberTwoPullbackDescentToPullback f g cover).obj p) ≅
      (fiberTwoPullbackGlobalToDescentPullback f g cover).obj p :=
  CategoricalPullback.mkIso
    (fiberTwoPullbackGlobalToDescentPullbackFstIso f g cover p)
    (fiberTwoPullbackGlobalToDescentPullbackSndIso f g cover p)
    (by
      apply Pseudofunctor.DescentData.hom_ext
      intro i
      change
        (f.app (.mk (Opposite.op (U i)))).toFunctor.map
              ((fiberTwoPullbackGlobalToDescentPullbackFstIso
                f g cover p).hom.hom i) ≫
            ((fiberTwoPullbackGlobalToDescentPullback f g cover).obj p).iso.hom.hom i =
          ((((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).toDescentData cover ⋙
              fiberTwoPullbackDescentToPullback f g cover).obj p).iso.hom).hom i ≫
            (g.app (.mk (Opposite.op (U i)))).toFunctor.map
              ((fiberTwoPullbackGlobalToDescentPullbackSndIso
                f g cover p).hom.hom i)
      rw [fiberTwoPullbackGlobalToDescentPullbackFstIso_hom_hom,
        fiberTwoPullbackGlobalToDescentPullbackSndIso_hom_hom]
      calc
        _ = ((fiberTwoPullbackGlobalToDescentPullback f g cover).obj p).iso.hom.hom i := by
          rw [(f.app (.mk (Opposite.op (U i)))).toFunctor.map_id,
            Category.id_comp]
        _ = ((((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).toDescentData cover ⋙
              fiberTwoPullbackDescentToPullback f g cover).obj p).iso.hom).hom i := rfl
        _ = _ := by
          rw [(g.app (.mk (Opposite.op (U i)))).toFunctor.map_id]
          exact (Category.comp_id _).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical global-to-descent functor for the fibrewise pullback agrees with the
pullback functor induced by the three component global-to-descent functors. -/
noncomputable def fiberTwoPullbackGlobalToDescentPullbackIso
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S) :
    (StackInGroupoids.fiberTwoPullbackPseudofunctor f g).toDescentData cover ⋙
        fiberTwoPullbackDescentToPullback f g cover ≅
      fiberTwoPullbackGlobalToDescentPullback f g cover :=
  NatIso.ofComponents
    (fiberTwoPullbackGlobalToDescentPullbackIsoApp f g cover)
    (by
      intro p q h
      apply CategoricalPullback.hom_ext
      · apply Pseudofunctor.DescentData.hom_ext
        intro i
        change
          (X.toPseudofunctor.map (cover i).op.toLoc).toFunctor.map h.fst ≫ 𝟙 _ =
            𝟙 _ ≫ (X.toPseudofunctor.map (cover i).op.toLoc).toFunctor.map h.fst
        simp
      · apply Pseudofunctor.DescentData.hom_ext
        intro i
        change
          (Y.toPseudofunctor.map (cover i).op.toLoc).toFunctor.map h.snd ≫ 𝟙 _ =
            𝟙 _ ≫ (Y.toPseudofunctor.map (cover i).op.toLoc).toFunctor.map h.snd
        simp)

set_option linter.style.haveILetI false in
/-- The canonical global-to-descent functor for the fibrewise pullback is an equivalence on
every fppf cover.  This is deduced from the three component stack conditions and the proved
comparison above. -/
theorem fiberTwoPullbackToDescentData_isEquivalence
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z)
    {ι : Type*} {S : Scheme.{u₁}} {U : ι → Scheme.{u₁}}
    (cover : ∀ i, U i ⟶ S)
    (hcover : Sieve.ofArrows U cover ∈
      (_root_.AlgebraicGeometry.Scheme.fppfTopology :
        GrothendieckTopology Scheme.{u₁}) S) :
    ((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).toDescentData cover).IsEquivalence := by
  have hglobal : (fiberTwoPullbackGlobalToDescentPullback f g cover).IsEquivalence :=
    fiberTwoPullbackGlobalToDescentPullback_isEquivalence f g cover hcover
  have hpullback : (fiberTwoPullbackDescentToPullback f g cover).IsEquivalence :=
    (fiberTwoPullbackDescentEquivalence f g cover).isEquivalence_functor
  have hcomposite :
      ((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).toDescentData cover ⋙
        fiberTwoPullbackDescentToPullback f g cover).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso
      (fiberTwoPullbackGlobalToDescentPullbackIso f g cover)).2 hglobal
  haveI := hpullback
  haveI := hcomposite
  exact Functor.isEquivalence_of_comp_right
    ((StackInGroupoids.fiberTwoPullbackPseudofunctor f g).toDescentData cover)
    (fiberTwoPullbackDescentToPullback f g cover)

/-- Genuine fibrewise two-pullbacks of fppf stacks are fppf stacks.  Effective descent is
proved from the component stack conditions; it is not an input field of this construction. -/
noncomputable def fiberTwoPullbackStack
    {X Y Z : FppfStack.{u₁}} (f : StackHom X Z) (g : StackHom Y Z) :
    FppfStack.{u₁} where
  toPseudofunctor := StackInGroupoids.fiberTwoPullbackPseudofunctor f g
  isGroupoidValued :=
    StackInGroupoids.fiberTwoPullbackPseudofunctorIsGroupoidValued f g
  isStack := by
    apply Pseudofunctor.IsStack.of_isStackFor
    intro S R hR
    rw [Pseudofunctor.isStackFor_iff]
    apply fiberTwoPullbackToDescentData_isEquivalence f g
    rw [Sieve.ofArrows_category']
    simpa using hR

/-- The fibrewise cone functor determined by the displayed global projections and comparison
2-cell. Its target object contains those two projected objects and the actual component of the
global comparison; its action on arrows is forced by naturality. -/
noncomputable def stackConeFiberFunctor
    {W X Y Z : FppfStack.{u₁}}
    (f : StackHom X Z) (g : StackHom Y Z)
    (fst : StackHom W X) (snd : StackHom W Y)
    (comparison : StackIso2
      (Pseudofunctor.StrongTrans.vcomp fst f)
      (Pseudofunctor.StrongTrans.vcomp snd g))
    (U : Scheme.{u₁}) :
    StackFiber W U ⥤ StackInGroupoids.FiberTwoPullback f g U where
  obj x :=
    { fst := (StackHom.appFunctor fst U).obj x
      snd := (StackHom.appFunctor snd U).obj x
      iso := (comparison.appIso U).app x }
  map {x y} h :=
    { fst := (StackHom.appFunctor fst U).map h
      snd := (StackHom.appFunctor snd U).map h
      w := by
        exact (comparison.appIso U).hom.naturality h }
  map_id x := by
    apply CategoricalPullback.hom_ext <;> simp
  map_comp h k := by
    apply CategoricalPullback.hom_ext <;> simp

/-- A genuine stack-level two-pullback presentation.  In every test fibre it is equivalent to
Mathlib's `CategoricalPullback`, whose objects retain the invertible comparison arrow.  The
global projections and comparison are strong transformations and an invertible modification,
so this object cannot collapse to a strict pullback silently. -/
structure StackTwoPullback {X Y Z : FppfStack.{u₁}}
    (f : StackHom X Z) (g : StackHom Y Z) where
  /-- The resulting stack in groupoids. -/
  pullback : FppfStack.{u₁}
  /-- First projection. -/
  fst : StackHom pullback X
  /-- Second projection. -/
  snd : StackHom pullback Y
  /-- The specified invertible comparison 2-cell. -/
  comparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp fst f)
    (Pseudofunctor.StrongTrans.vcomp snd g)
  /-- Identification with the genuine categorical pullback in every fibre. -/
  fiberEquiv (U : Scheme.{u₁}) :
    StackFiber pullback U ≌ StackInGroupoids.FiberTwoPullback f g U
  /-- The equivalence is induced by the displayed projections and comparison, up to a natural
  isomorphism. This prevents an unrelated equivalence with the same target category. -/
  fiberEquivCompatibility (U : Scheme.{u₁}) :
    (fiberEquiv U).functor ≅
      stackConeFiberFunctor f g fst snd comparison U

namespace StackTwoPullback

variable {X Y Z : FppfStack.{u₁}} {f : StackHom X Z} {g : StackHom Y Z}

/-- The canonical stack-level two-pullback constructed from the fibrewise categorical
pullback pseudofunctor.  Its stack condition is the one proved above from the stack
conditions on `X`, `Y`, and `Z`; its fibres are definitionally the genuine categorical
pullbacks, so no comparison-arrow data is discarded. -/
noncomputable def canonical
    (f : StackHom X Z) (g : StackHom Y Z) :
    StackTwoPullback f g where
  pullback := fiberTwoPullbackStack f g
  fst := fiberTwoPullbackFst f g
  snd := fiberTwoPullbackSnd f g
  comparison :=
    { hom := fiberTwoPullbackComparisonHom f g
      inv := fiberTwoPullbackComparisonInv f g
      hom_inv_id := fiberTwoPullbackComparison_hom_inv_id f g
      inv_hom_id := fiberTwoPullbackComparison_inv_hom_id f g }
  fiberEquiv _ := CategoryTheory.Equivalence.refl
  fiberEquivCompatibility _ := Iso.refl _

/-- Swapping the categorical-pullback output of a stack cone is naturally the cone obtained by
swapping its two global projections and inverting its comparison 2-cell. -/
noncomputable def stackConeFiberFunctorSwapIso (P : StackTwoPullback f g)
    (U : Scheme.{u₁}) :
    stackConeFiberFunctor f g P.fst P.snd P.comparison U ⋙
        TwoPullback.swapFunctor
          (f.app (LocallyDiscrete.mk (Opposite.op U))).toFunctor
          (g.app (LocallyDiscrete.mk (Opposite.op U))).toFunctor ≅
      stackConeFiberFunctor g f P.snd P.fst P.comparison.symm U :=
  Iso.refl _

/-- The presentation obtained by interchanging the two legs of a stack two-pullback.  Its
fibre comparison is constructed by the involutive categorical-pullback equivalence. -/
noncomputable def swapPresentation (P : StackTwoPullback f g) :
    StackTwoPullback g f where
  pullback := P.pullback
  fst := P.snd
  snd := P.fst
  comparison := P.comparison.symm
  fiberEquiv U := (P.fiberEquiv U).trans
    (TwoPullback.swapEquivalence
      (f.app (LocallyDiscrete.mk (Opposite.op U))).toFunctor
      (g.app (LocallyDiscrete.mk (Opposite.op U))).toFunctor)
  fiberEquivCompatibility U :=
    Functor.isoWhiskerRight (P.fiberEquivCompatibility U)
        (TwoPullback.swapFunctor
          (f.app (LocallyDiscrete.mk (Opposite.op U))).toFunctor
          (g.app (LocallyDiscrete.mk (Opposite.op U))).toFunctor) ≪≫
      stackConeFiberFunctorSwapIso P U

/-- Whiskering a modification of stack morphisms on the right by another stack morphism. -/
def whiskerRightModification {A B D : FppfStack.{u₁}}
    {h k : StackHom A B}
    (eta : Pseudofunctor.StrongTrans.Modification h k) (q : StackHom B D) :
    Pseudofunctor.StrongTrans.Modification
      (Pseudofunctor.StrongTrans.vcomp h q)
      (Pseudofunctor.StrongTrans.vcomp k q) :=
  (Pseudofunctor.StrongTrans.whiskerRight
    (Pseudofunctor.StrongTrans.Hom.of eta) q).as

/-- A cone over a stack cospan, including its invertible comparison 2-cell. -/
structure Cone (T : FppfStack.{u₁}) where
  fst : StackHom T X
  snd : StackHom T Y
  comparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp fst f)
    (Pseudofunctor.StrongTrans.vcomp snd g)

namespace Cone

/-- Interchange the two legs of a bicategorical cone and invert its comparison 2-cell. -/
def swap {T : FppfStack.{u₁}} (c : Cone (f := f) (g := g) T) :
    Cone (f := g) (g := f) T where
  fst := c.snd
  snd := c.fst
  comparison := c.comparison.symm

@[simp]
theorem swap_fst {T : FppfStack.{u₁}} (c : Cone (f := f) (g := g) T) :
    c.swap.fst = c.snd := rfl

@[simp]
theorem swap_snd {T : FppfStack.{u₁}} (c : Cone (f := f) (g := g) T) :
    c.swap.snd = c.fst := rfl

end Cone

/-- Compatibility saying that two projection isomorphisms identify the comparison arrow of a
candidate lift with the comparison arrow of the given cone.  This is the missing face of the
usual bicategorical cone diagram; projection isomorphisms alone do not determine it. -/
def ConeLiftClassifies (P : StackTwoPullback f g)
    {T : FppfStack.{u₁}} (c : Cone (f := f) (g := g) T)
    (h : StackHom T P.pullback)
    (hfst : StackIso2 (Pseudofunctor.StrongTrans.vcomp h P.fst) c.fst)
    (hsnd : StackIso2 (Pseudofunctor.StrongTrans.vcomp h P.snd) c.snd) : Prop :=
  ∀ (U : Scheme.{u₁}) (x : StackFiber T U),
    ((StackHom.appFunctor f U).mapIso ((hfst.appIso U).app x)).trans
        ((c.comparison.appIso U).app x) =
      ((P.comparison.appIso U).app ((StackHom.appFunctor h U).obj x)).trans
        ((StackHom.appFunctor g U).mapIso ((hsnd.appIso U).app x))

/- Swapping a pullback cone preserves the comparison-face equation.  Both directions are
proved by cancelling the actual invertible comparison arrows, not by identifying the two
orientations definitionally. -/
set_option backward.isDefEq.respectTransparency false in
theorem coneLiftClassifies_swap_iff (P : StackTwoPullback f g)
    {T : FppfStack.{u₁}} (c : Cone (f := g) (g := f) T)
    (h : StackHom T P.pullback)
    (hfst : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h P.snd) c.fst)
    (hsnd : StackIso2
      (Pseudofunctor.StrongTrans.vcomp h P.fst) c.snd) :
    ConeLiftClassifies (swapPresentation P) c h hfst hsnd ↔
      ConeLiftClassifies P c.swap h hsnd hfst := by
  constructor
  · intro hc U x
    have hx := congrArg Iso.hom (hc U x)
    change
      ((StackHom.appFunctor g U).mapIso ((hfst.appIso U).app x)).hom ≫
          (c.comparison.appIso U).hom.app x =
        (P.comparison.appIso U).inv.app
            ((StackHom.appFunctor h U).obj x) ≫
          ((StackHom.appFunctor f U).mapIso ((hsnd.appIso U).app x)).hom at hx
    apply Iso.ext
    change
      ((StackHom.appFunctor f U).mapIso ((hsnd.appIso U).app x)).hom ≫
          (c.comparison.appIso U).inv.app x =
        (P.comparison.appIso U).hom.app
            ((StackHom.appFunctor h U).obj x) ≫
          ((StackHom.appFunctor g U).mapIso ((hfst.appIso U).app x)).hom
    rw [← cancel_mono ((c.comparison.appIso U).hom.app x)]
    simp only [Category.assoc]
    rw [hx]
    simp only [Functor.mapIso_hom, Iso.app_hom, Iso.inv_hom_id_app,
      Iso.hom_inv_id_app_assoc]
    exact Category.comp_id
      (((StackHom.appFunctor f U).mapIso ((hsnd.appIso U).app x)).hom)
  · intro hc U x
    have hx := congrArg Iso.hom (hc U x)
    change
      ((StackHom.appFunctor f U).mapIso ((hsnd.appIso U).app x)).hom ≫
          (c.comparison.appIso U).inv.app x =
        (P.comparison.appIso U).hom.app
            ((StackHom.appFunctor h U).obj x) ≫
          ((StackHom.appFunctor g U).mapIso ((hfst.appIso U).app x)).hom at hx
    apply Iso.ext
    change
      ((StackHom.appFunctor g U).mapIso ((hfst.appIso U).app x)).hom ≫
          (c.comparison.appIso U).hom.app x =
        (P.comparison.appIso U).inv.app
            ((StackHom.appFunctor h U).obj x) ≫
          ((StackHom.appFunctor f U).mapIso ((hsnd.appIso U).app x)).hom
    rw [← cancel_mono ((c.comparison.appIso U).inv.app x)]
    simp only [Category.assoc]
    rw [hx]
    simp only [Functor.mapIso_hom, Iso.app_hom, Iso.hom_inv_id_app,
      Iso.inv_hom_id_app_assoc]
    exact Category.comp_id
      (((StackHom.appFunctor g U).mapIso ((hfst.appIso U).app x)).hom)

/-- A compatible pair of 2-cells between the projections of two maps to a presented
two-pullback.  The last equation is precisely the morphism equation in the categorical
pullback: it prevents two unrelated projection modifications from being treated as a
2-morphism of cones. -/
structure ProjectionTwoCell (P : StackTwoPullback f g)
    {T : FppfStack.{u₁}} (h k : StackHom T P.pullback) where
  fst : Pseudofunctor.StrongTrans.Modification
    (Pseudofunctor.StrongTrans.vcomp h P.fst)
    (Pseudofunctor.StrongTrans.vcomp k P.fst)
  snd : Pseudofunctor.StrongTrans.Modification
    (Pseudofunctor.StrongTrans.vcomp h P.snd)
    (Pseudofunctor.StrongTrans.vcomp k P.snd)
  compatibility (U : Scheme.{u₁}) (x : StackFiber T U) :
    (StackHom.appFunctor f U).map
          (((fst.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x) ≫
        (P.comparison.appIso U).hom.app ((StackHom.appFunctor k U).obj x) =
      (P.comparison.appIso U).hom.app ((StackHom.appFunctor h U).obj x) ≫
        (StackHom.appFunctor g U).map
          (((snd.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x)

namespace ProjectionTwoCell

@[ext]
theorem ext {P : StackTwoPullback f g} {T : FppfStack.{u₁}}
    {h k : StackHom T P.pullback} {a b : ProjectionTwoCell P h k}
    (hfst : a.fst = b.fst) (hsnd : a.snd = b.snd) : a = b := by
  cases a
  cases b
  cases hfst
  cases hsnd
  rfl

/- A compatible pair for the swapped presentation gives one for the original presentation by
interchanging its components.  Compatibility is rotated through the actual comparison
isomorphism. -/
set_option backward.isDefEq.respectTransparency false in
noncomputable def unswap (P : StackTwoPullback f g)
    {T : FppfStack.{u₁}} {h k : StackHom T P.pullback}
    (p : ProjectionTwoCell (swapPresentation P) h k) :
    ProjectionTwoCell P h k where
  fst := p.snd
  snd := p.fst
  compatibility U x := by
    have hp := p.compatibility U x
    change
      (StackHom.appFunctor g U).map
            (((p.fst.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x) ≫
          (P.comparison.appIso U).inv.app
            ((StackHom.appFunctor k U).obj x) =
        (P.comparison.appIso U).inv.app
            ((StackHom.appFunctor h U).obj x) ≫
          (StackHom.appFunctor f U).map
            (((p.snd.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x) at hp
    change
      (StackHom.appFunctor f U).map
            (((p.snd.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x) ≫
          (P.comparison.appIso U).hom.app
            ((StackHom.appFunctor k U).obj x) =
        (P.comparison.appIso U).hom.app
            ((StackHom.appFunctor h U).obj x) ≫
          (StackHom.appFunctor g U).map
            (((p.fst.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x)
    rw [← cancel_mono
      ((P.comparison.appIso U).inv.app ((StackHom.appFunctor k U).obj x))]
    simp only [Category.assoc]
    rw [hp]
    simp only [Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
    exact Category.comp_id
      ((StackHom.appFunctor f U).map
        (((p.snd.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x))

end ProjectionTwoCell

/-- A modification between maps to the pullback induces its two compatible projected
modifications.  Compatibility is naturality of the displayed comparison 2-cell. -/
def projectedTwoCell (P : StackTwoPullback f g)
    {T : FppfStack.{u₁}} {h k : StackHom T P.pullback}
    (eta : Pseudofunctor.StrongTrans.Modification h k) :
    ProjectionTwoCell P h k where
  fst := whiskerRightModification eta P.fst
  snd := whiskerRightModification eta P.snd
  compatibility U x := by
    exact (P.comparison.appIso U).hom.naturality
      (((eta.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x)

/- Full faithfulness of the projection functor is invariant under swapping the pullback legs.
The proof explicitly interchanges the two projected modifications; no new hom-set bijection is
accepted as data. -/
set_option backward.isDefEq.respectTransparency false in
theorem swapProjectedTwoCell_bijective (P : StackTwoPullback f g)
    {T : FppfStack.{u₁}} (h k : StackHom T P.pullback)
    (hp : Function.Bijective (projectedTwoCell P (h := h) (k := k))) :
    Function.Bijective
      (projectedTwoCell (swapPresentation P) (h := h) (k := k)) := by
  constructor
  · intro eta theta heq
    apply hp.1
    apply ProjectionTwoCell.ext
    · exact congrArg ProjectionTwoCell.snd heq
    · exact congrArg ProjectionTwoCell.fst heq
  · intro p
    obtain ⟨eta, heta⟩ := hp.2 (ProjectionTwoCell.unswap P p)
    refine ⟨eta, ?_⟩
    apply ProjectionTwoCell.ext
    · exact congrArg ProjectionTwoCell.snd heta
    · exact congrArg ProjectionTwoCell.fst heta

/-- Bicategorical universal-property data for a presented stack two-pullback. -/
structure IsBilimit (P : StackTwoPullback f g) where
  /-- Lift a cone to the pullback. -/
  lift {T : FppfStack.{u₁}} (c : Cone (f := f) (g := g) T) : StackHom T P.pullback
  /-- The first projected lift is 2-isomorphic to the given first leg. -/
  lift_fst {T : FppfStack.{u₁}} (c : Cone (f := f) (g := g) T) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (lift c) P.fst) c.fst
  /-- The second projected lift is 2-isomorphic to the given second leg. -/
  lift_snd {T : FppfStack.{u₁}} (c : Cone (f := f) (g := g) T) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (lift c) P.snd) c.snd
  /-- The chosen lift really classifies the supplied cone, including its comparison face. -/
  lift_compatible {T : FppfStack.{u₁}} (c : Cone (f := f) (g := g) T) :
    ConeLiftClassifies P c (lift c) (lift_fst c) (lift_snd c)
  /-- Any other lift is equivalent to the universal lift. -/
  lift_unique {T : FppfStack.{u₁}} (c : Cone (f := f) (g := g) T)
      (h : StackHom T P.pullback)
      (hfst : StackIso2 (Pseudofunctor.StrongTrans.vcomp h P.fst) c.fst)
      (hsnd : StackIso2 (Pseudofunctor.StrongTrans.vcomp h P.snd) c.snd)
      (_compatible : ConeLiftClassifies P c h hfst hsnd) :
    StackIso2 h (lift c)
  /-- The projection functor is fully faithful on the hom-category: modifications between
  maps to the pullback are in bijection with compatible pairs of projected modifications. -/
  projectedTwoCell_bijective {T : FppfStack.{u₁}}
      (h k : StackHom T P.pullback) :
    Function.Bijective (projectedTwoCell P (h := h) (k := k))

/-- A stack two-pullback together with its bicategorical universal property.  Bundling the
property prevents a fibrewise pullback-shaped presentation from being used as a cartesian
square without the required two-dimensional uniqueness theorem. -/
structure Genuine (f : StackHom X Z) (g : StackHom Y Z)
    extends StackTwoPullback f g where
  bilimit : toStackTwoPullback.IsBilimit

/- A genuine stack two-pullback remains genuine after its two legs are interchanged.  The lift,
comparison face, uniqueness 2-cell, and hom-category bijection are all transported from the
proved bilimit property of the original orientation. -/
set_option backward.isDefEq.respectTransparency false in
noncomputable def swap (P : Genuine f g) : Genuine g f where
  toStackTwoPullback := swapPresentation P.toStackTwoPullback
  bilimit :=
    { lift := fun c ↦ P.bilimit.lift c.swap
      lift_fst := fun c ↦ P.bilimit.lift_snd c.swap
      lift_snd := fun c ↦ P.bilimit.lift_fst c.swap
      lift_compatible := fun c ↦
        (coneLiftClassifies_swap_iff P.toStackTwoPullback c
          (P.bilimit.lift c.swap)
          (P.bilimit.lift_snd c.swap)
          (P.bilimit.lift_fst c.swap)).2
            (P.bilimit.lift_compatible c.swap)
      lift_unique := fun c h hfst hsnd hcompatible ↦
        P.bilimit.lift_unique c.swap h hsnd hfst
          ((coneLiftClassifies_swap_iff P.toStackTwoPullback c h hfst hsnd).1
            hcompatible)
      projectedTwoCell_bijective := fun h k ↦
        swapProjectedTwoCell_bijective P.toStackTwoPullback h k
          (P.bilimit.projectedTwoCell_bijective h k) }

/-- The standard right-identity fibre equivalence agrees with the cone functor determined by
the global identity pullback projections and its unitor comparison. -/
noncomputable def rightIdentitySecondIso (f : StackHom X Y)
    (U : Scheme.{u₁}) (x : StackFiber X U) :
    (StackHom.appFunctor f U).obj x ≅ (StackHom.appFunctor f U).obj x :=
  (StackHom.identityAppFullyFaithful Y U).preimageIso
    (((StackHom.appFunctor f U).mapIso (Iso.refl x)).trans
      ((((StackIso2.leftUnitor f).trans
        (StackIso2.rightUnitor f).symm).appIso U).app x))

@[simp]
theorem rightIdentitySecondIso_map (f : StackHom X Y)
    (U : Scheme.{u₁}) (x : StackFiber X U) :
    (StackHom.appFunctor
      (Pseudofunctor.StrongTrans.id Y.toPseudofunctor) U).map
        (rightIdentitySecondIso f U x).hom =
      (((StackHom.appFunctor f U).mapIso (Iso.refl x)).trans
        ((((StackIso2.leftUnitor f).trans
          (StackIso2.rightUnitor f).symm).appIso U).app x)).hom := by
  unfold rightIdentitySecondIso
  exact (StackHom.identityAppFullyFaithful Y U).map_preimage _

noncomputable def rightIdentityFiberCompatibility (f : StackHom X Y)
    (U : Scheme.{u₁}) :
    (TwoPullback.rightIdentityEquivalence
      (f.app (LocallyDiscrete.mk (Opposite.op U))).toFunctor).functor ≅
      stackConeFiberFunctor f
        (Pseudofunctor.StrongTrans.id Y.toPseudofunctor)
        (Pseudofunctor.StrongTrans.id X.toPseudofunctor) f
        ((StackIso2.leftUnitor f).trans (StackIso2.rightUnitor f).symm) U :=
  NatIso.ofComponents
    (fun x ↦ CategoricalPullback.mkIso (Iso.refl _) (rightIdentitySecondIso f U x) (by
      change (StackHom.appFunctor f U).map (𝟙 x) ≫
          ((((StackIso2.leftUnitor f).trans
            (StackIso2.rightUnitor f).symm).appIso U).app x).hom =
        𝟙 _ ≫
          (StackHom.appFunctor
            (Pseudofunctor.StrongTrans.id Y.toPseudofunctor) U).map
              (rightIdentitySecondIso f U x).hom
      simp only [Category.id_comp]
      rw [rightIdentitySecondIso_map]
      rfl))
    (by
      intro x y h
      apply CategoricalPullback.hom_ext_of_fst_of_fullyFaithfulSecond
        (StackHom.identityAppFullyFaithful Y U)
      change h ≫ 𝟙 y = 𝟙 x ≫
        (StackHom.appFunctor
          (Pseudofunctor.StrongTrans.id X.toPseudofunctor) U).map h
      change h ≫ 𝟙 y = 𝟙 x ≫ h
      simp)

/-- The stack-level cone underlying the right-identity two-pullback.  Keeping this definition
separate makes its projections and comparison available definitionally when proving the
bilimit face equation. -/
noncomputable def rightIdentityPresentation (f : StackHom X Y) : StackTwoPullback f
    (Pseudofunctor.StrongTrans.id Y.toPseudofunctor) where
  pullback := X
  fst := Pseudofunctor.StrongTrans.id X.toPseudofunctor
  snd := f
  comparison := (StackIso2.leftUnitor f).trans (StackIso2.rightUnitor f).symm
  fiberEquiv U := TwoPullback.rightIdentityEquivalence
    (f.app (LocallyDiscrete.mk (Opposite.op U))).toFunctor
  fiberEquivCompatibility U := rightIdentityFiberCompatibility f U

@[simp]
theorem rightUnitor_appIso_hom_app {A B : FppfStack.{u₁}}
    (q : StackHom A B) (U : Scheme.{u₁}) (x : StackFiber A U) :
    ((StackIso2.rightUnitor q).appIso U).hom.app x = 𝟙 _ := rfl

@[simp]
theorem rightUnitor_appIso_inv_app {A B : FppfStack.{u₁}}
    (q : StackHom A B) (U : Scheme.{u₁}) (x : StackFiber A U) :
    ((StackIso2.rightUnitor q).appIso U).inv.app x = 𝟙 _ := rfl

@[simp]
theorem leftUnitor_appIso_hom_app {A B : FppfStack.{u₁}}
    (q : StackHom A B) (U : Scheme.{u₁}) (x : StackFiber A U) :
    ((StackIso2.leftUnitor q).appIso U).hom.app x = 𝟙 _ := rfl

@[simp]
theorem leftUnitor_appIso_inv_app {A B : FppfStack.{u₁}}
    (q : StackHom A B) (U : Scheme.{u₁}) (x : StackFiber A U) :
    ((StackIso2.leftUnitor q).appIso U).inv.app x = 𝟙 _ := rfl

@[simp]
theorem trans_appIso_hom_app {A B : FppfStack.{u₁}}
    {q r s : StackHom A B} (e : StackIso2 q r) (e' : StackIso2 r s)
    (U : Scheme.{u₁}) (x : StackFiber A U) :
    ((e.trans e').appIso U).hom.app x =
      (e.appIso U).hom.app x ≫ (e'.appIso U).hom.app x := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem rightIdentityComparison_appIso_hom_app (f : StackHom X Y)
    (U : Scheme.{u₁}) (x : StackFiber X U) :
    (((rightIdentityPresentation f).comparison.appIso U).hom.app x) = 𝟙 _ := by
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp

@[simp]
theorem identityAppFunctor_map {A : FppfStack.{u₁}} (U : Scheme.{u₁})
    {x y : StackFiber A U} (h : x ⟶ y) :
    (StackHom.appFunctor
      (Pseudofunctor.StrongTrans.id A.toPseudofunctor) U).map h = h := rfl

set_option backward.isDefEq.respectTransparency false in
theorem rightIdentityLiftCompatible (f : StackHom X Y)
    {T : FppfStack.{u₁}}
    (c : Cone (f := f)
      (g := Pseudofunctor.StrongTrans.id Y.toPseudofunctor) T) :
    ConeLiftClassifies (rightIdentityPresentation f) c c.fst
      (StackIso2.rightUnitor c.fst)
      (c.comparison.trans (StackIso2.rightUnitor c.snd)) := by
  intro U x
  apply Iso.ext
  change
    (StackHom.appFunctor f U).map
          (((StackIso2.rightUnitor c.fst).appIso U).hom.app x) ≫
        (c.comparison.appIso U).hom.app x =
      ((rightIdentityPresentation f).comparison.appIso U).hom.app
          ((StackHom.appFunctor c.fst U).obj x) ≫
        (StackHom.appFunctor
          (Pseudofunctor.StrongTrans.id Y.toPseudofunctor) U).map
          (((c.comparison.trans
            (StackIso2.rightUnitor c.snd)).appIso U).hom.app x)
  rw [rightUnitor_appIso_hom_app]
  simp only [rightIdentityComparison_appIso_hom_app,
    trans_appIso_hom_app, rightUnitor_appIso_hom_app,
    identityAppFunctor_map]
  simp

/-- Recover a 2-cell from its first projection in a right-identity pullback.  This is the
quasi-inverse to right whiskering by the identity strong transformation. -/
noncomputable def rightIdentityUnproject (f : StackHom X Y)
    {T : FppfStack.{u₁}} {h k : StackHom T X}
    (p : ProjectionTwoCell (rightIdentityPresentation f) h k) :
    Pseudofunctor.StrongTrans.Modification h k :=
  Pseudofunctor.StrongTrans.Modification.vcomp
    (StackIso2.rightUnitor h).inv
    (Pseudofunctor.StrongTrans.Modification.vcomp p.fst
      (StackIso2.rightUnitor k).hom)

set_option backward.isDefEq.respectTransparency false in
theorem rightIdentityUnproject_projected_fst (f : StackHom X Y)
    {T : FppfStack.{u₁}} {h k : StackHom T X}
    (p : ProjectionTwoCell (rightIdentityPresentation f) h k) :
    (projectedTwoCell (rightIdentityPresentation f)
      (rightIdentityUnproject f p)).fst = p.fst := by
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext a
  rcases a with ⟨⟨U⟩⟩
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  change
    𝟙 _ ≫ (p.fst.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans.app x ≫
        𝟙 _ =
      (p.fst.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans.app x
  simp

theorem rightIdentityUnproject_projected_snd (f : StackHom X Y)
    {T : FppfStack.{u₁}} {h k : StackHom T X}
    (p : ProjectionTwoCell (rightIdentityPresentation f) h k) :
    (projectedTwoCell (rightIdentityPresentation f)
      (rightIdentityUnproject f p)).snd = p.snd := by
  let q := projectedTwoCell (rightIdentityPresentation f)
    (rightIdentityUnproject f p)
  have hfst : q.fst = p.fst := rightIdentityUnproject_projected_fst f p
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext a
  rcases a with ⟨⟨U⟩⟩
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  apply (StackHom.identityAppFullyFaithful Y U).map_injective
  apply (cancel_epi
    (((rightIdentityPresentation f).comparison.appIso U).hom.app
      ((StackHom.appFunctor h U).obj x))).1
  change
    ((rightIdentityPresentation f).comparison.appIso U).hom.app
          ((StackHom.appFunctor h U).obj x) ≫
        (StackHom.appFunctor
          (Pseudofunctor.StrongTrans.id Y.toPseudofunctor) U).map
          (((q.snd.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x) =
      ((rightIdentityPresentation f).comparison.appIso U).hom.app
          ((StackHom.appFunctor h U).obj x) ≫
        (StackHom.appFunctor
          (Pseudofunctor.StrongTrans.id Y.toPseudofunctor) U).map
          (((p.snd.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x)
  have hq := q.compatibility U x
  rw [hfst] at hq
  exact hq.symm.trans (p.compatibility U x)

theorem rightIdentityUnproject_projected (f : StackHom X Y)
    {T : FppfStack.{u₁}} {h k : StackHom T X}
    (p : ProjectionTwoCell (rightIdentityPresentation f) h k) :
    projectedTwoCell (rightIdentityPresentation f)
      (rightIdentityUnproject f p) = p := by
  apply ProjectionTwoCell.ext
  · exact rightIdentityUnproject_projected_fst f p
  · exact rightIdentityUnproject_projected_snd f p

theorem rightIdentityProjectedTwoCell_bijective (f : StackHom X Y)
    {T : FppfStack.{u₁}} (h k : StackHom T X) :
    Function.Bijective
      (projectedTwoCell (rightIdentityPresentation f) (h := h) (k := k)) := by
  constructor
  · intro eta theta heq
    have hfst := congrArg ProjectionTwoCell.fst heq
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    rcases a with ⟨⟨U⟩⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    apply (StackHom.identityAppFullyFaithful X U).map_injective
    have hx := congrArg
      (fun m ↦
        ((m.app (LocallyDiscrete.mk (Opposite.op U))).toNatTrans).app x)
      hfst
    exact hx
  · intro p
    exact ⟨rightIdentityUnproject f p,
      rightIdentityUnproject_projected f p⟩

/-- The genuine bicategorical pullback of `f : X ⟶ Y` along the identity of `Y`.  Its
pullback object is `X`, and both the fibrewise equivalence and global bilimit property are
constructed from the unitors and the comparison 2-cell of an arbitrary cone. -/
noncomputable def rightIdentity (f : StackHom X Y) : Genuine f
    (Pseudofunctor.StrongTrans.id Y.toPseudofunctor) where
  toStackTwoPullback := rightIdentityPresentation f
  bilimit :=
    { lift := fun c ↦ c.fst
      lift_fst := fun c ↦ StackIso2.rightUnitor c.fst
      lift_snd := fun c ↦ c.comparison.trans (StackIso2.rightUnitor c.snd)
      lift_compatible := fun c ↦ rightIdentityLiftCompatible f c
      lift_unique := fun _ h hfst _ _ ↦
        (StackIso2.rightUnitor h).symm.trans hfst
      projectedTwoCell_bijective := fun h k ↦
        rightIdentityProjectedTwoCell_bijective f h k }

/-- The genuine bicategorical pullback of the identity of `Y` along `f : X ⟶ Y`.
It is constructed by applying the proved symmetry operation to the right-identity pullback, so
its comparison face and full bilimit property are inherited rather than postulated again. -/
noncomputable def leftIdentity (f : StackHom X Y) :
    Genuine (Pseudofunctor.StrongTrans.id Y.toPseudofunctor) f :=
  swap (rightIdentity f)

/-- The fibre of a stack two-pullback is a groupoid. -/
noncomputable instance fiberIsGroupoid (P : StackTwoPullback f g) (U : Scheme.{u₁}) :
    IsGroupoid (StackFiber P.pullback U) := by
  infer_instance

/-- The fibre comparison preserves every arrow, in particular all stabilizer automorphisms. -/
noncomputable def fiberHomEquiv (P : StackTwoPullback f g) (U : Scheme.{u₁})
    (x y : StackFiber P.pullback U) :
    (x ⟶ y) ≃
      ((P.fiberEquiv U).functor.obj x ⟶ (P.fiberEquiv U).functor.obj y) :=
  (P.fiberEquiv U).fullyFaithfulFunctor.homEquiv

end StackTwoPullback

/-- Equivalence of stacks means adjoint equivalence in their induced bicategory. -/
abbrev StackEquivalence {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (X Y : StackBicategory.{v, v₁, u, u₁} C J) :=
  Bicategory.Equivalence X Y

end GromovWitten.AlgebraicGeometry
