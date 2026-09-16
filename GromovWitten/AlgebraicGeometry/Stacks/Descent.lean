/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Transporting descent data through strong transformations

A strong transformation of pseudofunctors sends descent data to descent data.  The transported
cocycle uses the inverse naturality cell at its source and the forward naturality cell at its
target.  In particular, no strict naturality assumption is hidden in this construction.
-/

open CategoryTheory
open CategoryTheory.Bicategory

namespace CategoryTheory.Pseudofunctor

open Opposite
open LocallyDiscreteOpToCat

universe t v' v u' u

variable {C : Type u} [Category.{v} C]
  {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

/-- Transport an object of the descent-data category along a strong transformation.

The naturality isomorphisms are part of the formula, so this does not identify pseudo- and
strict naturality. -/
noncomputable def StrongTrans.mapDescentData (eta : StrongTrans F G)
    {ι : Type t} {S : C} {X : ι → C} (cover : ∀ i, X i ⟶ S)
    (D : F.DescentData cover) : G.DescentData cover where
  obj i := (eta.app (.mk (op (X i)))).toFunctor.obj (D.obj i)
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (eta.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
      (eta.app (.mk (op Y))).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (eta.naturality f₂.op.toLoc).hom.toNatTrans.app (D.obj i₂)
  pullHom_hom Y' Y h q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ hf₁' hf₂' hhf₁ hhf₂ := by
    subst hf₁'
    subst hf₂'
    dsimp [pullHom]
    rw [G.mapComp'_eq_mapComp f₁.op.toLoc h.op.toLoc,
      G.mapComp'_eq_mapComp f₂.op.toLoc h.op.toLoc]
    simp only [Functor.map_comp, Category.assoc]
    rw [StrongTrans.naturality_comp_inv_app,
      StrongTrans.naturality_comp_hom_app]
    simp only [Category.assoc]
    rw [← D.pullHom_hom h q q' hq f₁ f₂ hf₁ hf₂
      (h ≫ f₁) (h ≫ f₂) rfl rfl]
    dsimp [pullHom]
    rw [F.mapComp'_eq_mapComp f₁.op.toLoc h.op.toLoc,
      F.mapComp'_eq_mapComp f₂.op.toLoc h.op.toLoc]
    conv_rhs =>
      rw [← Functor.map_comp_assoc,
        Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
      rw [← Functor.map_comp_assoc, Category.assoc,
        Cat.Hom.inv_hom_id_toNatTrans_app]
      simp only [Cat.comp_eq_comp, Functor.comp_obj]
      rw [Category.comp_id ((F.map h.op.toLoc).toFunctor.map
        (D.hom q f₁ f₂ hf₁ hf₂))]
    have hnat := (eta.naturality h.op.toLoc).hom.toNatTrans.naturality
      (D.hom q f₁ f₂ hf₁ hf₂)
    simp only [Cat.comp_eq_comp, Functor.comp_map] at hnat
    have hconj :
        (eta.naturality h.op.toLoc).inv.toNatTrans.app
              ((F.map f₁.op.toLoc).toFunctor.obj (D.obj i₁)) ≫
            (eta.app (.mk (op Y'))).toFunctor.map
              ((F.map h.op.toLoc).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂)) ≫
            (eta.naturality h.op.toLoc).hom.toNatTrans.app
              ((F.map f₂.op.toLoc).toFunctor.obj (D.obj i₂)) =
          (G.map h.op.toLoc).toFunctor.map
            ((eta.app (.mk (op Y))).toFunctor.map
              (D.hom q f₁ f₂ hf₁ hf₂)) := by
      rw [hnat]
      simp only [Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
    rw [cancel_epi ((G.mapComp f₁.op.toLoc h.op.toLoc).hom.toNatTrans.app
      ((eta.app (.mk (op (X i₁)))).toFunctor.obj (D.obj i₁)))]
    rw [cancel_epi ((G.map h.op.toLoc).toFunctor.map
      ((eta.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁)))]
    simp only [← Category.assoc]
    rw [cancel_mono
      ((G.mapComp f₂.op.toLoc h.op.toLoc).inv.toNatTrans.app
        ((eta.app (.mk (op (X i₂)))).toFunctor.obj (D.obj i₂)))]
    rw [cancel_mono ((G.map h.op.toLoc).toFunctor.map
      ((eta.naturality f₂.op.toLoc).hom.toNatTrans.app (D.obj i₂)))]
    simpa only [Category.assoc] using hconj.symm
  hom_self Y q i h hh := by
    dsimp
    simp [D.hom_self q h hh]
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    dsimp
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
    rw [← Functor.map_comp_assoc, D.hom_comp]

/-- Functorial transport of descent data along a strong transformation. -/
noncomputable def StrongTrans.mapDescentDataFunctor (eta : StrongTrans F G)
    {ι : Type t} {S : C} {X : ι → C} (cover : ∀ i, X i ⟶ S) :
    Functor (F.DescentData cover) (G.DescentData cover) where
  obj D := eta.mapDescentData cover D
  map {D₁ D₂} phi :=
    { hom i := (eta.app (.mk (op (X i)))).toFunctor.map (phi.hom i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        dsimp [StrongTrans.mapDescentData]
        have hleft := (eta.naturality f₁.op.toLoc).inv.toNatTrans.naturality
          (phi.hom i₁)
        have hright := (eta.naturality f₂.op.toLoc).hom.toNatTrans.naturality
          (phi.hom i₂)
        simp only [Cat.comp_eq_comp, Functor.comp_map] at hleft hright
        simp only [Category.assoc]
        rw [← Category.assoc, hleft, Category.assoc]
        rw [← Functor.map_comp_assoc, phi.comm q f₁ f₂ hf₁ hf₂,
          Functor.map_comp_assoc]
        rw [hright] }
  map_id D := by
    ext i
    dsimp [StrongTrans.mapDescentData]
    simp
  map_comp phi psi := by
    ext i
    dsimp [StrongTrans.mapDescentData]
    simp

variable {H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- Transporting descent data along a vertical composite of strong transformations is naturally
isomorphic to transporting it successively.  This is an explicit coherence isomorphism, not an
identification of pseudofunctorial composition with strict composition. -/
noncomputable def StrongTrans.mapDescentDataVcompIso
    (eta : StrongTrans F G) (theta : StrongTrans G H)
    {ι : Type t} {S : C} {X : ι → C} (cover : ∀ i, X i ⟶ S) :
    (StrongTrans.vcomp eta theta).mapDescentDataFunctor cover ≅
      eta.mapDescentDataFunctor cover ⋙ theta.mapDescentDataFunctor cover :=
  NatIso.ofComponents
    (fun D ↦ DescentData.isoMk (fun _ ↦ Iso.refl _) (by
      intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      dsimp [StrongTrans.mapDescentDataFunctor, StrongTrans.mapDescentData]
      simp [StrongTrans.vcomp, StrongTrans.mkOfOplax, StrongTrans.toOplax,
        Oplax.StrongTrans.vcomp, Oplax.StrongTrans.mkOfOplax,
        Oplax.StrongTrans.toOplax, Oplax.OplaxTrans.vcomp,
        Cat.Hom.comp_toFunctor]))
    (by
      intro D₁ D₂ phi
      ext i
      dsimp [StrongTrans.mapDescentDataFunctor, StrongTrans.mapDescentData]
      simp [StrongTrans.vcomp, StrongTrans.mkOfOplax, StrongTrans.toOplax,
        Oplax.StrongTrans.vcomp, Oplax.StrongTrans.mkOfOplax,
        Oplax.StrongTrans.toOplax, Oplax.OplaxTrans.vcomp,
        Cat.Hom.comp_toFunctor])

variable {eta mu : StrongTrans F G}

/-- A modification induces a natural transformation between the corresponding transport
functors on descent data.  Its components are the original modification components in every
member of the cover. -/
noncomputable def StrongTrans.Modification.mapDescentDataNatTrans
    (theta : StrongTrans.Modification eta mu)
    {ι : Type t} {S : C} {X : ι → C} (cover : ∀ i, X i ⟶ S) :
    eta.mapDescentDataFunctor cover ⟶ mu.mapDescentDataFunctor cover where
  app D :=
    { hom i := (theta.app (.mk (op (X i)))).toNatTrans.app (D.obj i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        dsimp [StrongTrans.mapDescentDataFunctor, StrongTrans.mapDescentData]
        have hm₁ := congrArg
          (fun k ↦ k.toNatTrans.app (D.obj i₁)) (theta.naturality f₁.op.toLoc)
        have hm₂ := congrArg
          (fun k ↦ k.toNatTrans.app (D.obj i₂)) (theta.naturality f₂.op.toLoc)
        simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
          Cat.whiskerRight_app, Cat.comp_eq_comp] at hm₁ hm₂
        have hleft :
            (G.map f₁.op.toLoc).toFunctor.map
                  ((theta.app (.mk (op (X i₁)))).toNatTrans.app (D.obj i₁)) ≫
                (mu.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) =
              (eta.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
                (theta.app (.mk (op Y))).toNatTrans.app
                  ((F.map f₁.op.toLoc).toFunctor.obj (D.obj i₁)) := by
          rw [← cancel_epi
            ((eta.naturality f₁.op.toLoc).hom.toNatTrans.app (D.obj i₁))]
          simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
          rw [← Category.assoc, ← hm₁]
          simp
        have hmid := (theta.app (.mk (op Y))).toNatTrans.naturality
          (D.hom q f₁ f₂ hf₁ hf₂)
        have hright := hm₂
        simp only [Category.assoc]
        rw [reassoc_of% hleft, ← reassoc_of% hmid, hright] }
  naturality {D₁ D₂} phi := by
    ext i
    exact (theta.app (.mk (op (X i)))).toNatTrans.naturality (phi.hom i)

@[simp]
theorem StrongTrans.Modification.mapDescentDataNatTrans_id
    (eta : StrongTrans F G)
    {ι : Type t} {S : C} {X : ι → C} (cover : ∀ i, X i ⟶ S) :
    (StrongTrans.Modification.id eta).mapDescentDataNatTrans cover =
      𝟙 (eta.mapDescentDataFunctor cover) := by
  ext D i
  rfl

@[simp]
theorem StrongTrans.Modification.mapDescentDataNatTrans_vcomp
    {nu : StrongTrans F G}
    (theta : StrongTrans.Modification eta mu)
    (gamma : StrongTrans.Modification mu nu)
    {ι : Type t} {S : C} {X : ι → C} (cover : ∀ i, X i ⟶ S) :
    (StrongTrans.Modification.vcomp theta gamma).mapDescentDataNatTrans cover =
      theta.mapDescentDataNatTrans cover ≫ gamma.mapDescentDataNatTrans cover := by
  ext D i
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma StrongTrans.naturality_comp'_hom_app (eta : StrongTrans F G)
    {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (fg : a ⟶ c) (hfg : f ≫ g = fg) (M : F.obj a) :
    (eta.naturality fg).hom.toNatTrans.app M =
      (eta.app c).toFunctor.map ((F.mapComp' f g fg hfg).hom.toNatTrans.app M) ≫
        (eta.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj M) ≫
          (G.map g).toFunctor.map ((eta.naturality f).hom.toNatTrans.app M) ≫
            (G.mapComp' f g fg hfg).inv.toNatTrans.app
              ((eta.app a).toFunctor.obj M) := by
  subst fg
  simpa only [F.mapComp'_eq_mapComp, G.mapComp'_eq_mapComp] using
    StrongTrans.naturality_comp_hom_app eta f g M

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- A strong transformation commutes with the canonical global-to-descent functors,
up to the actual pseudofunctorial naturality cells. -/
noncomputable def StrongTrans.toDescentDataMapIso (eta : StrongTrans F G)
    {ι : Type t} {S : C} {X : ι → C} (cover : ∀ i, X i ⟶ S) :
    F.toDescentData cover ⋙ eta.mapDescentDataFunctor cover ≅
      (eta.app (.mk (op S))).toFunctor ⋙ G.toDescentData cover :=
  NatIso.ofComponents
    (fun M ↦ DescentData.isoMk
      (fun i ↦ (Cat.Hom.toNatIso (eta.naturality (cover i).op.toLoc)).app M)
      (by
        intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
        dsimp [StrongTrans.mapDescentDataFunctor, StrongTrans.mapDescentData,
          Pseudofunctor.toDescentData, DescentData.ofObj]
        have hfg₁ :
            (cover i₁).op.toLoc ≫ f₁.op.toLoc = q.op.toLoc := by
          simpa only [op_comp, Quiver.Hom.comp_toLoc] using
            congrArg (fun h ↦ h.op.toLoc) hf₁
        have hfg₂ :
            (cover i₂).op.toLoc ≫ f₂.op.toLoc = q.op.toLoc := by
          simpa only [op_comp, Quiver.Hom.comp_toLoc] using
            congrArg (fun h ↦ h.op.toLoc) hf₂
        have hF₁ : ∀ h,
            F.mapComp' (cover i₁).op.toLoc f₁.op.toLoc q.op.toLoc h =
              F.mapComp' (cover i₁).op.toLoc f₁.op.toLoc q.op.toLoc hfg₁ := by
          intro h
          congr
        have hG₁ : ∀ h,
            G.mapComp' (cover i₁).op.toLoc f₁.op.toLoc q.op.toLoc h =
              G.mapComp' (cover i₁).op.toLoc f₁.op.toLoc q.op.toLoc hfg₁ := by
          intro h
          congr
        have hF₂ : ∀ h,
            F.mapComp' (cover i₂).op.toLoc f₂.op.toLoc q.op.toLoc h =
              F.mapComp' (cover i₂).op.toLoc f₂.op.toLoc q.op.toLoc hfg₂ := by
          intro h
          congr
        have hG₂ : ∀ h,
            G.mapComp' (cover i₂).op.toLoc f₂.op.toLoc q.op.toLoc h =
              G.mapComp' (cover i₂).op.toLoc f₂.op.toLoc q.op.toLoc hfg₂ := by
          intro h
          congr
        have hcancelF :
            (eta.app (.mk (op Y))).toFunctor.map
                ((F.mapComp' (cover i₁).op.toLoc f₁.op.toLoc
                  q.op.toLoc hfg₁).hom.toNatTrans.app M) ≫
              (eta.app (.mk (op Y))).toFunctor.map
                ((F.mapComp' (cover i₁).op.toLoc f₁.op.toLoc
                  q.op.toLoc hfg₁).inv.toNatTrans.app M) = 𝟙 _ := by
          rw [← Functor.map_comp]
          simp
        simp only [hF₁, hG₁, hF₂, hG₂]
        rw [← cancel_epi
          ((eta.naturality f₁.op.toLoc).hom.toNatTrans.app
            ((F.map (cover i₁).op.toLoc).toFunctor.obj M))]
        rw [← cancel_epi
          ((eta.app (.mk (op Y))).toFunctor.map
            ((F.mapComp' (cover i₁).op.toLoc f₁.op.toLoc
              q.op.toLoc hfg₁).hom.toNatTrans.app M))]
        simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
          ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
        rw [← StrongTrans.naturality_comp'_hom_app_assoc eta
          (cover i₁).op.toLoc f₁.op.toLoc q.op.toLoc hfg₁ M]
        rw [StrongTrans.naturality_comp'_hom_app eta
          (cover i₂).op.toLoc f₂.op.toLoc q.op.toLoc hfg₂ M]
        simp only [Functor.map_comp, Category.assoc,
          Cat.Hom.inv_hom_id_toNatTrans_app_assoc,
          Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
          Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
          Iso.inv_hom_id_app, Iso.hom_inv_id_app,
          Functor.map_id, Category.comp_id, Category.id_comp]
        slice_rhs 1 2 => exact hcancelF
        simp))
    (by
      intro M N h
      apply DescentData.hom_ext
      intro i
      dsimp [StrongTrans.mapDescentDataFunctor, StrongTrans.mapDescentData,
        Pseudofunctor.toDescentData, DescentData.ofObj]
      exact (Cat.Hom.toNatIso
        (eta.naturality (cover i).op.toLoc)).hom.naturality h)

@[simp]
theorem StrongTrans.toDescentDataMapIso_hom_hom (eta : StrongTrans F G)
    {ι : Type t} {S : C} {X : ι → C} (cover : ∀ i, X i ⟶ S)
    (M : F.obj (.mk (op S))) (i : ι) :
    ((eta.toDescentDataMapIso cover).app M).hom.hom i =
      (eta.naturality (cover i).op.toLoc).hom.toNatTrans.app M := rfl

@[simp]
theorem StrongTrans.toDescentDataMapIso_inv_hom (eta : StrongTrans F G)
    {ι : Type t} {S : C} {X : ι → C} (cover : ∀ i, X i ⟶ S)
    (M : F.obj (.mk (op S))) (i : ι) :
    ((eta.toDescentDataMapIso cover).app M).inv.hom i =
      (eta.naturality (cover i).op.toLoc).inv.toNatTrans.app M := rfl

end CategoryTheory.Pseudofunctor
