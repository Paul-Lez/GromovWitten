/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.Discrete
import GromovWitten.AlgebraicGeometry.Stacks.QuotientGeometryTrivialization
import GromovWitten.AlgebraicGeometry.Stacks.TorsorStackBundle

/-!
# Canonical points-to-quotient morphism

This file constructs the canonical strong transformation from the discrete stack of points of
`U` to the quotient stack `[U/G]`.  It keeps the source in the Hom-valued presentation of its
sheaf of points, so an object of a source fibre is already a map from a representable fppf sheaf.
The final theorem records fppf-local essential surjectivity of this transformation.
-/

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits CartesianMonoidalCategory
open CategoryTheory.Pseudofunctor
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open scoped CategoryTheory.MonoidalCategory
open Opposite
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace QuotientAtlas

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}

/-- The Hom-valued presheaf of points of an fppf sheaf. -/
noncomputable def points (X : FppfSheaf.{u}) : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) :=
  fppfYoneda.op ⋙ yoneda.obj X

/-- The Hom-valued presentation of points is naturally the universe lift of the sheaf itself. -/
noncomputable def pointsIso (X : FppfSheaf.{u}) :
    points X ≅ X.obj ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun T =>
    ((Scheme.fppfTopology.yonedaEquiv :
      (fppfYoneda.obj T.unop ⟶ X) ≃ X.obj.obj T).trans Equiv.ulift.symm).toIso) (by
        intro T S f
        ext a
        apply ULift.ext
        exact (Scheme.fppfTopology.yonedaEquiv_naturality' a f).symm)

theorem points_isSheaf (X : FppfSheaf.{u}) :
    Presieve.IsSheaf Scheme.fppfTopology (points X) := by
  apply Presieve.isSheaf_iso Scheme.fppfTopology (pointsIso X).symm
  apply Presieve.isSheaf_comp_uliftFunctor
  exact (isSheaf_iff_isSheaf_of_type _ _).mp X.property

/-- The source sheaf of points, with the fibre universe required by `LargeFppfStack`. -/
noncomputable def pointsSheaf (X : FppfSheaf.{u}) :
    Sheaf Scheme.fppfTopology (Type (u + 1)) :=
  ⟨points X, (isSheaf_iff_isSheaf_of_type _ _).2 (points_isSheaf X)⟩

/-- The discrete stack of points of `U`. -/
noncomputable def sourceStack :
    StackInGroupoids.{u, u + 1, u + 1, u + 1} Scheme.{u} fppfJ.{u} :=
  StackInGroupoids.ofSheafOfTypes fppfJ (pointsSheaf U.space.toSheaf)

@[simp]
theorem sourceStack_fiber (T : Scheme.{u}) :
    (sourceStack (G := G) (U := U)).toPseudofunctor.obj ⟨op T⟩ =
      Cat.of (Discrete ((points U.space.toSheaf).obj (op T))) :=
  rfl

/-- An object of the Hom-valued points fibre is the corresponding sheaf morphism. -/
noncomputable def pointHom (T : Scheme.{u})
    (x : Discrete ((points U.space.toSheaf).obj (op T))) :
    fppfYoneda.obj T ⟶ U.space.toSheaf :=
  x.as

theorem pointHom_map {T' T : Scheme.{u}} (b : T' ⟶ T)
    (x : Discrete ((points U.space.toSheaf).obj (op T))) :
    pointHom (G := G) (U := U) T'
        ⟨(points U.space.toSheaf).map b.op x.as⟩ =
      fppfYoneda.map b ≫ pointHom (G := G) (U := U) T x := by
  rfl

/-- The functor on a fibre sending a point to its trivial torsor. -/
noncomputable def appFunctor (T : Scheme.{u}) :
    Discrete ((points U.space.toSheaf).obj (op T)) ⥤ ActionTorsor G U T where
  obj x := ActionTorsor.trivialWithPoint (pointHom (G := G) (U := U) T x)
  map {x y} f := by
    have hxy : x = y := Discrete.ext (Discrete.eq_of_hom f)
    subst y
    exact 𝟙 _
  map_id x := by simp
  map_comp f g := by
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
    obtain rfl := Discrete.ext (Discrete.eq_of_hom g)
    simp

/-- The component of the quotient atlas on a fibre. -/
noncomputable def app (a : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    (sourceStack (G := G) (U := U)).toPseudofunctor.obj a ⟶
      (ActionTorsor.quotientStack G U).toPseudofunctor.obj a :=
  (appFunctor (G := G) (U := U) a.as.unop).toCatHom

/-- The distinguished section of the pullback of a trivial torsor. -/
noncomputable def pullbackTrivialSection {T' T : Scheme.{u}} (b : T' ⟶ T)
    (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    ActionTorsor.TorsorSection
      (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x)) where
  hom := Limits.pullback.lift
    (fppfYoneda.map b ≫ ActionTorsor.trivialSection G T)
    (𝟙 (fppfYoneda.obj T')) (by
      change (fppfYoneda.map b ≫ ActionTorsor.trivialSection G T) ≫
        (ActionTorsor.trivialWithPoint x).projection =
          𝟙 (fppfYoneda.obj T') ≫ fppfYoneda.map b
      rw [ActionTorsor.trivialWithPoint_projection, Category.assoc,
        ActionTorsor.trivialSection_snd]
      simp)

  over := Limits.pullback.lift_snd _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem pullbackTrivialSection_target {T' T : Scheme.{u}} (b : T' ⟶ T)
    (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (pullbackTrivialSection (G := G) (U := U) b x).hom ≫
        (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x)).target =
      fppfYoneda.map b ≫ x := by
  rw [ActionTorsor.pullbackObj_target, ActionTorsor.trivialWithPoint_target]
  simp only [pullbackTrivialSection]
  rw [← Category.assoc]
  simp only [Limits.pullback.lift_fst]
  have h := congrArg (fun z => fppfYoneda.map b ≫ z)
    (ActionTorsor.trivialSection_comp_target (G := G) (U := U) x)
  rw [ActionTorsor.trivialWithPoint_target] at h
  simpa only [Category.assoc] using h

/-- Pullback of the trivial torsor is canonically the trivial torsor of the pulled-back point. -/
noncomputable def pullbackTrivialIso {T' T : Scheme.{u}} (b : T' ⟶ T)
    (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    ActionTorsor.trivialWithPoint (fppfYoneda.map b ≫ x) ≅
      ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x) :=
  by
    let e := ActionTorsor.isoTrivialOfSection
      (P := ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x))
      (pullbackTrivialSection (G := G) (U := U) b x).hom
      (pullbackTrivialSection (G := G) (U := U) b x).over
    exact (eqToIso (congrArg (ActionTorsor.trivialWithPoint (G := G) (U := U))
      (pullbackTrivialSection_target (G := G) (U := U) b x).symm)).trans e

theorem trivialWithPoint_eqToHom_iso_hom {T : Scheme.{u}}
    {x y : fppfYoneda.obj T ⟶ U.space.toSheaf} (h : x = y) :
    (eqToHom (congrArg (ActionTorsor.trivialWithPoint (G := G) (U := U)) h)).iso.hom =
      𝟙 (G.space.toSheaf ⊗ fppfYoneda.obj T) := by
  subst y
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem pullbackTrivialIso_hom_iso_hom {T' T : Scheme.{u}} (b : T' ⟶ T)
    (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom =
      ActionTorsor.sectionMap
        (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x))
        (pullbackTrivialSection (G := G) (U := U) b x).hom := by
  simp only [pullbackTrivialIso, Iso.trans_hom, eqToIso.hom]
  rw [ActionTorsor.comp_iso_hom,
    trivialWithPoint_eqToHom_iso_hom
      (pullbackTrivialSection_target (G := G) (U := U) b x).symm]
  change 𝟙 _ ≫
    ActionTorsor.sectionMap
      (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x))
      (pullbackTrivialSection (G := G) (U := U) b x).hom = _
  exact Category.id_comp _

theorem pullbackTrivialIso_hom_section {T' T : Scheme.{u}} (b : T' ⟶ T)
    (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    ActionTorsor.trivialSection G T' ≫
        (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom =
      (pullbackTrivialSection (G := G) (U := U) b x).hom := by
  rw [pullbackTrivialIso_hom_iso_hom]
  exact ActionTorsor.trivialSection_comp_sectionMap _ _

theorem sectionMap_comp_hom {T : Scheme.{u}} (P Q : ActionTorsor G U T)
    (s : fppfYoneda.obj T ⟶ P.P) (f : P ⟶ Q) :
    ActionTorsor.sectionMap P s ≫ f.iso.hom =
      ActionTorsor.sectionMap Q (s ≫ f.iso.hom) := by
  simp only [ActionTorsor.sectionMap, Category.assoc]
  rw [f.equivariant, ← Category.assoc, MonoidalCategory.whiskerLeft_comp]

theorem pullbackTrivialSection_fst {T' T : Scheme.{u}} (b : T' ⟶ T)
    (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (pullbackTrivialSection (G := G) (U := U) b x).hom ≫
        Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection (fppfYoneda.map b) =
      fppfYoneda.map b ≫ ActionTorsor.trivialSection G T :=
  Limits.pullback.lift_fst _ _ _

theorem pullbackTrivialIso_id_hom {T : Scheme.{u}}
    (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (pullbackTrivialIso (G := G) (U := U) (𝟙 T) x).hom.iso.hom ≫
        (ActionTorsor.pullbackIdIsoApp (ActionTorsor.trivialWithPoint x)).hom.iso.hom =
      𝟙 (G.space.toSheaf ⊗ fppfYoneda.obj T) := by
  rw [pullbackTrivialIso_hom_iso_hom]
  change ActionTorsor.sectionMap
    (ActionTorsor.pullbackObj (𝟙 T) (ActionTorsor.trivialWithPoint x))
    (pullbackTrivialSection (G := G) (U := U) (𝟙 T) x).hom ≫
      (ActionTorsor.pullbackIdIsoApp (ActionTorsor.trivialWithPoint x)).hom.iso.hom =
        𝟙 (G.space.toSheaf ⊗ fppfYoneda.obj T)
  rw [sectionMap_comp_hom]
  have hs : (pullbackTrivialSection (G := G) (U := U) (𝟙 T) x).hom ≫
      (ActionTorsor.pullbackIdIsoApp (ActionTorsor.trivialWithPoint x)).hom.iso.hom =
        ActionTorsor.trivialSection G T := by
    change (pullbackTrivialSection (G := G) (U := U) (𝟙 T) x).hom ≫
      Limits.pullback.fst _ _ = _
    exact (pullbackTrivialSection_fst (G := G) (U := U) (𝟙 T) x).trans
      ((congrArg (fun k => k ≫ ActionTorsor.trivialSection G T)
        (fppfYoneda.map_id T)).trans (Category.id_comp _))
  rw [hs]
  have h := ActionTorsor.sectionMap_of_hom (ActionTorsor.trivialWithPoint x) x
    (𝟙 (ActionTorsor.trivialWithPoint x))
  change ActionTorsor.sectionMap (ActionTorsor.trivialWithPoint x)
    (ActionTorsor.trivialSection G T ≫ 𝟙 (G.space.toSheaf ⊗ fppfYoneda.obj T)) =
      𝟙 (G.space.toSheaf ⊗ fppfYoneda.obj T) at h
  exact (congrArg (ActionTorsor.sectionMap (ActionTorsor.trivialWithPoint x))
    (Category.comp_id (ActionTorsor.trivialSection G T))).symm.trans h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem pullbackTrivialIso_comp_hom {T T' T'' : Scheme.{u}} (a : T'' ⟶ T') (b : T' ⟶ T)
    (x : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (pullbackTrivialIso (G := G) (U := U) (a ≫ b) x).hom.iso.hom ≫
        (ActionTorsor.pullbackCompIsoApp a b
          (ActionTorsor.trivialWithPoint x)).hom.iso.hom =
      (pullbackTrivialIso (G := G) (U := U) a (fppfYoneda.map b ≫ x)).hom.iso.hom ≫
      ((ActionTorsor.pullbackFunctor a).map
          (pullbackTrivialIso (G := G) (U := U) b x).hom).iso.hom := by
  rw [pullbackTrivialIso_hom_iso_hom]
  let c := ActionTorsor.pullbackCompIsoApp a b
      (ActionTorsor.trivialWithPoint x)
  have hL := sectionMap_comp_hom
    (ActionTorsor.pullbackObj (a ≫ b) (ActionTorsor.trivialWithPoint x))
    (ActionTorsor.pullbackObj a
      (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x)))
    (pullbackTrivialSection (G := G) (U := U) (a ≫ b) x).hom c.hom
  rw [pullbackTrivialIso_hom_iso_hom]
  let d := (ActionTorsor.pullbackFunctor a).map
    (pullbackTrivialIso (G := G) (U := U) b x).hom
  have hR := sectionMap_comp_hom
    (ActionTorsor.pullbackObj a
      (ActionTorsor.trivialWithPoint (fppfYoneda.map b ≫ x)))
    (ActionTorsor.pullbackObj a
      (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x)))
    (pullbackTrivialSection (G := G) (U := U) a (fppfYoneda.map b ≫ x)).hom d
  have hs :
      (pullbackTrivialSection (G := G) (U := U) (a ≫ b) x).hom ≫ c.hom.iso.hom =
        (pullbackTrivialSection (G := G) (U := U) a (fppfYoneda.map b ≫ x)).hom ≫
          d.iso.hom := by
    have hmap :
        FppfTorsor.pullbackMap a
            (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom
            (pullbackTrivialIso (G := G) (U := U) b x).hom.over ≫
          Limits.pullback.fst
            (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x)).projection
            (fppfYoneda.map a) =
        Limits.pullback.fst
            (ActionTorsor.trivialWithPoint (fppfYoneda.map b ≫ x)).projection
            (fppfYoneda.map a) ≫
          (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom := by
      exact FppfTorsor.pullbackMap_fst _ _ _
    have hc :
        c.hom.iso.hom ≫
            Limits.pullback.fst
              (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x)).projection
              (fppfYoneda.map a) ≫
            Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
              (fppfYoneda.map b) =
          Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
            (fppfYoneda.map (a ≫ b)) := by
      change
        (FppfTorsor.pullbackCompIso
            (ActionTorsor.trivialWithPoint x).toFppfTorsor a b).hom ≫
            Limits.pullback.fst
              (Limits.pullback.snd
                (ActionTorsor.trivialWithPoint x).projection (fppfYoneda.map b))
              (fppfYoneda.map a) ≫
            Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
              (fppfYoneda.map b) =
          Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
            (fppfYoneda.map (a ≫ b))
      exact FppfTorsor.pullbackCompIso_hom_fst_fst _ _ _
    have hqsec :
        ActionTorsor.trivialSection G T' ≫
            (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom =
          (pullbackTrivialSection (G := G) (U := U) b x).hom :=
      pullbackTrivialIso_hom_section (G := G) (U := U) b x
    have ha :
        (pullbackTrivialSection (G := G) (U := U) a
            (fppfYoneda.map b ≫ x)).hom ≫
            Limits.pullback.fst
              (ActionTorsor.trivialWithPoint (fppfYoneda.map b ≫ x)).projection
              (fppfYoneda.map a) =
          fppfYoneda.map a ≫ ActionTorsor.trivialSection G T' :=
      pullbackTrivialSection_fst (G := G) (U := U) a (fppfYoneda.map b ≫ x)
    have hb :
        (pullbackTrivialSection (G := G) (U := U) b x).hom ≫
            Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
              (fppfYoneda.map b) =
          fppfYoneda.map b ≫
            (ActionTorsor.trivialSection G T :
              fppfYoneda.obj T ⟶ (ActionTorsor.trivialWithPoint x).P) := by
      exact pullbackTrivialSection_fst (G := G) (U := U) b x
    apply Limits.pullback.hom_ext
    · apply Limits.pullback.hom_ext
      · simp only [Category.assoc, c,
          ActionTorsor.pullbackCompIsoApp_hom_iso_hom,
          FppfTorsor.pullbackCompIso_hom_fst_fst,
          pullbackTrivialSection_fst,
          d, FppfTorsor.pullbackMapIso_hom]
        have hr :
            (pullbackTrivialSection (G := G) (U := U) a
                (fppfYoneda.map b ≫ x)).hom ≫
                d.iso.hom ≫
                Limits.pullback.fst
                  (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x)).projection
                  (fppfYoneda.map a) ≫
                Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                  (fppfYoneda.map b) =
              fppfYoneda.map a ≫ fppfYoneda.map b ≫
                ActionTorsor.trivialSection G T := by
          change (pullbackTrivialSection (G := G) (U := U) a
              (fppfYoneda.map b ≫ x)).hom ≫
              (FppfTorsor.pullbackMap a
                (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom
                (pullbackTrivialIso (G := G) (U := U) b x).hom.over) ≫
              Limits.pullback.fst
                (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x)).projection
                (fppfYoneda.map a) ≫
              Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                (fppfYoneda.map b) = _
          calc
            (pullbackTrivialSection (G := G) (U := U) a
                (fppfYoneda.map b ≫ x)).hom ≫
                (FppfTorsor.pullbackMap a
                  (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom
                  (pullbackTrivialIso (G := G) (U := U) b x).hom.over) ≫
                Limits.pullback.fst
                  (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x)).projection
                  (fppfYoneda.map a) ≫
                Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                  (fppfYoneda.map b)
              = (pullbackTrivialSection (G := G) (U := U) a
                (fppfYoneda.map b ≫ x)).hom ≫
                (FppfTorsor.pullbackMap a
                  (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom
                  (pullbackTrivialIso (G := G) (U := U) b x).hom.over ≫
                  Limits.pullback.fst
                    (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x)).projection
                    (fppfYoneda.map a)) ≫
                Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                  (fppfYoneda.map b) := by simp only [Category.assoc]
            _ = (pullbackTrivialSection (G := G) (U := U) a
                (fppfYoneda.map b ≫ x)).hom ≫
                (Limits.pullback.fst
                  (ActionTorsor.trivialWithPoint (fppfYoneda.map b ≫ x)).projection
                  (fppfYoneda.map a) ≫
                  (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom) ≫
                Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                  (fppfYoneda.map b) := by rw [hmap]
            _ = ((pullbackTrivialSection (G := G) (U := U) a
                (fppfYoneda.map b ≫ x)).hom ≫
                Limits.pullback.fst
                  (ActionTorsor.trivialWithPoint (fppfYoneda.map b ≫ x)).projection
                  (fppfYoneda.map a)) ≫
                (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom ≫
                Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                  (fppfYoneda.map b) := by simp only [Category.assoc]
            _ = ((fppfYoneda.map a ≫ ActionTorsor.trivialSection G T') ≫
                (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom) ≫
                Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                  (fppfYoneda.map b) := by
              rw [← Category.assoc]
              exact congrArg (fun k => k ≫
                (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom ≫
                Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                  (fppfYoneda.map b)) ha
            _ = (fppfYoneda.map a ≫
                (ActionTorsor.trivialSection G T' ≫
                  (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom)) ≫
                Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                  (fppfYoneda.map b) := by
              exact congrArg (fun k => k ≫
                  Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                    (fppfYoneda.map b))
                (Category.assoc (fppfYoneda.map a)
                  (ActionTorsor.trivialSection G T')
                  (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom)
            _ = fppfYoneda.map a ≫
                ((pullbackTrivialSection (G := G) (U := U) b x).hom ≫
                  Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                    (fppfYoneda.map b)) := by
              simpa only [Category.assoc] using
                congrArg (fun k => fppfYoneda.map a ≫ k ≫
                  Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                    (fppfYoneda.map b)) hqsec
            fppfYoneda.map a ≫
                ((pullbackTrivialSection (G := G) (U := U) b x).hom ≫
                  Limits.pullback.fst (ActionTorsor.trivialWithPoint x).projection
                    (fppfYoneda.map b)) =
              fppfYoneda.map a ≫ fppfYoneda.map b ≫
                (ActionTorsor.trivialSection G T :
                  fppfYoneda.obj T ⟶ (ActionTorsor.trivialWithPoint x).P) := by
              rw [hb]
        have hcomp : fppfYoneda.map (a ≫ b) ≫
              (ActionTorsor.trivialSection G T :
                fppfYoneda.obj T ⟶ (ActionTorsor.trivialWithPoint x).P) =
            fppfYoneda.map a ≫ fppfYoneda.map b ≫
              (ActionTorsor.trivialSection G T :
                fppfYoneda.obj T ⟶ (ActionTorsor.trivialWithPoint x).P) := by
          rw [fppfYoneda.map_comp]
          exact Category.assoc _ _ _
        exact hcomp.trans hr.symm
      · have hl := congrArg
          (fun z => (pullbackTrivialSection (G := G) (U := U) (a ≫ b) x).hom ≫ z)
          (FppfTorsor.pullbackCompIso_hom_fst_snd
            (ActionTorsor.trivialWithPoint x).toFppfTorsor a b)
        have hr := congrArg
          (fun z => (pullbackTrivialSection (G := G) (U := U) a
            (fppfYoneda.map b ≫ x)).hom ≫ z ≫
              Limits.pullback.snd (ActionTorsor.trivialWithPoint x).projection
                (fppfYoneda.map b)) hmap
        calc
          _ = (pullbackTrivialSection (G := G) (U := U) (a ≫ b) x).hom ≫
              Limits.pullback.snd (ActionTorsor.trivialWithPoint x).projection
                (fppfYoneda.map (a ≫ b)) ≫ fppfYoneda.map a := by
            simpa only [Category.assoc, c,
              ActionTorsor.pullbackCompIsoApp_hom_iso_hom] using hl
          _ = fppfYoneda.map a := by
            rw [← Category.assoc,
              (pullbackTrivialSection (G := G) (U := U) (a ≫ b) x).over,
              Category.id_comp]
          _ = (pullbackTrivialSection (G := G) (U := U) a
              (fppfYoneda.map b ≫ x)).hom ≫
                Limits.pullback.fst
                  (ActionTorsor.trivialWithPoint (fppfYoneda.map b ≫ x)).projection
                  (fppfYoneda.map a) ≫
                (ActionTorsor.trivialWithPoint (fppfYoneda.map b ≫ x)).projection := by
            rw [Limits.pullback.condition, ← Category.assoc,
              (pullbackTrivialSection (G := G) (U := U) a
                (fppfYoneda.map b ≫ x)).over, Category.id_comp]
          _ = (pullbackTrivialSection (G := G) (U := U) a
              (fppfYoneda.map b ≫ x)).hom ≫
                Limits.pullback.fst
                  (ActionTorsor.trivialWithPoint (fppfYoneda.map b ≫ x)).projection
                  (fppfYoneda.map a) ≫
                (pullbackTrivialIso (G := G) (U := U) b x).hom.iso.hom ≫
                Limits.pullback.snd (ActionTorsor.trivialWithPoint x).projection
                  (fppfYoneda.map b) := by
            rw [(pullbackTrivialIso (G := G) (U := U) b x).hom.over]
          _ = _ := by
            simpa only [Category.assoc, d, ActionTorsor.pullbackFunctor_map_iso_hom,
              FppfTorsor.pullbackMapIso_hom] using hr.symm
    · simp only [Category.assoc]
      rw [c.hom.over,
        (pullbackTrivialSection (G := G) (U := U) (a ≫ b) x).over,
        d.over,
        (pullbackTrivialSection (G := G) (U := U) a (fppfYoneda.map b ≫ x)).over]
  calc
    _ = (ActionTorsor.pullbackObj a
      (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x))).sectionMap
        ((pullbackTrivialSection (G := G) (U := U) (a ≫ b) x).hom ≫ c.hom.iso.hom) := hL
    _ = (ActionTorsor.pullbackObj a
      (ActionTorsor.pullbackObj b (ActionTorsor.trivialWithPoint x))).sectionMap
        ((pullbackTrivialSection (G := G) (U := U) a (fppfYoneda.map b ≫ x)).hom ≫
          d.iso.hom) := congrArg _ hs
    _ = _ := hR.symm

/-- The pullback comparison, assembled as the naturality cell of the atlas. -/
noncomputable def appNaturality {a b : LocallyDiscrete Scheme.{u}ᵒᵖ} (f : a ⟶ b) :
    (sourceStack (G := G) (U := U)).toPseudofunctor.map f ≫ app (G := G) (U := U) b ≅
      app (G := G) (U := U) a ≫
        (ActionTorsor.quotientStack G U).toPseudofunctor.map f := by
  apply Cat.Hom.isoMk
  refine NatIso.ofComponents (fun x ↦ ?_) ?_
  · let y : Discrete ((points U.space.toSheaf).obj b.as) :=
      ⟨(points U.space.toSheaf).map f.as x.as⟩
    change (appFunctor (G := G) (U := U) b.as.unop).obj y ≅
      ActionTorsor.pullbackObj f.as.unop
        ((appFunctor (G := G) (U := U) a.as.unop).obj x)
    have hy := pointHom_map (G := G) (U := U) f.as.unop x
    simpa only [appFunctor, y, Quiver.Hom.op_unop] using
      (eqToIso (congrArg (ActionTorsor.trivialWithPoint (G := G) (U := U)) hy)).trans
        (pullbackTrivialIso (G := G) (U := U) f.as.unop
          (pointHom (G := G) (U := U) a.as.unop x))
  · intro x y h
    have hxy : x = y := Discrete.ext (Discrete.eq_of_hom h)
    subst y
    have hh : h = 𝟙 x := by
      change @Eq (ULift (PLift (_ = _))) _ _
      apply Subsingleton.elim
    rw [hh]
    simp

/- The explicit transparency setting is needed when reducing the fibre casts in the coherence
   equations. -/
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- The explicit fibre normalization in the composition coherence needs this reduction budget.
/-- The canonical points-to-quotient strong transformation. -/
noncomputable def strongTrans :
    Pseudofunctor.StrongTrans (sourceStack (G := G) (U := U)).toPseudofunctor
      (ActionTorsor.quotientStack G U).toPseudofunctor where
  app a := app (G := G) (U := U) a
  naturality f := appNaturality (G := G) (U := U) f
  naturality_naturality {a b f g} η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 f := by
      change @Eq (ULift (PLift (_ = _))) _ _
      apply Subsingleton.elim
    rw [hη]
    apply Cat.Hom₂.ext
    ext x
    simp
  naturality_id a := by
    apply Cat.Hom₂.ext
    ext x
    change Discrete ((points U.space.toSheaf).obj a.as) at x
    apply ActionTorsor.Hom.ext
    change
      (𝟙 _ ≫ (pullbackTrivialIso (G := G) (U := U) (𝟙 a.as.unop)
        (pointHom (G := G) (U := U) a.as.unop x)).hom.iso.hom) ≫
          (ActionTorsor.pullbackIdIsoApp
            (ActionTorsor.trivialWithPoint (pointHom (G := G) (U := U) a.as.unop x))).hom.iso.hom =
        𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    rw [Category.id_comp, Category.id_comp, Category.comp_id]
    exact pullbackTrivialIso_id_hom (G := G) (U := U)
      (pointHom (G := G) (U := U) a.as.unop x)

  naturality_comp {a b c} f g := by
    apply Cat.Hom₂.ext
    ext x
    change Discrete ((points U.space.toSheaf).obj _) at x
    apply ActionTorsor.Hom.ext
    change
      (𝟙 _ ≫
        (pullbackTrivialIso (G := G) (U := U) (g.as.unop ≫ f.as.unop)
          (pointHom (G := G) (U := U) a.as.unop x)).hom.iso.hom) ≫
        (ActionTorsor.pullbackCompIsoApp g.as.unop f.as.unop
          (ActionTorsor.trivialWithPoint
            (pointHom (G := G) (U := U) a.as.unop x))).hom.iso.hom =
      (pullbackTrivialIso (G := G) (U := U) g.as.unop
        (fppfYoneda.map f.as.unop ≫ pointHom (G := G) (U := U) a.as.unop x)).hom.iso.hom ≫
        ((ActionTorsor.pullbackFunctor (U := U) g.as.unop).map
          (pullbackTrivialIso (G := G) (U := U) f.as.unop
            (pointHom (G := G) (U := U) a.as.unop x)).hom).iso.hom
    rw [Category.id_comp]
    exact pullbackTrivialIso_comp_hom (G := G) (U := U)
      g.as.unop f.as.unop (pointHom (G := G) (U := U) a.as.unop x)

/-- Every quotient-stack object becomes one of the atlas objects over its specified fppf cover. -/
theorem localEssentialSurjectivity (T : Scheme.{u}) (P : ActionTorsor G U T) :
    ∃ (T' : Scheme.{u}) (b : T' ⟶ T)
      (_ : _root_.AlgebraicGeometry.Flat b)
      (_ : _root_.AlgebraicGeometry.LocallyOfFinitePresentation b)
      (_ : _root_.AlgebraicGeometry.Surjective b)
      (x : fppfYoneda.obj T' ⟶ U.space.toSheaf),
      Nonempty (ActionTorsor.trivialWithPoint x ≅ ActionTorsor.pullbackObj b P) := by
  let T' := P.locallyTrivial.coverScheme
  let b := P.locallyTrivial.cover
  let σ : ActionTorsor.TorsorSection (ActionTorsor.pullbackObj b P) :=
    ⟨Limits.pullback.lift P.locallyTrivial.localLift (𝟙 _)
      (by rw [P.locallyTrivial.localLift_over, Category.id_comp]),
      Limits.pullback.lift_snd _ _ _⟩
  refine ⟨T', b, P.locallyTrivial.flat, P.locallyTrivial.locallyOfFinitePresentation,
    P.locallyTrivial.surjective, σ.hom ≫ (ActionTorsor.pullbackObj b P).target, ?_⟩
  exact ⟨ActionTorsor.isoTrivialOfSection (P := ActionTorsor.pullbackObj b P) σ.hom σ.over⟩

/-- Maps from a fibre point of the atlas are exactly sections of the target torsor with the
    prescribed map to `U`. -/
noncomputable def fibreHomSectionEquiv (T : Scheme.{u})
    (x : Discrete ((points U.space.toSheaf).obj (op T))) (P : ActionTorsor G U T) :
    ((appFunctor (G := G) (U := U) T).obj x ⟶ P) ≃
      {s : ActionTorsor.TorsorSection P //
        s.hom ≫ P.target = pointHom (G := G) (U := U) T x} :=
  ActionTorsor.homSectionEquiv P (pointHom (G := G) (U := U) T x)

end QuotientAtlas

end GromovWitten.AlgebraicGeometry
