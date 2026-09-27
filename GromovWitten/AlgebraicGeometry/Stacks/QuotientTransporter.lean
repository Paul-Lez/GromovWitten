/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientGeometryTrivialization
import GromovWitten.AlgebraicGeometry.Spaces.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Transporters for quotient actions

For `x,y : T ⟶ U`, the transporter is the pullback of the action graph.  The exported
`actionGraph` uses `(u,g • u)`, while `reverseActionGraph` uses `(g • u,u)`.  The latter is
the convenient orientation for left torsors: an equivariant map between left trivial torsors
is right multiplication, so an arrow from `x` to `y` is labelled by `g` with `g • y = x`.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace QuotientTransporter

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}
  {T : Scheme.{u}}

noncomputable def actionGraph :
    G.space.toSheaf ⊗ U.space.toSheaf ⟶ U.space.toSheaf ⨯ U.space.toSheaf :=
  prod.lift (snd _ _)
    (ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf))

noncomputable def reverseActionGraph :
    G.space.toSheaf ⊗ U.space.toSheaf ⟶ U.space.toSheaf ⨯ U.space.toSheaf :=
  prod.lift (ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) (snd _ _)

@[reassoc (attr := simp)]
theorem actionGraph_fst :
    actionGraph (G := G) (U := U) ≫ prod.fst = snd _ _ :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem actionGraph_snd :
    actionGraph (G := G) (U := U) ≫ prod.snd =
      ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) :=
  prod.lift_snd _ _

@[reassoc (attr := simp)]
theorem reverseActionGraph_fst :
    reverseActionGraph (G := G) (U := U) ≫ prod.fst =
      ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem reverseActionGraph_snd :
    reverseActionGraph (G := G) (U := U) ≫ prod.snd = snd _ _ :=
  prod.lift_snd _ _

noncomputable def pointPair (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    fppfYoneda.obj T ⟶ U.space.toSheaf ⨯ U.space.toSheaf :=
  prod.lift x y

@[reassoc (attr := simp)]
theorem pointPair_fst (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    pointPair (T := T) x y ≫ prod.fst = x :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem pointPair_snd (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    pointPair (T := T) x y ≫ prod.snd = y :=
  prod.lift_snd _ _

/-- The sheaf of elements carrying `y` to `x`. -/
noncomputable def sheaf (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) : FppfSheaf.{u} :=
  pullback (reverseActionGraph (G := G) (U := U)) (pointPair x y)

noncomputable def projection (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    sheaf (G := G) (U := U) x y ⟶ fppfYoneda.obj T :=
  pullback.snd _ _

noncomputable def graphLift (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    sheaf (G := G) (U := U) x y ⟶ G.space.toSheaf ⊗ U.space.toSheaf :=
  pullback.fst _ _

theorem pointPair_precomp {T' : Scheme.{u}} (b : T' ⟶ T)
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    fppfYoneda.map b ≫ pointPair x y =
      pointPair (fppfYoneda.map b ≫ x) (fppfYoneda.map b ≫ y) := by
  apply prod.hom_ext <;> simp

@[reassoc (attr := simp)]
theorem graphLift_condition (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    graphLift (G := G) (U := U) x y ≫ reverseActionGraph (G := G) (U := U) =
      projection (G := G) (U := U) x y ≫ pointPair x y :=
  pullback.condition

@[reassoc (attr := simp)]
theorem graphLift_smul (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    graphLift (G := G) (U := U) x y ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) =
      projection (G := G) (U := U) x y ≫ x := by
  have h := congrArg (fun k ↦ k ≫ prod.fst)
    (graphLift_condition (G := G) (U := U) x y)
  simpa only [Category.assoc, reverseActionGraph_fst, pointPair_fst] using h

@[reassoc (attr := simp)]
theorem graphLift_snd (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    graphLift (G := G) (U := U) x y ≫ snd _ _ =
      projection (G := G) (U := U) x y ≫ y := by
  have h := congrArg (fun k ↦ k ≫ prod.snd)
    (graphLift_condition (G := G) (U := U) x y)
  simpa only [Category.assoc, reverseActionGraph_snd, pointPair_snd] using h

/-! ### Sections of the actual transporter sheaf -/

structure Section (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) where
  hom : fppfYoneda.obj T ⟶ sheaf (G := G) (U := U) x y
  over : hom ≫ projection (G := G) (U := U) x y = 𝟙 _

@[ext]
theorem Section.ext {x y : fppfYoneda.obj T ⟶ U.space.toSheaf}
    (s₁ s₂ : Section (G := G) (U := U) x y) (h : s₁.hom = s₂.hom) : s₁ = s₂ := by
  cases s₁
  cases s₂
  simp only [Section.mk.injEq]
  exact h

theorem Section.graph_fst {x y : fppfYoneda.obj T ⟶ U.space.toSheaf}
    (s : Section (G := G) (U := U) x y) :
    s.hom ≫ graphLift (G := G) (U := U) x y ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) = x := by
  rw [graphLift_smul, ← Category.assoc, s.over, Category.id_comp]

theorem Section.graph_snd {x y : fppfYoneda.obj T ⟶ U.space.toSheaf}
    (s : Section (G := G) (U := U) x y) :
    s.hom ≫ graphLift (G := G) (U := U) x y ≫ snd _ _ = y := by
  rw [graphLift_snd, ← Category.assoc, s.over, Category.id_comp]

/-! The following maps are the concrete bridge to `homSectionEquiv` from
`QuotientGeometryTrivialization`. -/

noncomputable def torsorHom
    (y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : ActionTorsor.TorsorSection (ActionTorsor.trivialWithPoint y)) :
    fppfYoneda.obj T ⟶ G.space.toSheaf ⊗ fppfYoneda.obj T := by
  simpa only [ActionTorsor.trivialWithPoint, FppfTorsor.trivial] using s.hom

theorem torsorHom_over
    (y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : ActionTorsor.TorsorSection (ActionTorsor.trivialWithPoint y)) :
    torsorHom (G := G) (U := U) y s ≫ snd _ _ = 𝟙 _ := by
  simpa only [torsorHom, ActionTorsor.trivialWithPoint, FppfTorsor.trivial] using s.over

theorem torsorHom_target
    (y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : ActionTorsor.TorsorSection (ActionTorsor.trivialWithPoint y)) :
    torsorHom (G := G) (U := U) y s ≫
        ((G.space.toSheaf ◁ y) ≫
          ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) =
      s.hom ≫ (ActionTorsor.trivialWithPoint y).target := by
  rfl

noncomputable def sectionPoint
    (y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : ActionTorsor.TorsorSection (ActionTorsor.trivialWithPoint y)) :
    fppfYoneda.obj T ⟶ G.space.toSheaf ⊗ U.space.toSheaf :=
  lift (torsorHom (G := G) (U := U) y s ≫ fst _ _) y

theorem sectionPoint_smul
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : ActionTorsor.TorsorSection (ActionTorsor.trivialWithPoint y))
    (hs : s.hom ≫ (ActionTorsor.trivialWithPoint y).target = x) :
    sectionPoint (G := G) (U := U) y s ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) = x := by
  have hpoint :
      sectionPoint (G := G) (U := U) y s ≫
          ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) =
        s.hom ≫ (ActionTorsor.trivialWithPoint y).target := by
    have hy : torsorHom (G := G) (U := U) y s ≫ snd _ _ ≫ y = y := by
      rw [← Category.assoc, torsorHom_over, Category.id_comp]
    rw [← torsorHom_target, sectionPoint,
      QuotientGeometryTrivialization.whiskerLeft_eq_lift,
      ← Category.assoc, comp_lift, hy]
  exact hpoint.trans hs

noncomputable def sectionOfTorsorSection
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : ActionTorsor.TorsorSection (ActionTorsor.trivialWithPoint y))
    (hs : s.hom ≫ (ActionTorsor.trivialWithPoint y).target = x) :
    Section (G := G) (U := U) x y where
  hom := pullback.lift (sectionPoint (G := G) (U := U) y s) (𝟙 _) (by
    apply prod.hom_ext
    · rw [Category.assoc, reverseActionGraph_fst, sectionPoint_smul x y s hs,
        Category.assoc, pointPair_fst, Category.id_comp]
    · rw [Category.assoc, reverseActionGraph_snd, sectionPoint, lift_snd,
        Category.assoc, pointPair_snd, Category.id_comp])
  over := pullback.lift_snd _ _ _

noncomputable def torsorSectionOfSection
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : Section (G := G) (U := U) x y) :
    ActionTorsor.TorsorSection (ActionTorsor.trivialWithPoint y) where
  hom := by
    simpa only [ActionTorsor.trivialWithPoint, FppfTorsor.trivial] using
      (lift (s.hom ≫ graphLift (G := G) (U := U) x y ≫ fst _ _) (𝟙 _))
  over := by
    change lift (s.hom ≫ graphLift (G := G) (U := U) x y ≫ fst _ _) (𝟙 _) ≫
      snd _ _ = 𝟙 _
    rw [lift_snd]

theorem torsorSectionOfSection_target
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : Section (G := G) (U := U) x y) :
    (torsorSectionOfSection (G := G) (U := U) x y s).hom ≫
        (ActionTorsor.trivialWithPoint y).target = x := by
  change lift (s.hom ≫ graphLift (G := G) (U := U) x y ≫ fst _ _) (𝟙 _) ≫
      ((G.space.toSheaf ◁ y) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) = x
  have hq : lift (s.hom ≫ graphLift (G := G) (U := U) x y ≫ fst _ _) y =
      s.hom ≫ graphLift (G := G) (U := U) x y := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [lift_fst, Category.assoc]
    · rw [lift_snd]
      simpa only [Category.assoc] using (Section.graph_snd s).symm
  rw [QuotientGeometryTrivialization.lift_whiskerLeft_assoc,
    Category.id_comp, hq]
  simpa only [Category.assoc] using Section.graph_fst s

theorem sectionPoint_torsorSectionOfSection
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : Section (G := G) (U := U) x y) :
    sectionPoint (G := G) (U := U) y
        (torsorSectionOfSection (G := G) (U := U) x y s) =
      s.hom ≫ graphLift (G := G) (U := U) x y := by
  rw [sectionPoint]
  apply CartesianMonoidalCategory.hom_ext
  · change lift (s.hom ≫ graphLift (G := G) (U := U) x y ≫ fst _ _) (𝟙 _) ≫
        fst _ _ = s.hom ≫ graphLift (G := G) (U := U) x y ≫ fst _ _
    rw [lift_fst]
  · rw [lift_snd]
    simpa only [Category.assoc] using (Section.graph_snd s).symm

noncomputable def sectionTorsorSectionEquiv
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    Section (G := G) (U := U) x y ≃
      {s : ActionTorsor.TorsorSection (ActionTorsor.trivialWithPoint y) //
        s.hom ≫ (ActionTorsor.trivialWithPoint y).target = x} where
  toFun s :=
    ⟨torsorSectionOfSection (G := G) (U := U) x y s,
      torsorSectionOfSection_target (G := G) (U := U) x y s⟩
  invFun s := sectionOfTorsorSection (G := G) (U := U) x y s.1 s.2
  left_inv s := by
    apply Section.ext
    change (sectionOfTorsorSection (G := G) (U := U) x y
        (torsorSectionOfSection (G := G) (U := U) x y s)
        (torsorSectionOfSection_target (G := G) (U := U) x y s)).hom = s.hom
    dsimp [sectionOfTorsorSection]
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      change sectionPoint (G := G) (U := U) y
          (torsorSectionOfSection (G := G) (U := U) x y s) =
        s.hom ≫ graphLift (G := G) (U := U) x y
      exact sectionPoint_torsorSectionOfSection (G := G) (U := U) x y s
    · rw [pullback.lift_snd]
      change 𝟙 _ = s.hom ≫ projection (G := G) (U := U) x y
      exact s.over.symm
  right_inv s := by
    apply Subtype.ext
    apply ActionTorsor.TorsorSection.ext
    have hgraph :
        (sectionOfTorsorSection (G := G) (U := U) x y s.1 s.2).hom ≫
            graphLift (G := G) (U := U) x y =
          sectionPoint (G := G) (U := U) y s.1 := by
      dsimp [sectionOfTorsorSection]
      unfold sheaf
      unfold graphLift
      rw [pullback.lift_fst]
    have hnorm :
        lift (((sectionOfTorsorSection (G := G) (U := U) x y s.1 s.2).hom ≫
          graphLift (G := G) (U := U) x y) ≫ fst _ _) (𝟙 _) =
          torsorHom (G := G) (U := U) y s.1 := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, hgraph, sectionPoint]
        simp only [lift_fst]
      · rw [lift_snd]
        exact (torsorHom_over (G := G) (U := U) y s.1).symm
    simpa only [torsorSectionOfSection, ActionTorsor.trivialWithPoint,
      FppfTorsor.trivial, torsorHom, id_eq, Category.assoc] using hnorm

/-! The transporter section/arrow correspondence has the arrow orientation inherited from
`ActionTorsor.homSectionEquiv`: an arrow from `x` to `y` is labelled by `g` satisfying
`g • y = x`. -/
noncomputable def homSectionEquiv
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (ActionTorsor.trivialWithPoint x ⟶ ActionTorsor.trivialWithPoint y) ≃
      Section (G := G) (U := U) x y :=
  (ActionTorsor.homSectionEquiv (P := ActionTorsor.trivialWithPoint y) x).trans
    (sectionTorsorSectionEquiv (G := G) (U := U) x y).symm

noncomputable def sectionOfArrow
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (f : ActionTorsor.trivialWithPoint x ⟶ ActionTorsor.trivialWithPoint y) :
    Section (G := G) (U := U) x y :=
  homSectionEquiv (G := G) (U := U) x y f

noncomputable def arrowOfSection
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : Section (G := G) (U := U) x y) :
    ActionTorsor.trivialWithPoint x ⟶ ActionTorsor.trivialWithPoint y :=
  (homSectionEquiv (G := G) (U := U) x y).symm s

@[simp]
theorem sectionOfArrow_arrowOfSection
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (s : Section (G := G) (U := U) x y) :
    sectionOfArrow (G := G) (U := U) x y (arrowOfSection (G := G) (U := U) x y s) = s :=
  (homSectionEquiv (G := G) (U := U) x y).apply_symm_apply s

@[simp]
theorem arrowOfSection_sectionOfArrow
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (f : ActionTorsor.trivialWithPoint x ⟶ ActionTorsor.trivialWithPoint y) :
    arrowOfSection (G := G) (U := U) x y (sectionOfArrow (G := G) (U := U) x y f) = f :=
  (homSectionEquiv (G := G) (U := U) x y).symm_apply_apply f

/-! ### Base change of the same transporter sheaf -/

noncomputable def baseChangeMap {T' : Scheme.{u}} (b : T' ⟶ T)
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    sheaf (G := G) (U := U) (fppfYoneda.map b ≫ x) (fppfYoneda.map b ≫ y) ⟶
      sheaf (G := G) (U := U) x y :=
  pullback.lift
    (graphLift (G := G) (U := U) (fppfYoneda.map b ≫ x) (fppfYoneda.map b ≫ y))
    (projection (G := G) (U := U) (fppfYoneda.map b ≫ x) (fppfYoneda.map b ≫ y) ≫
      fppfYoneda.map b)
    (by
      rw [graphLift_condition]
      simp only [Category.assoc]
      rw [← pointPair_precomp])

@[reassoc (attr := simp)]
theorem baseChangeMap_projection {T' : Scheme.{u}} (b : T' ⟶ T)
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    baseChangeMap (G := G) (U := U) b x y ≫ projection (G := G) (U := U) x y =
      projection (G := G) (U := U) (fppfYoneda.map b ≫ x) (fppfYoneda.map b ≫ y) ≫
        fppfYoneda.map b := by
  apply pullback.lift_snd

@[reassoc (attr := simp)]
theorem baseChangeMap_graphLift {T' : Scheme.{u}} (b : T' ⟶ T)
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    baseChangeMap (G := G) (U := U) b x y ≫ graphLift (G := G) (U := U) x y =
      graphLift (G := G) (U := U) (fppfYoneda.map b ≫ x) (fppfYoneda.map b ≫ y) := by
  apply pullback.lift_fst

set_option backward.isDefEq.respectTransparency false in
theorem baseChangeMap_isPullback {T' : Scheme.{u}} (b : T' ⟶ T)
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    IsPullback
      (baseChangeMap (G := G) (U := U) b x y)
      (projection (G := G) (U := U) (fppfYoneda.map b ≫ x) (fppfYoneda.map b ≫ y))
      (projection (G := G) (U := U) x y)
      (fppfYoneda.map b) := by
  apply IsPullback.of_right (h₁₂ := graphLift (G := G) (U := U) x y)
    (v₁₃ := reverseActionGraph (G := G) (U := U))
    (h₂₂ := pointPair (G := G) (U := U) x y) _
    (baseChangeMap_projection (G := G) (U := U) b x y)
    (IsPullback.of_hasPullback _ _)
  rw [baseChangeMap_graphLift, pointPair_precomp]
  exact
    (IsPullback.of_hasPullback
      (reverseActionGraph (G := G) (U := U))
      (pointPair (fppfYoneda.map b ≫ x) (fppfYoneda.map b ≫ y)))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem baseChangeMap_id
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    baseChangeMap (G := G) (U := U) (𝟙 T) x y = 𝟙 _ := by
  dsimp [baseChangeMap, graphLift, projection, sheaf]
  apply pullback.hom_ext <;> simp <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseChangeMap_comp {T' T'' : Scheme.{u}} (b : T' ⟶ T) (c : T'' ⟶ T')
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    baseChangeMap (G := G) (U := U) (c ≫ b) x y =
      baseChangeMap (G := G) (U := U) c (fppfYoneda.map b ≫ x) (fppfYoneda.map b ≫ y) ≫
        baseChangeMap (G := G) (U := U) b x y := by
  dsimp [baseChangeMap, graphLift, projection, sheaf]
  apply pullback.hom_ext <;> simp <;> rfl

/-! ### The same transporter equipped with its algebraic-space structure -/

noncomputable def tensorToProduct (X Y : FppfSheaf.{u}) :
    X ⊗ Y ⟶ X ⨯ Y :=
  prod.lift (fst _ _) (snd _ _)

noncomputable def productToTensor (X Y : FppfSheaf.{u}) :
    X ⨯ Y ⟶ X ⊗ Y :=
  lift (prod.fst) (prod.snd)

noncomputable def tensorProductIso (X Y : FppfSheaf.{u}) :
    X ⊗ Y ≅ X ⨯ Y where
  hom := tensorToProduct X Y
  inv := productToTensor X Y
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · change prod.lift (fst X Y) (snd X Y) ≫ prod.fst = fst X Y
      rw [prod.lift_fst]
    · change prod.lift (fst X Y) (snd X Y) ≫ prod.snd = snd X Y
      rw [prod.lift_snd]
  inv_hom_id := by
    apply prod.hom_ext <;> simp [tensorToProduct, productToTensor]

noncomputable instance tensorToProduct_isIso (X Y : FppfSheaf.{u}) :
    IsIso (tensorToProduct X Y) := by
  change IsIso (tensorProductIso X Y).hom
  infer_instance

noncomputable def tensorProductData
    (X Y : AlgebraicSpaceData.{u}) : AlgebraicSpaceData.{u} := by
  have h : FppfSheaf.IsRepresentable (tensorToProduct X.toSheaf Y.toSheaf) :=
    Functor.relativelyRepresentable.of_isIso fppfYoneda _
  exact AlgebraicSpaceData.ofRepresentable
    (AlgebraicSpaceData.prod X Y)
    (tensorToProduct X.toSheaf Y.toSheaf)
    h

noncomputable def transporterSpaceData
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) : AlgebraicSpaceData.{u} :=
  AlgebraicSpaceData.pullback
    (tensorProductData G.space U.space)
    (AlgebraicSpace.ofSchemeObj T)
    (AlgebraicSpaceData.prod U.space U.space)
    (reverseActionGraph (G := G) (U := U))
    (pointPair (G := G) (U := U) x y)

noncomputable def transporterSpace
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) : AlgebraicSpace.{u} :=
  transporterSpaceData (G := G) (U := U) x y

@[simp]
theorem transporterSpace_toSheaf
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (transporterSpace (G := G) (U := U) x y).toSheaf =
      sheaf (G := G) (U := U) x y :=
  rfl

noncomputable def transporterProjectionMap
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    transporterSpace (G := G) (U := U) x y ⟶ AlgebraicSpace.ofScheme.obj T :=
  AlgebraicSpace.homMk (projection (G := G) (U := U) x y)

noncomputable def transporterGraphMap
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    transporterSpace (G := G) (U := U) x y ⟶
      tensorProductData G.space U.space :=
  AlgebraicSpace.homMk (graphLift (G := G) (U := U) x y)

@[reassoc (attr := simp)]
theorem transporterGraphMap_action
    (x y : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    transporterGraphMap (G := G) (U := U) x y ≫
        AlgebraicSpace.homMk (Y := AlgebraicSpaceData.prod U.space U.space)
          (reverseActionGraph (G := G) (U := U)) =
      transporterProjectionMap (G := G) (U := U) x y ≫
        AlgebraicSpace.homMk (Y := AlgebraicSpaceData.prod U.space U.space)
          (pointPair (G := G) (U := U) x y) := by
  apply InducedCategory.hom_ext
  exact graphLift_condition (G := G) (U := U) x y

/-! ### Scheme representability and base-change-stable properties -/

variable {G₀ U₀ T₀ : Scheme.{u}}

noncomputable def schemeActionGraph (a : G₀ ⨯ U₀ ⟶ U₀) :
    G₀ ⨯ U₀ ⟶ U₀ ⨯ U₀ :=
  prod.lift a Limits.prod.snd

noncomputable def schemeTransporter (a : G₀ ⨯ U₀ ⟶ U₀)
    (x y : T₀ ⟶ U₀) : Scheme.{u} :=
  Limits.pullback (schemeActionGraph a) (Limits.prod.lift x y)

noncomputable def schemeTransporterProjection (a : G₀ ⨯ U₀ ⟶ U₀)
    (x y : T₀ ⟶ U₀) : schemeTransporter a x y ⟶ T₀ :=
  Limits.pullback.snd _ _

theorem schemeTransporterProjection_hasProperty
    (a : G₀ ⨯ U₀ ⟶ U₀) (x y : T₀ ⟶ U₀)
    (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    (ha : P (schemeActionGraph a)) :
    P (schemeTransporterProjection a x y) := by
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (schemeActionGraph a) (Limits.prod.lift x y)) ha

end QuotientTransporter

end GromovWitten.AlgebraicGeometry
