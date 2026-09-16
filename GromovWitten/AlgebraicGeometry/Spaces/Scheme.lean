/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Spaces.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Schemes as algebraic spaces

The fppf Yoneda sheaf of a scheme is an algebraic space.  Its diagonal is representable because
Yoneda preserves binary products, and its identity morphism is a surjective étale atlas.  This
gives the promised fully faithful comparison functor from schemes to algebraic spaces.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace AlgebraicSpace

/-- The product comparison identifies the Yoneda image of the diagonal of a scheme with the
diagonal of its fppf sheaf. -/
theorem map_diagonal_comp_prodComparison (X : Scheme.{u}) :
    fppfYoneda.map (Limits.diag X) ≫
        (PreservesLimitPair.iso fppfYoneda X X).hom =
      FppfSheaf.diagonal (fppfYoneda.obj X) := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst]
    rw [← fppfYoneda.map_comp]
    simpa only [FppfSheaf.diagonal, prod.lift_fst, Functor.map_id]
      using fppfYoneda.map_id X
  · simp only [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd]
    rw [← fppfYoneda.map_comp]
    simpa only [FppfSheaf.diagonal, prod.lift_snd, Functor.map_id]
      using fppfYoneda.map_id X

/-- The fppf functor of points of a scheme, equipped with its algebraic-space structure. -/
noncomputable def ofSchemeObj (X : Scheme.{u}) : AlgebraicSpaceData.{u} where
  toSheaf := fppfYoneda.obj X
  diagonal_representable := by
    rw [← map_diagonal_comp_prodComparison X]
    exact FppfSheaf.IsRepresentable.comp_mem _ _
      (FppfSheaf.yoneda_map_isRepresentable (Limits.diag X))
      (Functor.relativelyRepresentable.of_isIso fppfYoneda _)
  atlas := ⟨X, 𝟙 _, by
    change (((@_root_.AlgebraicGeometry.Etale ⊓ @_root_.AlgebraicGeometry.Surjective) :
      MorphismProperty Scheme.{u}).relative fppfYoneda) (𝟙 _)
    refine ⟨Functor.relativelyRepresentable.of_isIso fppfYoneda _, ?_⟩
    intro a b g fst snd h
    have : IsIso (fppfYoneda.map snd) := h.isIso_snd_of_isIso
    have : IsIso snd :=
      Scheme.fppfTopology.yonedaFullyFaithful.isIso_of_isIso_map snd
    exact ⟨inferInstance, inferInstance⟩⟩

/-- The fully faithful functor from schemes to algebraic spaces. -/
noncomputable def ofScheme : Scheme.{u} ⥤ AlgebraicSpace.{u} where
  obj X := ofSchemeObj X
  map f := homMk (fppfYoneda.map f)
  map_id X := by rfl
  map_comp f g := by rfl

@[simp]
theorem ofScheme_forget_obj (X : Scheme.{u}) :
    forget.obj (ofScheme.obj X) = fppfYoneda.obj X :=
  rfl

@[simp]
theorem ofScheme_forget_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    forget.map (ofScheme.map f) = fppfYoneda.map f :=
  rfl

/-- Scheme morphisms are exactly the morphisms between the associated algebraic spaces. -/
noncomputable def ofSchemeFullyFaithful : ofScheme.{u}.FullyFaithful where
  preimage f := fppfYoneda.preimage f.hom
  map_preimage f := by
    apply InducedCategory.hom_ext
    exact fppfYoneda.map_preimage f.hom
  preimage_map f := fppfYoneda.preimage_map f

instance : ofScheme.{u}.Full := ofSchemeFullyFaithful.full

instance : ofScheme.{u}.Faithful := ofSchemeFullyFaithful.faithful

instance : forget.{u}.Full := forgetFullyFaithful.full

instance : forget.{u}.Faithful := forgetFullyFaithful.faithful

/-- Forgetting the algebraic-space structure after embedding a scheme is exactly its fppf
Yoneda sheaf. -/
noncomputable def ofSchemeCompForgetIso : ofScheme.{u} ⋙ forget.{u} ≅ fppfYoneda.{u} :=
  Iso.refl _

/-- The scheme-to-algebraic-space embedding preserves pullbacks.  Thus a pullback of schemes,
viewed as algebraic spaces, is the categorical pullback of the same two morphisms; no second
scheme pullback API is introduced. -/
noncomputable instance : PreservesLimitsOfShape WalkingCospan ofScheme.{u} := by
  have : PreservesLimitsOfShape WalkingCospan (ofScheme.{u} ⋙ forget.{u}) :=
    preservesLimitsOfShape_of_natIso ofSchemeCompForgetIso.symm
  exact preservesLimitsOfShape_of_reflects_of_preserves ofScheme forget

/-- The embedding also preserves binary products of schemes. -/
noncomputable instance :
    PreservesLimitsOfShape (Discrete WalkingPair) ofScheme.{u} := by
  have : PreservesLimitsOfShape (Discrete WalkingPair) (ofScheme.{u} ⋙ forget.{u}) :=
    preservesLimitsOfShape_of_natIso ofSchemeCompForgetIso.symm
  exact preservesLimitsOfShape_of_reflects_of_preserves ofScheme forget

/-- A scheme morphism is representable after embedding schemes into algebraic spaces. -/
theorem ofScheme_map_representable {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Representable (ofScheme.map f) :=
  FppfSheaf.yoneda_map_isRepresentable f

/-- A base-change-stable property of a scheme morphism agrees with the corresponding
representable property of its morphism of algebraic spaces. -/
theorem ofScheme_map_hasRepresentableProperty_iff
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} {f : X ⟶ Y} :
    HasRepresentableProperty P (ofScheme.map f) ↔ P f :=
  FppfSheaf.yoneda_map_hasRepresentableProperty_iff P

end AlgebraicSpace

end GromovWitten.AlgebraicGeometry
