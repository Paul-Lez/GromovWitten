/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Sites.Stack

/-!
# Cartesian factorization in the total category

The point of this file is to keep the topology comparison tied to the actual Grothendieck
construction.  In a groupoid-valued pseudofunctor, the fibre component of every arrow is
invertible, so every arrow in the total category is strongly cartesian over its base arrow.
-/

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Pseudofunctor
open _root_.AlgebraicGeometry
open Opposite
open scoped CategoryTheory.Bicategory

namespace GromovWitten.AlgebraicGeometry.Sites

universe v u v' u'

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

open CategoryTheory.Bicategory
attribute [local simp] Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso
  Strict.associator_eqToIso
attribute [local simp] PrelaxFunctor.map₂_eqToHom

open Pseudofunctor.CoGrothendieck

/-- The vertical isomorphism from a total morphism to its canonical cartesian lift. -/
noncomputable def verticalIso
    [F.IsGroupoidValued] {a b : F.CoGrothendieck} (φ : a ⟶ b) :
    a ≅ domainCartesianLift b.fiber φ.base :=
  (ι F a.base).mapIso (asIso φ.fiber)

/-- All arrows in the total category of a groupoid-valued pseudofunctor are cartesian. -/
theorem isStronglyCartesian
    [F.IsGroupoidValued] {a b : F.CoGrothendieck} (φ : a ⟶ b) :
    IsStronglyCartesian (forget F) φ.base φ := by
  let ψ : domainCartesianLift b.fiber φ.base ⟶ b :=
    cartesianLift b.fiber φ.base
  let e : a ≅ domainCartesianLift b.fiber φ.base := verticalIso φ
  have hψ : IsStronglyCartesian (forget F) φ.base ψ := by
    exact isStronglyCartesian_homCartesianLift b.fiber φ.base
  have : IsStronglyCartesian (forget F) φ.base ψ := hψ
  have : IsHomLift (forget F) (𝟙 a.base) e.hom := by
    change IsHomLift (forget F) (𝟙 a.base) ((ι F a.base).map φ.fiber)
    exact HasFibers.homLift (p := forget F) (S := a.base) φ.fiber
  have : IsCartesian (forget F) φ.base (e.hom ≫ ψ) := by
    infer_instance
  have hcomp : e.hom ≫ ψ = φ := by
    refine Hom.ext _ _
      (by simp [e, ψ, verticalIso, Pseudofunctor.CoGrothendieck.ι]) ?_
    dsimp [e, ψ, verticalIso, Pseudofunctor.CoGrothendieck.ι]
    change
      (φ.fiber ≫ (F.mapId ⟨op a.base⟩).inv.toNatTrans.app
          ((F.map φ.base.op.toLoc).toFunctor.obj b.fiber)) ≫
        (F.map (𝟙 a.base).op.toLoc).toFunctor.map (𝟙 _) ≫
          (F.mapComp φ.base.op.toLoc (𝟙 a.base).op.toLoc).inv.toNatTrans.app b.fiber =
        φ.fiber ≫ eqToHom (by simp)
    simp [F.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso,
      ← Cat.Hom₂.comp_app]
  have hs : IsStronglyCartesian (forget F) φ.base (e.hom ≫ ψ) := by
    infer_instance
  simpa [hcomp] using hs

/-! The cartesian factorization implies an exact sieve comparison over every fixed target. -/

theorem functorPullback_functorPushforward_eq
    [F.IsGroupoidValued] {b : F.CoGrothendieck} (S : Sieve b) :
    (S.functorPushforward (forget F)).functorPullback (forget F) = S := by
  ext a α
  constructor
  · intro hα
    change Presieve.functorPushforward (forget F) S.arrows _ at hα
    obtain ⟨c, β, h, hβ, hfac⟩ := hα
    have : IsStronglyCartesian (forget F) ((forget F).map β) β := by
      change IsStronglyCartesian (forget F) β.base β
      exact isStronglyCartesian β
    obtain ⟨χ, ⟨hχ, hχβ⟩, -⟩ :=
      IsStronglyCartesian.universal_property
        (forget F) ((forget F).map β) β h ((forget F).map α) hfac α
    exact hχβ ▸ S.downward_closed hβ χ
  · intro hα
    exact (Sieve.le_functorPushforward_pullback (forget F) S) α hα

end StackInGroupoids

end GromovWitten.AlgebraicGeometry.Sites
