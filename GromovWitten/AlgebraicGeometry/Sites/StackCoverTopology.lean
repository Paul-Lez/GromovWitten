/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Sites.StackTopology

/-!
# The topology detected by a groupoid-valued Grothendieck projection

For the projection from the Grothendieck construction of a groupoid-valued
pseudofunctor, covering sieves can be tested after pushing them to the base.
The cartesian lifts in the construction provide the exact sieve pullback
calculus needed for this statement.
-/

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Pseudofunctor
open _root_.AlgebraicGeometry
open Opposite
open scoped CategoryTheory.Bicategory

namespace GromovWitten.AlgebraicGeometry.Sites

universe v u v' u' w

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

open CategoryTheory.Bicategory
open Pseudofunctor.CoGrothendieck

attribute [local simp] Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso
  Strict.associator_eqToIso
attribute [local simp] PrelaxFunctor.map₂_eqToHom

/-! ## Exact sieve pullback along a total arrow -/

/-- At the underlying object of a total category, pushing a base sieve down
after pulling it back along the projection recovers the original base sieve.
The canonical cartesian lift supplies a total lift of every base arrow into
that object. -/
theorem functorPushforward_functorPullback_eq
    [F.IsGroupoidValued] {b : F.CoGrothendieck} (R : Sieve b.base) :
    (R.functorPullback (forget F)).functorPushforward (forget F) = R := by
  apply le_antisymm
  · exact Sieve.functorPullback_pushforward_le (forget F) R
  · intro T f hf
    let β : domainCartesianLift b.fiber f ⟶ b := cartesianLift b.fiber f
    have hβ : (R.functorPullback (forget F)) β := by
      change R ((forget F).map β)
      change R f
      exact hf
    exact Sieve.image_mem_functorPushforward (forget F)
      (R.functorPullback (forget F)) hβ

/-- Pushing a sieve after pulling it back along a total arrow agrees with
pulling the pushed sieve back along the corresponding base arrow.  The
nontrivial inclusion uses the canonical cartesian lift of an arbitrary base
arrow and the reflection theorem from `StackTopology`. -/
theorem functorPushforward_pullback_eq
    [F.IsGroupoidValued] {a b : F.CoGrothendieck} (α : a ⟶ b) (S : Sieve b) :
    (S.pullback α).functorPushforward (forget F) =
      (S.functorPushforward (forget F)).pullback α.base := by
  apply le_antisymm
  · exact Sieve.functorPushforward_pullback_le (forget F) α S
  · intro T f hf
    let γ : domainCartesianLift a.fiber f ⟶ a := cartesianLift a.fiber f
    have hγ : (forget F).map γ = f := by
      change γ.base = f
      rfl
    have hcomp : S (γ ≫ α) := by
      rw [← functorPullback_functorPushforward_eq (F := F) S]
      change (S.functorPushforward (forget F))
        ((forget F).map (γ ≫ α))
      rw [Functor.map_comp, hγ]
      exact hf
    exact Sieve.image_mem_functorPushforward (forget F)
      (S.pullback α) hcomp

/-! ## The explicit pushforward topology -/

/-- The topology on the total category whose covers are exactly the sieves
whose pushforward is a cover on the base. -/
def pushforwardTopology [F.IsGroupoidValued]
    (K : GrothendieckTopology C) :
    GrothendieckTopology F.CoGrothendieck where
  sieves b := {S | S.functorPushforward (forget F) ∈ K b.base}
  top_mem' b := by
    change (⊤ : Sieve b).functorPushforward (forget F) ∈ K b.base
    rw [Sieve.functorPushforward_top]
    exact K.top_mem _
  pullback_stable' X Y S f hS := by
    change (S.pullback f).functorPushforward (forget F) ∈ K Y.base
    rw [functorPushforward_pullback_eq (F := F) f S]
    exact K.pullback_stable f.base hS
  transitive' X S hS R hR := by
    change R.functorPushforward (forget F) ∈ K X.base
    apply K.transitive hS (R.functorPushforward (forget F))
    intro Y g hg
    let β : domainCartesianLift X.fiber g ⟶ X := cartesianLift X.fiber g
    have hβ : S β := by
      rw [← functorPullback_functorPushforward_eq (F := F) S]
      change (S.functorPushforward (forget F)) g
      exact hg
    have hRβ : (R.pullback β).functorPushforward (forget F) ∈ K Y := hR hβ
    rw [functorPushforward_pullback_eq (F := F) β R] at hRβ
    exact hRβ

/-! ## Continuity of the explicit topology -/

theorem pushforwardTopology_coverPreserving [F.IsGroupoidValued]
    (K : GrothendieckTopology C) :
    CoverPreserving (pushforwardTopology (F := F) K) K (forget F) := by
  constructor
  intro b S hS
  exact hS

theorem pushforwardTopology_compatiblePreserving [F.IsGroupoidValued]
    (K : GrothendieckTopology C) :
    CompatiblePreserving.{w} K (forget F) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ heq
  let c : F.CoGrothendieck := domainCartesianLift Z.fiber
    (f₁ ≫ (forget F).map g₁)
  let φ : c ⟶ Z := cartesianLift Z.fiber
    (f₁ ≫ (forget F).map g₁)
  have hφ₁lift : (forget F).IsHomLift (f₁ ≫ (forget F).map g₁) φ := by
    change IsHomLift (forget F) ((forget F).map φ) φ
    exact IsHomLift.map (forget F) φ
  have : (forget F).IsHomLift (f₁ ≫ (forget F).map g₁) φ := hφ₁lift
  have hstrong₁ : IsStronglyCartesian (forget F) ((forget F).map g₁) g₁ :=
    isStronglyCartesian g₁
  obtain ⟨χ₁, ⟨hχ₁, hfac₁⟩, -⟩ :=
    IsStronglyCartesian.universal_property (forget F) ((forget F).map g₁) g₁ f₁
      (f₁ ≫ (forget F).map g₁) rfl φ
  have hstrong₂ : IsStronglyCartesian (forget F) ((forget F).map g₂) g₂ :=
    isStronglyCartesian g₂
  obtain ⟨χ₂, ⟨hχ₂, hfac₂⟩, -⟩ :=
    IsStronglyCartesian.universal_property (forget F) ((forget F).map g₂) g₂ f₂
      (f₁ ≫ (forget F).map g₁) heq φ
  have e₁ : f₁ = (forget F).map χ₁ :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ (forget F) c Y₁ f₁ χ₁ hχ₁
  have e₂ : f₂ = (forget F).map χ₂ :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ (forget F) c Y₂ f₂ χ₂ hχ₂
  rw [e₁, e₂]
  exact hx _ _ hg₁ hg₂ (hfac₁.trans hfac₂.symm)

theorem pushforwardTopology_isContinuous [F.IsGroupoidValued]
    (K : GrothendieckTopology C) :
    (forget F).IsContinuous (pushforwardTopology (F := F) K) K :=
  Functor.isContinuous_of_coverPreserving
    (pushforwardTopology_compatiblePreserving (F := F) K)
    (pushforwardTopology_coverPreserving (F := F) K)

/-! ## Identification with the induced topology -/

theorem inducedTopology_eq_pushforwardTopology [F.IsGroupoidValued]
    (K : GrothendieckTopology C) :
    (forget F).inducedTopology K = pushforwardTopology (F := F) K := by
  apply le_antisymm
  · intro b S hS
    change S.functorPushforward (forget F) ∈ K b.base
    exact (CoverPreserving.of_isContinuous (forget F)
      ((forget F).inducedTopology K) K).cover_preserve hS
  · rw [Functor.le_inducedTopology_iff]
    exact pushforwardTopology_isContinuous (F := F) K

end StackInGroupoids

/-! ## The big fppf stack site -/

theorem bigFppfStackTopology_eq_pushforwardTopology
    (X : FppfStack.{u}) :
    bigFppfStackTopology X =
      StackInGroupoids.pushforwardTopology (F := X.toPseudofunctor)
        Scheme.fppfTopology := by
  exact StackInGroupoids.inducedTopology_eq_pushforwardTopology
    (F := X.toPseudofunctor) Scheme.fppfTopology

theorem mem_bigFppfStackTopology_iff
    (X : FppfStack.{u}) (b : X.total) (S : Sieve b) :
    S ∈ bigFppfStackTopology X b ↔
      S.functorPushforward X.projection ∈ Scheme.fppfTopology b.base := by
  rw [bigFppfStackTopology_eq_pushforwardTopology]
  rfl

end GromovWitten.AlgebraicGeometry.Sites
