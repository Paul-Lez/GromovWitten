/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineHigherBaseChange
import GromovWitten.AlgebraicGeometry.Curves.AffineBaseChangeIsomorphism

/-!
# Isomorphism criteria for flat higher base change

The degree-zero flat comparison is the ordinary Beck--Chevalley map after the
canonical zeroth-derived identifications.  Since those identifications are
isomorphisms, its invertibility is equivalent to ordinary base change.  For an
affine family, ordinary quasi-coherent base change and positive-degree vanishing
give the comparison in every degree.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S T Z : Scheme.{u}}

private theorem isIso_middle_iff {C : Type u} [Category C]
    {W X Y Z : C} {α : W ⟶ X} {β : X ⟶ Y} {γ : Y ⟶ Z}
    [IsIso α] [IsIso γ] :
    IsIso β ↔ IsIso ((α ≫ β) ≫ γ) := by
  constructor
  · intro hβ
    have : IsIso β := hβ
    rw [Category.assoc]
    infer_instance
  · intro hcomp
    have : IsIso ((α ≫ β) ≫ γ) := hcomp
    have : IsIso (α ≫ β) := IsIso.of_isIso_comp_right _ γ
    exact IsIso.of_isIso_comp_left α β

/-- Degree-zero flat higher base change is invertible exactly when ordinary
base change is invertible. -/
theorem moduleFlatHigherBaseChange_zero_isIso_iff
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [Flat b] (M : X.Modules) :
    IsIso ((moduleFlatHigherBaseChangeNatTrans f b p g h 0).app M) ↔
      IsIso (canonicalPushforwardBaseChangeComparison f M b p g h) := by
  let α := (Scheme.Modules.pullback b).map
    ((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf.inv.app M)
  let β := (moduleFlatHigherBaseChangeNatTrans f b p g h 0).app M
  let γ := (Scheme.Modules.pushforward g).rightDerivedZeroIsoSelf.hom.app
    ((Scheme.Modules.pullback p).obj M)
  let q := canonicalPushforwardBaseChangeComparison f M b p g h
  change IsIso β ↔ IsIso q
  have : IsIso α := by
    dsimp [α]
    infer_instance
  have : IsIso γ := by
    dsimp [γ]
    infer_instance
  have hz : (α ≫ β) ≫ γ = q := by
    simpa only [Category.assoc, α, β, γ, q] using
      (moduleFlatHigherBaseChange_zero f b p g h M)
  constructor
  · intro hβ
    have : IsIso β := hβ
    have hcomp : IsIso ((α ≫ β) ≫ γ) := by infer_instance
    rw [hz] at hcomp
    exact hcomp
  · intro hq
    have : IsIso q := hq
    have hcomp : IsIso ((α ≫ β) ≫ γ) := by
      rw [hz]
      infer_instance
    exact (isIso_middle_iff (α := α) (β := β) (γ := γ)).mpr hcomp

/-- Flat higher base change for an affine morphism and a quasi-coherent module,
in every degree. -/
theorem moduleFlatHigherBaseChange_all_isIso
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [IsAffineHom f] [Flat b]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    IsIso ((moduleFlatHigherBaseChangeNatTrans f b p g h n).app M) := by
  cases n with
  | zero =>
      exact (moduleFlatHigherBaseChange_zero_isIso_iff f b p g h M).mpr
        (canonicalPushforwardBaseChangeComparison_isIso_of_isAffineHom f b p g h M)
  | succ n =>
      exact moduleFlatHigherBaseChange_succ_isIso f b p g h M n

end GromovWitten.AlgebraicGeometry.Curves
