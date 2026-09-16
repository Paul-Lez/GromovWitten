/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Basic

/-!
# The relative resolved virtual class

This module records the target dimension formula for a future relative construction.  The former
scheme-relative wrapper accepted its cone class and homotopy-invariance theorem as fields and is
retired below.  No general relative virtual class is exported.
-/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass

open IntersectionTheory

universe u

variable {X : Scheme.{u}} {dimensionX : DimensionFunction X}
  (base : RationalChowGrading X dimensionX)

/-
The former scheme-relative wrapper accepted its cone class and homotopy-invariance theorem as
fields.  It is deliberately inactive; a relative virtual-class constructor must build these from
the relative normal cone and vector bundle.

/-- Chow-theoretic data for a globally resolved relative perfect obstruction theory over a
smooth pure-dimensional base. -/
structure RelativeResolvedCone
    {F₁ : Scheme.{u}} {dimensionF₁ : DimensionFunction F₁}
    (total : RationalChowGrading F₁ dimensionF₁) where
  /-- Pure dimension of the smooth base. -/
  baseDimension : ℤ
  /-- Rank of `F₀=(F⁰)∨`. -/
  rankF₀ : ℕ
  /-- Rank of `F₁=(F⁻¹)∨`. -/
  rankF₁ : ℕ
  /-- Homotopy invariance for the total space of `F₁`. -/
  homotopy : VectorBundleHomotopyInvariance base total rankF₁
  /-- Fundamental class of the resolved relative cone, in dimension `d + rank F₀`. -/
  coneClass : total.group (baseDimension + (rankF₀ : ℤ))

namespace RelativeResolvedCone

variable {base}
  {F₁ : Scheme.{u}} {dimensionF₁ : DimensionFunction F₁}
  {total : RationalChowGrading F₁ dimensionF₁}
  (F : RelativeResolvedCone base total)

/-- Rank of the relative obstruction complex. -/
def virtualRank : ℤ :=
  (F.rankF₀ : ℤ) - (F.rankF₁ : ℤ)

/-- Dimension of the relative virtual class. -/
def virtualDimension : ℤ :=
  F.baseDimension + F.virtualRank

theorem virtualDimension_add_rankF₁ :
    F.virtualDimension + (F.rankF₁ : ℤ) =
      F.baseDimension + (F.rankF₀ : ℤ) := by
  simp [virtualDimension, virtualRank, add_assoc]

/-- Move the cone cycle into the source degree of zero-section Gysin. -/
def coneClassAtGysinDegree :
    total.group (F.virtualDimension + (F.rankF₁ : ℤ)) :=
  RationalChowGrading.cast F.virtualDimension_add_rankF₁.symm F.coneClass

/-- The relative Behrend--Fantechi class. -/
def virtualClass : base.group F.virtualDimension :=
  F.homotopy.zeroGysin F.virtualDimension F.coneClassAtGysinDegree

theorem virtualClass_formula :
    F.virtualClass =
      F.homotopy.zeroGysin F.virtualDimension
        (RationalChowGrading.cast F.virtualDimension_add_rankF₁.symm F.coneClass) :=
  rfl

/-- Regard an absolute resolved cone as a relative one over a zero-dimensional base. -/
noncomputable def ofAbsolute (A : ResolvedCone base total) : RelativeResolvedCone base total where
  baseDimension := 0
  rankF₀ := A.rankF₀
  rankF₁ := A.rankF₁
  homotopy := A.homotopy
  coneClass := RationalChowGrading.cast (by simp) A.coneClass

@[simp]
theorem ofAbsolute_virtualRank (A : ResolvedCone base total) :
    (ofAbsolute A).virtualRank = A.virtualRank :=
  rfl

@[simp]
theorem ofAbsolute_virtualDimension (A : ResolvedCone base total) :
    (ofAbsolute A).virtualDimension = A.virtualRank := by
  change 0 + (ofAbsolute A).virtualRank = A.virtualRank
  rw [zero_add, ofAbsolute_virtualRank]

set_option backward.isDefEq.respectTransparency false in
/-- The relative construction over a zero-dimensional base recovers the absolute resolved
class, after the canonical grading transport. -/
theorem ofAbsolute_virtualClass (A : ResolvedCone base total) :
  RationalChowGrading.cast (ofAbsolute_virtualDimension A)
      (ofAbsolute A).virtualClass = A.virtualClass := by
  unfold RelativeResolvedCone.virtualClass
  unfold RelativeResolvedCone.coneClassAtGysinDegree
  unfold RelativeResolvedCone.virtualDimension RelativeResolvedCone.virtualRank
  dsimp only [ofAbsolute]
  rw [A.homotopy.cast_zeroGysin]
  simp [ResolvedCone.virtualRank,
    ResolvedCone.virtualClass, ResolvedCone.coneClassAtGysinDegree,
    RationalChowGrading.cast_cast]

end RelativeResolvedCone

-/

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
