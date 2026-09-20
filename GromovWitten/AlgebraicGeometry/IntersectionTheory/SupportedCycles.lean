/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup

/-!
# Cycles and rational relations supported in a closed subset

Two small predicates used by the Noetherian induction proving the global homotopy property of
vector bundles (Fulton, *Intersection Theory*, Proposition 1.9):

* `AlgebraicCycle.SupportedIn z Z`: the cycle `z` vanishes outside the subset `Z`;
* `RationalFunctionGenerator.SupportedIn g Z`: the integral closed subscheme of the generator `g`
  lies inside `Z`;
* `supportedRelations X dimension Z`: the span of the principal divisors of the generators
  supported in `Z`.  It is contained in `totalRationalRelations X dimension` and is monotone in
  `Z`.
-/

open CategoryTheory

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

variable {X : Scheme.{u}}

namespace AlgebraicCycle

/-- A cycle is supported in a subset if it vanishes at every point outside the subset. -/
def SupportedIn (z : AlgebraicCycle X ℚ) (Z : Set X) : Prop :=
  ∀ x, (z : X → ℚ) x ≠ 0 → x ∈ Z

theorem SupportedIn.mono {z : AlgebraicCycle X ℚ} {Z Z' : Set X} (h : z.SupportedIn Z)
    (hZ : Z ⊆ Z') : z.SupportedIn Z' :=
  fun x hx ↦ hZ (h x hx)

theorem supportedIn_zero (Z : Set X) : (0 : AlgebraicCycle X ℚ).SupportedIn Z :=
  fun _ hx ↦ absurd rfl hx

theorem SupportedIn.add {z w : AlgebraicCycle X ℚ} {Z : Set X} (hz : z.SupportedIn Z)
    (hw : w.SupportedIn Z) : (z + w).SupportedIn Z := by
  intro x hx
  by_contra hcon
  have h1 : (z : X → ℚ) x = 0 := by
    by_contra h
    exact hcon (hz x h)
  have h2 : (w : X → ℚ) x = 0 := by
    by_contra h
    exact hcon (hw x h)
  exact hx (by rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, h1, h2, add_zero])

theorem SupportedIn.neg {z : AlgebraicCycle X ℚ} {Z : Set X} (hz : z.SupportedIn Z) :
    (-z).SupportedIn Z := by
  intro x hx
  refine hz x ?_
  intro h
  exact hx (by rw [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, h, neg_zero])

theorem SupportedIn.sub {z w : AlgebraicCycle X ℚ} {Z : Set X} (hz : z.SupportedIn Z)
    (hw : w.SupportedIn Z) : (z - w).SupportedIn Z := by
  rw [sub_eq_add_neg]
  exact hz.add hw.neg

theorem SupportedIn.smul {z : AlgebraicCycle X ℚ} {Z : Set X} (q : ℚ) (hz : z.SupportedIn Z) :
    (q • z).SupportedIn Z := by
  intro x hx
  refine hz x ?_
  intro h
  exact hx (by rw [Function.locallyFinsuppWithin.coe_rational_smul, Pi.smul_apply, h, smul_zero])

/-- The cycles supported in a subset form a submodule. -/
def supportedIn (Z : Set X) : Submodule ℚ (AlgebraicCycle X ℚ) where
  carrier := {z | z.SupportedIn Z}
  zero_mem' := supportedIn_zero Z
  add_mem' := fun hz hw ↦ SupportedIn.add hz hw
  smul_mem' := fun q _ hz ↦ SupportedIn.smul q hz

theorem mem_supportedIn_iff (Z : Set X) (z : AlgebraicCycle X ℚ) :
    z ∈ supportedIn Z ↔ z.SupportedIn Z :=
  Iff.rfl

end AlgebraicCycle

namespace RationalFunctionGenerator

/-- A generator is supported in a subset if its integral closed subscheme lies inside it. -/
def SupportedIn (g : RationalFunctionGenerator X) (Z : Set X) : Prop :=
  Set.range g.subspace.inclusion.base ⊆ Z

theorem SupportedIn.mono {g : RationalFunctionGenerator X} {Z Z' : Set X} (h : g.SupportedIn Z)
    (hZ : Z ⊆ Z') : g.SupportedIn Z' :=
  h.trans hZ

end RationalFunctionGenerator

/-- The span of the principal divisors of the generators supported in `Z`. -/
def supportedRelations (X : Scheme.{u}) (dimension : DimensionFunction X) (Z : Set X) :
    Submodule ℚ (AlgebraicCycle X ℚ) :=
  Submodule.span ℚ
    {d | ∃ g : RationalFunctionGenerator X, g.SupportedIn Z ∧ d = g.divisor dimension}

theorem divisor_mem_supportedRelations (dimension : DimensionFunction X) {Z : Set X}
    {g : RationalFunctionGenerator X} (hg : g.SupportedIn Z) :
    g.divisor dimension ∈ supportedRelations X dimension Z :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem supportedRelations_le_totalRationalRelations (dimension : DimensionFunction X)
    (Z : Set X) : supportedRelations X dimension Z ≤ totalRationalRelations X dimension := by
  refine Submodule.span_le.2 ?_
  rintro d ⟨g, -, rfl⟩
  exact Submodule.subset_span ⟨g, rfl⟩

theorem supportedRelations_mono (dimension : DimensionFunction X) {Z Z' : Set X} (h : Z ⊆ Z') :
    supportedRelations X dimension Z ≤ supportedRelations X dimension Z' := by
  refine Submodule.span_le.2 ?_
  rintro d ⟨g, hg, rfl⟩
  exact Submodule.subset_span ⟨g, hg.mono h, rfl⟩

theorem supportedRelations_univ (dimension : DimensionFunction X) :
    supportedRelations X dimension Set.univ = totalRationalRelations X dimension := by
  refine le_antisymm (supportedRelations_le_totalRationalRelations dimension _) ?_
  refine Submodule.span_le.2 ?_
  rintro d ⟨g, rfl⟩
  exact Submodule.subset_span ⟨g, Set.subset_univ _, rfl⟩

end GromovWitten.AlgebraicGeometry.IntersectionTheory
