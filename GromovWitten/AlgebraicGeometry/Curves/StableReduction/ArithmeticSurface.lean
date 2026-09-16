/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.RegularScheme
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.Model
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.NumericalType

/-!
# Arithmetic surfaces and their special-fibre intersection data

This file supplies the local arithmetic-surface interface used by stable reduction.  The
component carrier is not an unrelated finite index type: it is the actual type of irreducible
components of the scheme-theoretic special fibre.  Multiplicities, residue weights, genera, and
the intersection matrix are recorded on that carrier, and the usual fibre relation produces the
existing `NumericalType` without any reindexing assumption.

Regularity is stated on the actual local rings of the total scheme.  Resolutions and proper
modifications likewise contain actual models and scheme morphisms; their generic-fibre map is
required to be an isomorphism rather than represented by a Boolean or a numerical flag.
-/

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- The underlying scheme of the special fibre of a model. -/
abbrev Model.specialFiberScheme (M : Model R K C toK) : Scheme.{u} :=
  (specialFiber R M.toBase).left

/-- A regular proper arithmetic surface model of the fixed generic curve. -/
structure ArithmeticSurface (M : Model R K C toK) : Prop where
  proper : M.IsProper
  regular : SchemeIsRegular M.total

namespace ArithmeticSurface

variable {M : Model R K C toK}

theorem isProper (h : ArithmeticSurface M) : M.IsProper := h.proper

/-- The actual irreducible components of the scheme-theoretic special fibre. -/
abbrev Component (M : Model R K C toK) :=
  irreducibleComponents M.specialFiberScheme

/-- A component-indexed divisor on the special fibre. -/
abbrev VerticalDivisor (M : Model R K C toK) := Component M → ℤ

/-- Intersection-theoretic data on the actual components of the special fibre.

The divisibility convention is the destination-weight convention used by the arithmetic
surface Picard relations. -/
structure SpecialFiberIntersectionData (M : Model R K C toK) where
  componentFintype : Fintype (Component M)
  componentDecidableEq : DecidableEq (Component M)
  componentNonempty : Nonempty (Component M)
  multiplicity : Component M → ℕ+
  weight : Component M → ℕ+
  intersection : Matrix (Component M) (Component M) ℤ
  intersection_symm : ∀ i j, intersection i j = intersection j i
  offDiagonal_nonnegative : ∀ i j, i ≠ j → 0 ≤ intersection i j
  connected : ∀ i j, Relation.ReflTransGen
    (fun i j ↦ i ≠ j ∧ 0 < intersection i j) i j
  fiber_relation : ∀ i, ∑ j, (multiplicity j : ℤ) * intersection i j = 0
  weight_dvd : ∀ i j, (weight i : ℤ) ∣ intersection i j
  genus : Component M → ℕ

namespace SpecialFiberIntersectionData

variable (D : SpecialFiberIntersectionData M)

/-- Forgetting the geometric carrier inclusion gives the established numerical-type API. -/
def toNumericalType : NumericalType where
  Component := Component M
  componentFintype := D.componentFintype
  componentDecidableEq := D.componentDecidableEq
  componentNonempty := D.componentNonempty
  multiplicity := D.multiplicity
  weight := D.weight
  intersection := D.intersection
  intersection_symm := D.intersection_symm
  offDiagonal_nonnegative := D.offDiagonal_nonnegative
  connected := D.connected
  fiber_relation := D.fiber_relation
  weight_dvd := D.weight_dvd
  genus := D.genus

@[simp]
theorem toNumericalType_component : D.toNumericalType.Component = Component M := rfl

@[simp]
theorem toNumericalType_multiplicity (i : Component M) :
    D.toNumericalType.multiplicity i = D.multiplicity i := rfl

@[simp]
theorem toNumericalType_weight (i : Component M) :
    D.toNumericalType.weight i = D.weight i := rfl

@[simp]
theorem toNumericalType_intersection (i j : Component M) :
    D.toNumericalType.intersection i j = D.intersection i j := rfl

@[simp]
theorem toNumericalType_genus (i : Component M) :
    D.toNumericalType.genus i = D.genus i := rfl

/-- Bilinear intersection of vertical divisors, formed from the geometric component matrix. -/
def divisorIntersection (A B : VerticalDivisor M) : ℤ := by
  letI := D.componentFintype
  exact ∑ i, ∑ j, A i * B j * D.intersection i j

/-- The special fibre as a vertical divisor. -/
def fiberDivisor : VerticalDivisor M := fun i ↦ D.multiplicity i

theorem divisorIntersection_add_left (A B E : VerticalDivisor M) :
    D.divisorIntersection (A + B) E =
      D.divisorIntersection A E + D.divisorIntersection B E := by
  let _ := D.componentFintype
  let _ := D.componentDecidableEq
  simp only [divisorIntersection, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem divisorIntersection_add_right (A B E : VerticalDivisor M) :
    D.divisorIntersection A (B + E) =
      D.divisorIntersection A B + D.divisorIntersection A E := by
  let _ := D.componentFintype
  let _ := D.componentDecidableEq
  simp only [divisorIntersection, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem divisorIntersection_symm (A B : VerticalDivisor M) :
    D.divisorIntersection A B = D.divisorIntersection B A := by
  classical
  rw [divisorIntersection, divisorIntersection, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [D.intersection_symm]
  ring

/-- Every vertical divisor has zero intersection with the whole special fibre. -/
theorem divisorIntersection_fiberDivisor_right (A : VerticalDivisor M) :
    D.divisorIntersection A D.fiberDivisor = 0 := by
  let _ := D.componentFintype
  let _ := D.componentDecidableEq
  rw [divisorIntersection]
  apply Finset.sum_eq_zero
  intro i _
  calc
    ∑ j, A i * D.fiberDivisor j * D.intersection i j =
        A i * ∑ j, (D.multiplicity j : ℤ) * D.intersection i j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [fiberDivisor]
          ring
    _ = 0 := by rw [D.fiber_relation, mul_zero]

theorem divisorIntersection_fiberDivisor_left (A : VerticalDivisor M) :
    D.divisorIntersection D.fiberDivisor A = 0 := by
  rw [D.divisorIntersection_symm, D.divisorIntersection_fiberDivisor_right]

/-- A geometric component has the numerical signature of an exceptional `(-1)`-curve. -/
def IsExceptionalComponent (i : Component M) : Prop :=
  D.genus i = 0 ∧ D.multiplicity i = 1 ∧ D.weight i = 1 ∧ D.intersection i i = -1

/-- Relative minimality excludes exceptional components from the actual special fibre. -/
def IsRelativelyMinimal : Prop := ∀ i, ¬ D.IsExceptionalComponent i

end SpecialFiberIntersectionData

end ArithmeticSurface

/-- A proper modification between two models of the same generic curve.  Compatibility with
their chosen generic-fibre identifications is carried by the model morphism; the displayed
generic map is additionally certified to be an isomorphism. -/
structure ModelModification (M N : Model R K C toK) where
  hom : M ⟶ N
  proper : _root_.AlgebraicGeometry.IsProper hom.hom
  genericIsIso : IsIso (Model.baseChangeHom (R := R) (K := K) hom.hom hom.over_base)

namespace ModelModification

variable {M N P : Model R K C toK}

/-- The identity modification. -/
def refl (M : Model R K C toK) : ModelModification M M where
  hom := 𝟙 M
  proper := by
    change _root_.AlgebraicGeometry.IsProper (𝟙 M.total)
    infer_instance
  genericIsIso := by
    change IsIso (Model.baseChangeHom (R := R) (K := K) (𝟙 M.total) _)
    rw [Model.baseChangeHom_id]
    infer_instance

/-- Proper modifications compose. -/
def comp (f : ModelModification M N) (g : ModelModification N P) :
    ModelModification M P where
  hom := f.hom ≫ g.hom
  proper := by
    change _root_.AlgebraicGeometry.IsProper (f.hom.hom ≫ g.hom.hom)
    let _ : _root_.AlgebraicGeometry.IsProper f.hom.hom := f.proper
    let _ : _root_.AlgebraicGeometry.IsProper g.hom.hom := g.proper
    infer_instance
  genericIsIso := by
    change IsIso (Model.baseChangeHom (R := R) (K := K)
      (f.hom.hom ≫ g.hom.hom) _)
    rw [Model.baseChangeHom_comp]
    let _ : IsIso (Model.baseChangeHom (R := R) (K := K)
      f.hom.hom f.hom.over_base) := f.genericIsIso
    let _ : IsIso (Model.baseChangeHom (R := R) (K := K)
      g.hom.hom g.hom.over_base) := g.genericIsIso
    infer_instance

end ModelModification

/-- A regular resolution of a proper model by an actual proper modification. -/
structure RegularResolution (M : Model R K C toK) where
  resolved : Model R K C toK
  resolvedProper : resolved.IsProper
  resolvedRegular : SchemeIsRegular resolved.total
  map : ModelModification resolved M

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
