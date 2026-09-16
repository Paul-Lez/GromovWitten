/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.ObstructionTheory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Groupoid

/-!
# Derived-category infrastructure for future cotangent complexes

The active declarations in this file provide derived Ext notation, a homology-defined amplitude
predicate, and comparison with a local two-term presentation.  A genuine geometric cotangent
complex, its Jacobi--Zariski triangle, and square-zero deformation theory are not constructed
here; former records that supplied those results as fields remain retired below.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Derived Ext between two derived objects, expressed by a morphism to a shift. -/
abbrev DerivedExt (E F : DerivedCategory C) (n : ℤ) := E ⟶ F⟦n⟧

/-
Retired provisional abstract derived-operation bundle.  These functors were unconstrained and
were not constructed from a ringed-site morphism.

/-- A derived pullback between two fixed derived module categories.  Identity and composition
coherences belong to the varying geometric family (`GeometricTheory`), rather than being
vacuous automorphisms of this one functor. -/
structure DerivedPullback (D : Type u) [Category.{v} D] [Abelian D]
    [HasDerivedCategory.{w} D] where
  functor : DerivedCategory C ⥤ DerivedCategory D

/-- Derived tensor, internal Hom, and duality on a module category.  These are honest functors;
the evaluation and bidual maps retain the morphisms used by perfect-complex arguments. -/
structure DerivedMonoidalOperations where
  tensor : (DerivedCategory C × DerivedCategory C) ⥤ DerivedCategory C
  internalHom : ((DerivedCategory C)ᵒᵖ × DerivedCategory C) ⥤ DerivedCategory C
  unit : DerivedCategory C
  dual : (DerivedCategory C)ᵒᵖ ⥤ DerivedCategory C
  evaluation (E : DerivedCategory C) : tensor.obj (dual.obj (Opposite.op E), E) ⟶ unit
  bidual (E : DerivedCategory C) : E ⟶ dual.obj (Opposite.op (dual.obj (Opposite.op E)))

-/

/-- Cohomological amplitude `[a,b]`, stated through Mathlib's homology functors on the actual
derived category. -/
def HasCohomologicalAmplitude (E : DerivedCategory C) (a b : ℤ) : Prop :=
  ∀ i : ℤ, i < a ∨ b < i →
    IsZero ((DerivedCategory.homologyFunctor C i).obj E)

theorem amplitude_negOne_zero_iff (E : DerivedCategory C) :
    HasCohomologicalAmplitude E (-1) 0 ↔
      DerivedObstructionTheory.HasAmplitudeNegOneZero E :=
  Iff.rfl

/-- Comparison of a geometric cotangent complex with a local two-term presentation. -/
structure LocalPresentationComparison (L presentation : DerivedCategory C) where
  map : L ⟶ presentation
  hZero_isIso :
    IsIso ((DerivedCategory.homologyFunctor C 0).map map)
  hNegOne_isIso :
    IsIso ((DerivedCategory.homologyFunctor C (-1)).map map)

attribute [instance] LocalPresentationComparison.hZero_isIso
  LocalPresentationComparison.hNegOne_isIso

/-
Retired provisional global cotangent/deformation packages.  They supplied the cotangent object,
coherence, obstruction/lift equivalence, and automorphism calculation as fields.  Affine
cotangent presentations and their derived localizations remain actual constructions.

/-- A geometric cotangent object with coherent cohomology.

Affine presentation comparisons are deliberately not fields of this generic record.  Without a
fixed geometric presentation type, such a field lets the caller choose a favorable private
index and omit other charts.  Concrete affine presentations are instead constructed from actual
`Algebra.Extension`s in `CotangentComplex.AffinePresentation`; stack-local comparisons must be
indexed by the fixed type of actual geometric charts at the layer where those charts exist. -/
structure GeometricCotangentComplex
    (Coherent : C → Prop) where
  object : DerivedCategory C
  cohomology_coherent (i : ℤ) :
    Coherent ((DerivedCategory.homologyFunctor C i).obj object)

/-- A square-zero lifting problem governed by a cotangent object.  Its solutions form a
groupoid, so automorphisms of a lift are not discarded. -/
structure SquareZeroLiftingProblem (L J : DerivedCategory C) where
  /-- The obstruction class in `Ext¹(L,J)`. -/
  obstruction : DerivedExt L J 1
  /-- The groupoid of lifts. -/
  Lift : Type u
  [liftCategory : Category.{v} Lift]
  [liftGroupoid : IsGroupoid Lift]
  /-- Vanishing is equivalent to existence of a lift. -/
  obstruction_zero_iff_nonempty : obstruction = 0 ↔ Nonempty Lift
  /-- Automorphisms of a chosen lift are identified with degree-zero deformation classes. -/
  automorphismEquiv (x : Lift) : (x ⟶ x) ≃ DerivedExt L J 0

attribute [instance] SquareZeroLiftingProblem.liftCategory
  SquareZeroLiftingProblem.liftGroupoid

namespace SquareZeroLiftingProblem

variable {L J : DerivedCategory C}

/-- The obstruction vanishes exactly when the lifting groupoid has an object. -/
theorem hasLift_iff (P : SquareZeroLiftingProblem L J) :
    Nonempty P.Lift ↔ P.obstruction = 0 :=
  P.obstruction_zero_iff_nonempty.symm

/-- Every arrow between lifts is invertible. -/
noncomputable def arrowIso (P : SquareZeroLiftingProblem L J)
    {x y : P.Lift} (f : x ⟶ y) : x ≅ y :=
  asIso f

end SquareZeroLiftingProblem

-/

end GromovWitten.AlgebraicGeometry.CotangentComplex
