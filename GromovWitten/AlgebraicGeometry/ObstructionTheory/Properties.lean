/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.Perfect
import GromovWitten.AlgebraicGeometry.IntrinsicNormalCone.Properties
import GromovWitten.AlgebraicGeometry.ObstructionTheory.Geometric

/-!
# Functoriality and local meaning of obstruction theories

This module is currently an inactive checklist for the closed-immersion criterion, pullback,
external sums, transitivity, and geometric-point obstruction theory.  The former records
supplied these constructions or conclusions as fields and are retired below; no corresponding
general theorem is exported from this file.
-/

open CategoryTheory CategoryTheory.Pretriangulated

namespace GromovWitten.AlgebraicGeometry.DerivedObstructionTheory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {L E : DerivedCategory C}

/-
Retired provisional obstruction-theory property packages.  They supplied the closed-immersion
criterion, pullback/external-sum comparison, transitivity, or curvilinear universality as fields
and then projected those fields as the advertised theorem.  They are inactive pending genuine
constructions from derived functors and the intrinsic cone.

/-- A derived map and the induced map of dual Picard cone stacks. -/
structure DualConeMapCriterion
    {X : DeligneMumfordStack.{u}} {O : FppfScalarRings.{u}}
    (φ : E ⟶ L) where
  sourceCone : AbelianConeStack X.toStack O
  targetCone : AbelianConeStack X.toStack O
  dualMap : ConeStack.Hom targetCone.toConeStack sourceCone.toConeStack
  closed_iff :
    dualMap.toStackHom.ClosedImmersion ↔
      IsIso (cohomologyMap 0 φ) ∧ Epi (cohomologyMap (-1) φ)

namespace DualConeMapCriterion

/-- The Behrend--Fantechi cohomological conditions are equivalent to the dual cone map being a
representable closed immersion. -/
theorem obstructionTheory_iff_closed
    {X : DeligneMumfordStack.{u}} {O : FppfScalarRings.{u}}
    {φ : E ⟶ L} (D : DualConeMapCriterion (X := X) (O := O) φ) :
    (IsIso (cohomologyMap 0 φ) ∧ Epi (cohomologyMap (-1) φ)) ↔
      D.dualMap.toStackHom.ClosedImmersion := by
  exact D.closed_iff.symm

end DualConeMapCriterion

/-- Pullback of an obstruction theory through a derived inverse-image functor. -/
structure Pullback
    (D : Type u) [Category.{v} D] [Abelian D] [HasDerivedCategory.{w} D]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (T : ObstructionTheory L) (L' : DerivedCategory D) where
  cotangentComparison : F.obj L ⟶ L'
  pulled : ObstructionTheory L'
  sourceIso : pulled.E ≅ F.obj T.E
  morphismFormula : sourceIso.hom ≫ F.map T.φ ≫ cotangentComparison = pulled.φ

/-- External direct sum of obstruction theories on a product. -/
structure ExternalSum
    (T : ObstructionTheory L) (T' : ObstructionTheory L) where
  target : DerivedCategory C
  theory : ObstructionTheory target
  sourceIso : theory.E ≅ T.E ⊞ T'.E
  virtualRank : ℤ
  leftRank : ℤ
  rightRank : ℤ
  rank_add : virtualRank = leftRank + rightRank

/-- Compatibility of obstruction theories is a genuine morphism of distinguished transitivity
triangles. -/
structure CompatibleTransitivity
    (A B : CotangentComplex.TransitivityTriangle (C := C)) where
  obstructionTriangle : Triangle (DerivedCategory C)
  obstruction_distinguished :
    obstructionTriangle ∈ distTriang (DerivedCategory C)
  triangleMap : obstructionTriangle ⟶ A.triangle
  comparison : A.triangle ⟶ B.triangle
  composite : obstructionTriangle ⟶ B.triangle
  composite_eq : triangleMap ≫ comparison = composite

/-- The local obstruction space and curvilinear arcs at a geometric point. -/
structure GeometricPointObstruction
    (k : Type u) [Field k]
    {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}}
    (N : IntrinsicNormalCone.Geometry X ground O) where
  pointScheme : Scheme.{u}
  pointSchemeIso : pointScheme ≅ _root_.AlgebraicGeometry.Spec (.of k)
  point : StackFiber X.toStack pointScheme
  tangentSpace : Type u
  obstructionSpace : Type u
  tangent_add : AddCommGroup tangentSpace
  obstruction_add : AddCommGroup obstructionSpace
  tangent_module : Module k tangentSpace
  obstruction_module : Module k obstructionSpace
  CurvilinearExtension : Type u
  obstruction : CurvilinearExtension → obstructionSpace
  coarseConeClass : N.cone.cone.FiberOver pointScheme point → obstructionSpace
  intrinsicConeFiber : Set obstructionSpace
  intrinsicConeFiber_eq_range : intrinsicConeFiber = Set.range coarseConeClass
  universal : ∀ v : obstructionSpace,
    v ∈ intrinsicConeFiber ↔ ∃ e : CurvilinearExtension, obstruction e = v
  /-- Lifts of each curvilinear extension form a groupoid, retaining automorphisms. -/
  Lift (e : CurvilinearExtension) : Type u
  [liftCategory (e : CurvilinearExtension) : Category.{v} (Lift e)]
  [liftGroupoid (e : CurvilinearExtension) : IsGroupoid (Lift e)]
  liftable_iff (e : CurvilinearExtension) : Nonempty (Lift e) ↔ obstruction e = 0

attribute [instance] GeometricPointObstruction.tangent_add
  GeometricPointObstruction.obstruction_add GeometricPointObstruction.tangent_module
  GeometricPointObstruction.obstruction_module GeometricPointObstruction.liftCategory
  GeometricPointObstruction.liftGroupoid

namespace GeometricPointObstruction

variable {k : Type u} [Field k]
  {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
  {O : FppfScalarRings.{u}}
  {N : IntrinsicNormalCone.Geometry X ground O}

/-- The intrinsic-cone fibre is exactly the set of curvilinear obstruction classes. -/
theorem mem_intrinsicConeFiber_iff
    (G : GeometricPointObstruction k N) (v : G.obstructionSpace) :
    v ∈ G.intrinsicConeFiber ↔ ∃ e, G.obstruction e = v :=
  G.universal v

/-- A curvilinear extension lifts exactly when its universal obstruction vanishes. -/
theorem liftable_iff_obstruction_zero
    (G : GeometricPointObstruction k N) (e : G.CurvilinearExtension) :
    Nonempty (G.Lift e) ↔ G.obstruction e = 0 :=
  G.liftable_iff e

end GeometricPointObstruction

-/

end GromovWitten.AlgebraicGeometry.DerivedObstructionTheory
