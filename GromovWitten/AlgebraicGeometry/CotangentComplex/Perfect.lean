/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.AffinePresentation
import GromovWitten.AlgebraicGeometry.CotangentComplex.Derived
import GromovWitten.AlgebraicGeometry.Modules.Stack

/-!
# Retired perfect-complex and site-comparison interfaces

The former interfaces for perfectness, Tor-amplitude, monoidal operations, site comparison,
geometric cotangent complexes, and resolution operations accepted their main mathematical
conclusions as fields.  They are therefore retained below only inside block comments and export
no such theory.  The sole active declaration is the elementary categorical record
`GeometricBaseChangeSquare`; constructing the geometric theories it was intended to support
remains open.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-
Retired provisional perfect-complex calculus.  Perfectness, Tor amplitude, monoidal operations,
rank, and every closure/rank theorem were supplied as fields.

/-- The complete operations and closure properties for perfect derived objects. -/
structure PerfectComplexTheory where
  IsPerfect : DerivedCategory C → Prop
  HasTorAmplitude : DerivedCategory C → ℤ → ℤ → Prop
  rank : DerivedCategory C → ℤ
  monoidal : DerivedMonoidalOperations (C := C)
  zeroObject : DerivedCategory C
  zeroObject_isZero : IsZero zeroObject
  perfect_zero : IsPerfect zeroObject
  perfect_shift (E : DerivedCategory C) (n : ℤ) : IsPerfect E → IsPerfect (E⟦n⟧)
  perfect_dual (E : DerivedCategory C) :
    IsPerfect E → IsPerfect (monoidal.dual.obj (.op E))
  perfect_tensor (E F : DerivedCategory C) :
    IsPerfect E → IsPerfect F → IsPerfect (monoidal.tensor.obj (E, F))
  rank_zero : rank zeroObject = 0
  rank_shift (E : DerivedCategory C) (n : ℤ) :
    IsPerfect E → rank (E⟦n⟧) = (-1 : ℤ) ^ n.natAbs * rank E
  rank_dual (E : DerivedCategory C) :
    IsPerfect E → rank (monoidal.dual.obj (.op E)) = rank E
  triangle_two_out_of_three (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) :
    (IsPerfect T.obj₁ ∧ IsPerfect T.obj₂ → IsPerfect T.obj₃) ∧
    (IsPerfect T.obj₂ ∧ IsPerfect T.obj₃ → IsPerfect T.obj₁) ∧
    (IsPerfect T.obj₁ ∧ IsPerfect T.obj₃ → IsPerfect T.obj₂)
  triangle_rank (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C))
    (h₁ : IsPerfect T.obj₁) (h₂ : IsPerfect T.obj₂) (h₃ : IsPerfect T.obj₃) :
    rank T.obj₂ = rank T.obj₁ + rank T.obj₃

namespace PerfectComplexTheory

variable (P : PerfectComplexTheory (C := C))

/-- In a distinguished triangle, perfectness of the first two objects implies perfectness of
the cone. -/
theorem perfect_cone (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C))
    (h₁ : P.IsPerfect T.obj₁) (h₂ : P.IsPerfect T.obj₂) :
    P.IsPerfect T.obj₃ :=
  (P.triangle_two_out_of_three T hT).1 ⟨h₁, h₂⟩

/-- Additivity of virtual rank in a distinguished triangle. -/
theorem rank_additive (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C))
    (h₁ : P.IsPerfect T.obj₁) (h₂ : P.IsPerfect T.obj₂) (h₃ : P.IsPerfect T.obj₃) :
    P.rank T.obj₂ = P.rank T.obj₁ + P.rank T.obj₃ :=
  P.triangle_rank T hT h₁ h₂ h₃

end PerfectComplexTheory

-/

/-
Retired provisional site comparison.  The derived equivalence and all homology/Ext comparisons
were fields rather than constructions from the actual ringed-site comparison.

/-- Comparison of derived module theories on two genuinely different sites. -/
structure DerivedSiteComparison
    (D : Type u) [Category.{v} D] [Abelian D] [HasDerivedCategory.{w} D] where
  inverseImage : DerivedCategory C ⥤ DerivedCategory D
  directImage : DerivedCategory D ⥤ DerivedCategory C
  equivalence : DerivedCategory C ≌ DerivedCategory D
  inverseImageIso : equivalence.functor ≅ inverseImage
  homologyComparison (i : ℤ) (E : DerivedCategory C) :
    (DerivedCategory.homologyFunctor D i).obj (inverseImage.obj E) ≅
      (DerivedCategory.homologyFunctor D i).obj (equivalence.functor.obj E)
  extComparison (E F : DerivedCategory C) (n : ℤ) :
    DerivedExt E F n ≃
      DerivedExt (inverseImage.obj E) (inverseImage.obj F) n

-/

/-- A categorical cartesian square used by geometric cotangent base change. -/
structure GeometricBaseChangeSquare
    (Geom : Type u) [Category.{v} Geom] where
  X : Geom
  Y : Geom
  X' : Geom
  Y' : Geom
  top : X' ⟶ X
  left : X' ⟶ Y'
  right : X ⟶ Y
  bottom : Y' ⟶ Y
  cartesian : IsPullback top left right bottom

/-
Retired provisional global cotangent, morphism-criterion, and resolution-operation calculi.
Their constructions and the advertised base-change, amplitude, and stability theorems were
supplied as fields.

/-- A globally constructed cotangent theory on a geometric category. -/
structure GeometricTheory
    (Geom : Type u) [Category.{v} Geom] where
  absolute : Geom → DerivedCategory C
  relative {X Y : Geom} (f : X ⟶ Y) : DerivedCategory C
  pullback {X Y : Geom} (f : X ⟶ Y) : DerivedCategory C ⥤ DerivedCategory C
  transitivity {X Y : Geom} (f : X ⟶ Y) : TransitivityTriangle (C := C)
  transitivity_pulledTarget {X Y : Geom} (f : X ⟶ Y) :
    (transitivity f).pulledTarget = (pullback f).obj (absolute Y)
  transitivity_absoluteSource {X Y : Geom} (f : X ⟶ Y) :
    (transitivity f).absoluteSource = absolute X
  transitivity_relative {X Y : Geom} (f : X ⟶ Y) :
    (transitivity f).relative = relative f
  pullback_id (X : Geom) : pullback (𝟙 X) ≅ 𝟭 _
  pullback_comp {X Y Z : Geom} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f
  Flat : MorphismProperty Geom
  baseChangeMap (s : GeometricBaseChangeSquare Geom) :
    (pullback s.top).obj (relative s.right) ⟶ relative s.left
  flatBaseChange_isIso (s : GeometricBaseChangeSquare Geom) :
    Flat s.bottom → IsIso (baseChangeMap s)

/-- Smooth, etale, unramified, and lci criteria for a geometric cotangent complex. -/
structure MorphismCriteria
    (Geom : Type u) [Category.{v} Geom]
    (L : {X Y : Geom} → (X ⟶ Y) → DerivedCategory C) where
  Smooth : {X Y : Geom} → (X ⟶ Y) → Prop
  Etale : {X Y : Geom} → (X ⟶ Y) → Prop
  Unramified : {X Y : Geom} → (X ⟶ Y) → Prop
  LCI : {X Y : Geom} → (X ⟶ Y) → Prop
  etale_iff_isZero {X Y : Geom} (f : X ⟶ Y) : Etale f ↔ IsZero (L f)
  smooth_implies_amplitude_zero {X Y : Geom} (f : X ⟶ Y) :
    Smooth f → HasCohomologicalAmplitude (L f) 0 0
  unramified_implies_hZero_zero {X Y : Geom} (f : X ⟶ Y) :
    Unramified f → IsZero ((DerivedCategory.homologyFunctor C 0).obj (L f))
  lci_iff_amplitude {X Y : Geom} (f : X ⟶ Y) :
    LCI f ↔ HasCohomologicalAmplitude (L f) (-1) 0

/-- Stability operations for global two-term resolutions.  The resulting resolutions still
compare by derived isomorphisms, never by equality of complexes. -/
structure GlobalResolutionOperations
    (FiniteLocallyFree : C → Prop) where
  pullbackFunctor : DerivedCategory C ⥤ DerivedCategory C
  pullbackObject : C ⥤ C
  pullback_finiteLocallyFree (M : C) :
    FiniteLocallyFree M → FiniteLocallyFree (pullbackObject.obj M)
  pullbackResolution {E : DerivedCategory C} :
    DerivedObstructionTheory.GlobalTwoTermResolution FiniteLocallyFree E →
      DerivedObstructionTheory.GlobalTwoTermResolution FiniteLocallyFree
        (pullbackFunctor.obj E)
  externalSumObject : C ⥤ C
  externalSum_finiteLocallyFree (M : C) :
    FiniteLocallyFree M → FiniteLocallyFree (externalSumObject.obj M)
  externalSumResolution {E F : DerivedCategory C} :
    DerivedObstructionTheory.GlobalTwoTermResolution FiniteLocallyFree E →
    DerivedObstructionTheory.GlobalTwoTermResolution FiniteLocallyFree F →
    DerivedObstructionTheory.GlobalTwoTermResolution FiniteLocallyFree (E ⊞ F)

-/

end GromovWitten.AlgebraicGeometry.CotangentComplex
