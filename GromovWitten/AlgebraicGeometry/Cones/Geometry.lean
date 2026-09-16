/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.Affine
import GromovWitten.AlgebraicGeometry.Cones.Stack
import GromovWitten.AlgebraicGeometry.CotangentComplex.Perfect

/-!
# Relative spectra, geometric normal cones, and derived Picard stacks

This file exposes the canonical affine normal-cone morphism.  Earlier provisional records for
relative spectra, relative Proj, global normal cones, deformation spaces, and a
resolution-independent `h¹/h⁰` construction have been removed: those records merely accepted
the desired objects and comparison theorems as fields and therefore did not constitute
constructions.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

/-
Retired provisional APIs.  These definitions accepted the relative spectrum, its algebra
points, base-change equivalences, and the relative Proj as caller data.  Keeping them active
would falsely present those hard constructions as completed interfaces.

/-- The actual groupoid fibre of a stack morphism over a fixed object of the base stack. -/
structure StackMorphismFiber {total base : FppfStack.{u}}
    (projection : StackHom total base) (T : Scheme.{u}) (x : StackFiber base T) where
  object : StackFiber total T
  comparison : (StackHom.appFunctor projection T).obj object ≅ x

namespace StackMorphismFiber

variable {total base : FppfStack.{u}} {projection : StackHom total base}
  {T : Scheme.{u}} {x : StackFiber base T}

/-- Arrows in the fibre are arrows of the total stack commuting with the comparison to the
fixed base object. -/
structure Hom (a b : StackMorphismFiber projection T x) where
  hom : a.object ⟶ b.object
  comm : (StackHom.appFunctor projection T).map hom ≫ b.comparison.hom =
    a.comparison.hom

@[ext]
theorem Hom.ext {a b : StackMorphismFiber projection T x} (f g : Hom a b)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact h

instance : Category (StackMorphismFiber projection T x) where
  Hom := Hom
  id a := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by simp [f.comm, g.comm]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- Stack fibres are groupoids, hence so are fixed-object fibres of a stack morphism. -/
noncomputable instance : Groupoid (StackMorphismFiber projection T x) where
  inv f :=
    { hom := inv f.hom
      comm := by
        apply (cancel_epi ((StackHom.appFunctor projection T).map f.hom)).1
        rw [← Category.assoc, ← Functor.map_comp]
        simp [f.comm] }
  inv_comp f := Hom.ext _ _ (by change inv f.hom ≫ f.hom = 𝟙 _; simp)
  comp_inv f := Hom.ext _ _ (by change f.hom ≫ inv f.hom = 𝟙 _; simp)

end StackMorphismFiber

/-- A nonnegatively graded algebra generated in degree one.  Generation is the concrete span of
degree-one monomials in every homogeneous piece. -/
structure DegreeOneGeneratedGradedAlgebra (R : Type u) [CommRing R] where
  component : ℕ → Type u
  addCommGroup (n : ℕ) : AddCommGroup (component n)
  module (n : ℕ) : Module R (component n)
  one : component 0
  mul {m n : ℕ} : component m → component n → component (m + n)
  mul_add_left {m n : ℕ} (x y : component m) (z : component n) :
    mul (x + y) z = mul x z + mul y z
  mul_add_right {m n : ℕ} (x : component m) (y z : component n) :
    mul x (y + z) = mul x y + mul x z
  smul_mul {m n : ℕ} (r : R) (x : component m) (y : component n) :
    mul (r • x) y = r • mul x y
  monomial (n : ℕ) : (Fin n → component 1) → component n
  generated_degree_one (n : ℕ) :
    Submodule.span R (Set.range (monomial n)) = ⊤

attribute [instance] DegreeOneGeneratedGradedAlgebra.addCommGroup
  DegreeOneGeneratedGradedAlgebra.module

/-- A relative spectrum over a stack, expressed by its groupoid-valued functor of algebra
points.  The equivalence is in every fibre and is compatible with pullback. -/
structure RelativeSpec (base : FppfStack.{u}) where
  /-- The relative-affine input is an actual sheaf of commutative rings on the big fppf site,
  rather than an unstructured carrier type. -/
  algebraSheaf : Sheaf (Sites.bigFppfStackTopology base) CommRingCat.{u + 1}
  AlgebraPoint (T : Scheme.{u}) (x : StackFiber base T) : Type u
  algebraPointCategory (T : Scheme.{u}) (x : StackFiber base T) :
    Category.{u} (AlgebraPoint T x)
  algebraPointGroupoid (T : Scheme.{u}) (x : StackFiber base T) :
    IsGroupoid.{u} (AlgebraPoint T x)
  total : FppfStack.{u}
  projection : StackHom total base
  pointsEquivalence (T : Scheme.{u}) (x : StackFiber base T) :
    StackMorphismFiber projection T x ≌ AlgebraPoint T x
  pullbackAlgebraPoint {S T : Scheme.{u}} (f : S ⟶ T) (x : StackFiber base T) :
    AlgebraPoint T x ⥤ AlgebraPoint S ((stackPullback base f).obj x)

attribute [instance] RelativeSpec.algebraPointCategory RelativeSpec.algebraPointGroupoid

/-- Compatibility of a relative spectrum with arbitrary base change. -/
structure RelativeSpecBaseChange
    {X Y : FppfStack.{u}} (A : RelativeSpec Y) (f : StackHom X Y) where
  pullbackSpec : RelativeSpec X
  square : StackTwoPullback.Genuine A.projection f
  comparison : StackEquivalenceData pullbackSpec.total square.pullback

/-- A graded cone represented by a relative spectrum, with its vertex and contraction action. -/
structure RelativeGradedCone (base : FppfStack.{u}) (O : FppfScalarRings.{u}) where
  baseRing : Type u
  [baseCommRing : CommRing baseRing]
  /-- The grading and degree-one generation are mathematical structure, not an unrelated
  proposition supplied next to an ungraded carrier. -/
  algebra : DegreeOneGeneratedGradedAlgebra baseRing
  spec : RelativeSpec base
  cone : ConeStack base O
  specComparison : StackEquivalenceData spec.total cone.total

/-- Relative Proj of a degree-one generated graded algebra, characterized by its groupoid of
homogeneous invertible quotients in every actual projection fibre. -/
structure RelativeProj {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (A : RelativeGradedCone base O) where
  total : FppfStack.{u}
  projection : StackHom total base
  QuotientPoint (T : Scheme.{u}) (x : StackFiber base T) : Type u
  [quotientPointCategory (T : Scheme.{u}) (x : StackFiber base T) :
    Category.{u} (QuotientPoint T x)]
  [quotientPointGroupoid (T : Scheme.{u}) (x : StackFiber base T) :
    IsGroupoid.{u} (QuotientPoint T x)]
  pointsEquivalence (T : Scheme.{u}) (x : StackFiber base T) :
    StackMorphismFiber projection T x ≌ QuotientPoint T x

attribute [instance] RelativeProj.quotientPointCategory RelativeProj.quotientPointGroupoid

/-- Relative Proj commutes with arbitrary stack base change through a genuine 2-pullback. -/
structure RelativeProjBaseChange
    {X Y : FppfStack.{u}} {O : FppfScalarRings.{u}}
    {A : RelativeGradedCone Y O} (P : RelativeProj A) (f : StackHom X Y) where
  baseChangedAlgebra : RelativeGradedCone X O
  baseChangedProj : RelativeProj baseChangedAlgebra
  square : StackTwoPullback.Genuine P.projection f
  comparison : StackEquivalenceData baseChangedProj.total square.pullback

-/

/-- An ideal is generated by a displayed finite regular sequence. -/
def IdealGeneratedByRegularSequence (R : Type u) [CommRing R] (I : Ideal R) : Prop :=
  ∃ (n : ℕ) (f : Fin n → R),
    Ideal.span (Set.range f) = I ∧ RingTheory.Sequence.IsRegular R (List.ofFn f)

/-
Retired provisional API.  It supplied both a relative spectrum and its cone-stack realization,
then stored the vector-bundle characterization as a field.

/-- The abelian cone of a coherent sheaf, with its symmetric-algebra functor of points. -/
structure AbelianConeGeometry (base : FppfStack.{u}) (O : FppfScalarRings.{u}) where
  [weakSheafify (Z : Sites.BigFppfStackSite base) :
    HasWeakSheafify ((Sites.bigFppfRingedSite base).topology.over Z)
      AddCommGrpCat.{u + 1}]
  [wEquals (Z : Sites.BigFppfStackSite base) :
    ((Sites.bigFppfRingedSite base).topology.over Z).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1}]
  sheaf : (Sites.bigFppfRingedSite base).Modules
  moduleOperations : Modules.Operations (Sites.bigFppfRingedSite base)
  spec : RelativeSpec base
  cone : AbelianConeStack base O
  comparison : StackEquivalenceData spec.total cone.total
  rank : ℕ
  vectorBundle_iff : Modules.IsFiniteLocallyFreeOfRank
      (Sites.bigFppfRingedSite base) sheaf rank ↔
    ∃ V : VectorBundleStack base O,
      Nonempty (ConeStack.Iso V.toConeStack cone.toConeStack)

-/

namespace AffineNormalConeComparison

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- The affine normal-cone comparison map is the canonical degree-one Rees map.  There is no
structure in this API in which a caller can install an unrelated map. -/
noncomputable abbrev coordinateMap :=
  AffineNormalCone.normalSheafCoordinateMap R I

/-- Closedness of the affine normal-cone inclusion is a theorem of the canonical map, not a
supplied field. -/
theorem surjective :
    Function.Surjective (AffineNormalCone.normalSheafCoordinateMap R I) :=
  AffineNormalCone.normalSheafCoordinateMap_surjective R I

/-- The resulting morphism of affine schemes is the canonical normal-cone inclusion. -/
noncomputable abbrev schemeMap :
    AffineNormalCone.scheme R I ⟶ AffineNormalCone.normalSheaf R I :=
  AffineNormalCone.coneToNormalSheaf R I

/-- Closedness is inherited from the proved coordinate-ring surjection. -/
theorem closedImmersion :
    _root_.AlgebraicGeometry.IsClosedImmersion
      (AffineNormalCone.coneToNormalSheaf R I) := by
  infer_instance

end AffineNormalConeComparison

/-
Retired provisional APIs.  These records accepted the normal cone, normal sheaf, deformation
space, fibres, base-change equivalences, and exact cone quotient as fields.  None had a
constructor from an immersion or Rees algebra, so keeping them active would allow precisely the
theorem-as-data shortcut this development excludes.

/-- An actual flat base change of a stack.  This replaces caller-selected test types: every
flat morphism into `base` is an inhabitant, and the identity gives a canonical inhabitant. -/
structure FlatStackBaseChange (base : FppfStack.{u}) where
  source : FppfStack.{u}
  map : StackHom source base
  flat : map.Flat

namespace FlatStackBaseChange

/-- The identity is an actual flat base change, so the quantified base-change type is never
vacuous. -/
noncomputable def identity (base : FppfStack.{u}) : FlatStackBaseChange base where
  source := base
  map := Pseudofunctor.StrongTrans.id base.toPseudofunctor
  flat := StackHom.id_hasRepresentableProperty
    (@_root_.AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) base

instance (base : FppfStack.{u}) : Nonempty (FlatStackBaseChange base) :=
  ⟨identity base⟩

end FlatStackBaseChange

/-- An actual smooth base change of a stack. -/
structure SmoothStackBaseChange (base : FppfStack.{u}) where
  source : FppfStack.{u}
  map : StackHom source base
  smooth : map.Smooth

namespace SmoothStackBaseChange

/-- The identity is an actual smooth base change, so the quantified base-change type is never
vacuous. -/
noncomputable def identity (base : FppfStack.{u}) : SmoothStackBaseChange base where
  source := base
  map := Pseudofunctor.StrongTrans.id base.toPseudofunctor
  smooth := by
    refine ⟨Pseudofunctor.StrongTrans.id base.toPseudofunctor,
      ⟨StackIso2.refl _⟩, ?_⟩
    intro T x
    refine ⟨⟨StackHom.identityPresentation base T x, ?_⟩⟩
    change _root_.AlgebraicGeometry.Smooth (𝟙 T)
    infer_instance

instance (base : FppfStack.{u}) : Nonempty (SmoothStackBaseChange base) :=
  ⟨identity base⟩

end SmoothStackBaseChange

/-- Geometric normal-cone data for a closed immersion. -/
structure NormalConeGeometry (base : FppfStack.{u}) (O : FppfScalarRings.{u}) where
  ambient : FppfStack.{u}
  immersion : StackHom base ambient
  immersion_closed : immersion.ClosedImmersion
  [weakSheafify (Z : Sites.BigFppfStackSite base) :
    HasWeakSheafify ((Sites.bigFppfRingedSite base).topology.over Z)
      AddCommGrpCat.{u + 1}]
  [wEquals (Z : Sites.BigFppfStackSite base) :
    ((Sites.bigFppfRingedSite base).topology.over Z).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1}]
  idealSheaf : (Sites.bigFppfRingedSite base).Modules
  conormalSheaf : (Sites.bigFppfRingedSite base).Modules
  conormalAlgebra :
    Sheaf (Sites.bigFppfStackTopology base) CommRingCat.{u + 1}
  normalCone : ConeStack base O
  normalSheaf : AbelianConeStack base O
  abelianHull : AbelianHull normalCone
  hullComparison : ConeStack.Iso abelianHull.hull.toConeStack normalSheaf.toConeStack
  regularIso : immersion.RegularImmersion →
    ConeStack.Iso normalCone normalSheaf.toConeStack
  flatPullback (s : FlatStackBaseChange base) : ConeStackBaseChange normalCone s.map
  flatBaseChangeCone (s : FlatStackBaseChange base) : ConeStack s.source O
  flatBaseChangeIso (s : FlatStackBaseChange base) :
    ConeStack.Iso (flatBaseChangeCone s) (flatPullback s).pullback
  productPullback : StackTwoPullback.Genuine normalCone.projection normalCone.projection
  productCone : ConeStack base O
  productEquivalence : StackEquivalenceData productCone.total productPullback.pullback

/-- Exact cone sequence associated to a smooth ambient morphism. -/
structure SmoothAmbientConeSequence
    {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (C : ConeStack base O) where
  relativeTangent : AbelianConeStack base O
  ambientCone : ConeStack base O
  tangentAction : ConeStackAction relativeTangent ambientCone
  quotient : ConeQuotientPresentation relativeTangent ambientCone
  quotientIso : ConeStack.Iso quotient.quotient C

/-- Rees-algebra deformation to the normal cone, including its two geometric fibres and smooth
base-change comparison. -/
structure DeformationToNormalCone
    (base : FppfStack.{u}) (O : FppfScalarRings.{u})
    (N : NormalConeGeometry base O) where
  affineLine : FppfStack.{u}
  puncturedAffineLine : FppfStack.{u}
  family : FppfStack.{u}
  toAffineLine : StackHom family affineLine
  familyToBase : StackHom family base
  puncturedMap : StackHom puncturedAffineLine affineLine
  zeroMap : StackHom base affineLine
  genericFiber : StackTwoPullback.Genuine toAffineLine puncturedMap
  specialFiber : StackTwoPullback.Genuine toAffineLine zeroMap
  genericModel : FppfStack.{u}
  genericToAmbient : StackHom genericModel N.ambient
  genericComparison : StackEquivalenceData genericFiber.pullback genericModel
  specialComparison : StackEquivalenceData specialFiber.pullback N.normalCone.total
  familyPullback (s : SmoothStackBaseChange base) :
    StackTwoPullback.Genuine familyToBase s.map
  smoothBaseChangedFamily (s : SmoothStackBaseChange base) : FppfStack.{u}
  smoothBaseChangeComparison (s : SmoothStackBaseChange base) :
    StackEquivalenceData (smoothBaseChangedFamily s) (familyPullback s).pullback

/-- A short exact sequence of abelian cone stacks. -/
structure ShortExactConeStacks
    {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (A B C : AbelianConeStack base O) where
  inclusion : StackHom A.total B.total
  projection : StackHom B.total C.total
  compositeZero : StackIso2
    (Pseudofunctor.StrongTrans.vcomp inclusion projection)
    (Pseudofunctor.StrongTrans.vcomp A.projection C.vertex)
  quotient : ConeQuotientPresentation A B.toConeStack
  quotientIso : ConeStack.Iso quotient.quotient C.toConeStack

-/

/-
Retired provisional `DerivedPicardStack`.  It accepted the desired stack, every vector-bundle
presentation, and all comparison isomorphisms as fields.  A genuine replacement must construct
the quotient stack from an actual two-term complex and prove invariance under quasi-isomorphism.

/-- Resolution-independent realization of `h¹/h⁰` for a derived complex. -/
structure DerivedPicardStack
    {C : Type u} [Category.{u} C] [Abelian C] [HasDerivedCategory.{u} C]
    (base : FppfStack.{u}) (O : FppfScalarRings.{u})
    (E : DerivedCategory C)
    (FiniteLocallyFree : C → Prop)
    (IsPerfect : DerivedCategory C → Prop) where
  stack : AbelianConeStack base O
  presentation
      (F : DerivedObstructionTheory.GlobalTwoTermResolution FiniteLocallyFree E) :
    VectorBundleStack base O
  presentationIso
      (F : DerivedObstructionTheory.GlobalTwoTermResolution FiniteLocallyFree E) :
    ConeStack.Iso (presentation F).toConeStack stack.toConeStack
  perfectPresentation
      (h : DerivedObstructionTheory.PerfectData IsPerfect E) :
    VectorBundleStack base O
  perfectPresentationIso
      (h : DerivedObstructionTheory.PerfectData IsPerfect E) :
    ConeStack.Iso (perfectPresentation h).toConeStack stack.toConeStack

-/

end GromovWitten.AlgebraicGeometry
