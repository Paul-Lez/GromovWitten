/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.Stack
import GromovWitten.AlgebraicGeometry.Stacks.TwoPullbackBilimit

/-!
# Base change and fibre products of cone stacks

The total stack of a cone stack `C : ConeStack base O` is base changed along a morphism of base
stacks `f : StackHom base' base` by the genuine two-pullback `C.total ×_base base'` of
`Stacks/TwoPullback.lean`, whose fibre over a test scheme `T` is the groupoid of triples
`(x, b, α)` with `x` in `C.total T`, `b` in `base' T` and `α : projection x ≅ f b` an
isomorphism of the base fibre (never an equality).

* `ConeStack.baseChangeTotal`, `ConeStack.baseChangeProjection`, `ConeStack.baseChangeFst`: the
  two-pullback and its two projections.
* `ConeStack.baseChangeVertex`: the vertex section, produced by the bicategorical universal
  property (`StackTwoPullback.canonicalLift`) from the cone whose legs are `f ≫ C.vertex` and
  the identity; `ConeStack.baseChangeVertexProjectionIso` is the resulting section property,
  which is the universal property's own comparison cell, not an assumption.
* `ConeStack.baseChangeContraction`: the fibrewise contraction, contracting the first component
  and transporting the comparison isomorphism `α` through `contractionProjectionIso`.
* `ConeStack.baseChangeContractionProjectionIso`: the base change lies over the new base on the
  nose, because contraction does not move the second component.
* `ConeStack.baseChange`: the resulting `ConeStack base' O`.

## What is conditional

`ConeStack` deliberately does not encode the higher coherence laws of its five comparison cells
(see the module documentation of `Cones/Stack.lean`).  Transporting the contraction structure
through a two-pullback needs exactly those laws: the comparison isomorphism of a point of the
base change is an arrow of the base stack, so each contraction comparison of `C` must act on it
through `contractionProjectionIso`.  The five equations are collected in the `Prop`-valued
structure `ConeStack.BaseChangeCoherence`, which is an explicit hypothesis of `baseChange`; no
field of the produced `ConeStack` is assumed.  The constructions of the total stack, the two
projections, the vertex, its section property and the contraction functors themselves are
unconditional.

The `O`-indexing is unchanged by the base change: the scalar rings `O.ring T` depend only on
the test scheme, so for `O = canonicalFppfScalarRings` no comparison of scalars is needed.

## Fibre products

The same construction with the two projections of two cone stacks `C D : ConeStack base O` gives
their fibre product over the base:

* `ConeStack.prodTotal`, `ConeStack.prodFst`, `ConeStack.prodSnd`, `ConeStack.prodProjection`;
* `ConeStack.prodVertex` and `ConeStack.prodVertexProjectionIso`, again from the bicategorical
  universal property applied to the cone formed by the two vertices and their section cells;
* `ConeStack.prodContraction`, contracting both components and transporting the comparison
  isomorphism through both projection comparisons, and `ConeStack.prodContractionProjectionIso`;
* `ConeStack.prod`, the fibre product, under the coherence hypotheses `ConeStack.ProdCoherence`
  (the analogue of `BaseChangeCoherence`, with all five laws stated as the compatibility squares
  they are used for);
* `ConeStack.prodHomFst`, `ConeStack.prodHomSnd`: the two projections as morphisms of cone
  stacks.  Both are strictly equivariant for the contractions; the base comparison of the first
  is an identity and that of the second is the comparison 2-cell of the two-pullback.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

namespace ConeStack

universe u

section BaseChange

variable {base base' : FppfStack.{u}} {O : FppfScalarRings.{u}}
variable (C : ConeStack base O) (f : StackHom base' base)

/-- The total stack of the base change of a cone stack: the genuine two-pullback of the
projection along the base morphism.  Its fibres are the triples `(x, b, α)` with
`α : projection x ≅ f b`. -/
noncomputable abbrev baseChangeTotal : FppfStack.{u} :=
  fiberTwoPullbackStack C.projection f

/-- The projection of the base change to the new base. -/
noncomputable abbrev baseChangeProjection : StackHom (baseChangeTotal C f) base' :=
  fiberTwoPullbackSnd C.projection f

/-- The projection of the base change to the original cone. -/
noncomputable abbrev baseChangeFst : StackHom (baseChangeTotal C f) C.total :=
  fiberTwoPullbackFst C.projection f

/-- Contraction of the base change on a fibre: contract the first component and transport the
comparison isomorphism through the projection comparison of the contraction. -/
noncomputable def baseChangeContraction (T : Scheme.{u}) (r : O.ring T) :
    StackFiber (baseChangeTotal C f) T ⥤ StackFiber (baseChangeTotal C f) T where
  obj p :=
    { fst := (C.contraction T r).obj (CategoricalPullback.fst p)
      snd := CategoricalPullback.snd p
      iso := ((C.contractionProjectionIso T r).app (CategoricalPullback.fst p)).trans
        (CategoricalPullback.iso p) }
  map {p q} k :=
    { fst := (C.contraction T r).map k.fst
      snd := k.snd
      w := by
        have hnat := (C.contractionProjectionIso T r).hom.naturality k.fst
        dsimp at hnat ⊢
        rw [← Category.assoc, hnat, Category.assoc, k.w, Category.assoc] }
  map_id p := by
    apply CategoricalPullback.hom_ext
    · exact (C.contraction T r).map_id _
    · rfl
  map_comp k l := by
    apply CategoricalPullback.hom_ext
    · exact (C.contraction T r).map_comp _ _
    · rfl

/-- The bicategorical cone whose lift is the vertex of the base change: the first leg is the
vertex of `C` precomposed with the base morphism, the second leg is the identity. -/
noncomputable def baseChangeVertexCone :
    StackTwoPullback.Cone (f := C.projection) (g := f) base' where
  fst := Pseudofunctor.StrongTrans.vcomp f C.vertex
  snd := Pseudofunctor.StrongTrans.id base'.toPseudofunctor
  comparison :=
    (StackIso2.associator f C.vertex C.projection).trans
      ((StackIso2.whiskerLeft f C.vertexProjectionIso).trans
        ((StackIso2.rightUnitor f).trans (StackIso2.leftUnitor f).symm))

/-- The vertex section of the base change, obtained from the bicategorical universal property
of the two-pullback. -/
noncomputable def baseChangeVertex : StackHom base' (baseChangeTotal C f) :=
  StackTwoPullback.canonicalLift C.projection f (baseChangeVertexCone C f)

/-- The vertex of the base change is a genuine section of its projection. -/
noncomputable def baseChangeVertexProjectionIso :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (baseChangeVertex C f) (baseChangeProjection C f))
      (Pseudofunctor.StrongTrans.id base'.toPseudofunctor) :=
  StackTwoPullback.canonicalLiftSndIso C.projection f (baseChangeVertexCone C f)

/-- The contraction of the base change does not move the second component, so it lies over the
new base on the nose. -/
noncomputable def baseChangeContractionProjectionIso (T : Scheme.{u}) (r : O.ring T) :
    baseChangeContraction C f T r ⋙ StackHom.appFunctor (baseChangeProjection C f) T ≅
      StackHom.appFunctor (baseChangeProjection C f) T :=
  CategoryTheory.Iso.refl (StackHom.appFunctor (baseChangeProjection C f) T)

/-- The coherence laws relating the contraction comparison isomorphisms of a cone stack to its
projection comparison.

`ConeStack` deliberately does not encode the higher coherence laws of its comparison cells (see
the module documentation of `Cones/Stack.lean`), but transporting the contraction structure
through a two-pullback requires exactly these compatibilities: the comparison isomorphism of a
point of the base change is an arrow of the base stack, and every contraction isomorphism has
to act on it through `contractionProjectionIso`.  They are therefore *hypotheses* of the
base-change construction below, not consequences of `ConeStack`. -/
structure BaseChangeCoherence : Prop where
  /-- Contraction by one is compatible with the projection comparison. -/
  one (T : Scheme.{u}) (x : StackFiber C.total T) :
    (StackHom.appFunctor C.projection T).map ((C.contractionOneIso T).hom.app x) =
      (C.contractionProjectionIso T 1).hom.app x
  /-- Contraction by a product is compatible with the projection comparison. -/
  mul (T : Scheme.{u}) (r s : O.ring T) (x : StackFiber C.total T) :
    (StackHom.appFunctor C.projection T).map ((C.contractionMulIso T r s).hom.app x) ≫
        (C.contractionProjectionIso T r).hom.app ((C.contraction T s).obj x) ≫
          (C.contractionProjectionIso T s).hom.app x =
      (C.contractionProjectionIso T (r * s)).hom.app x
  /-- Contraction of the vertex is compatible with the projection comparison, on the points of
  the new base. -/
  vertex (T : Scheme.{u}) (r : O.ring T) (b : StackFiber base' T) :
    (StackHom.appFunctor C.projection T).map
          ((C.contractionVertexIso T r).app ((StackHom.appFunctor f T).obj b)).hom ≫
        (CategoricalPullback.iso
          ((StackHom.appFunctor (baseChangeVertex C f) T).obj b)).hom =
      (CategoricalPullback.iso ((StackHom.appFunctor (baseChangeVertex C f) T ⋙
          baseChangeContraction C f T r).obj b)).hom ≫
        (StackHom.appFunctor f T).map (𝟙 b)
  /-- Contraction by zero is compatible with the projection comparison and with the section
  property of the vertex, on the points of the base change. -/
  zero (T : Scheme.{u}) (p : StackFiber (baseChangeTotal C f) T) :
    (StackHom.appFunctor C.projection T).map
          (((C.contractionZeroIso T).app (CategoricalPullback.fst p)).trans
            ((StackHom.appFunctor C.vertex T).mapIso (CategoricalPullback.iso p))).hom ≫
        (CategoricalPullback.iso ((StackHom.appFunctor (baseChangeVertex C f) T).obj
          ((StackHom.appFunctor (baseChangeProjection C f) T).obj p))).hom =
      (((C.contractionProjectionIso T 0).app (CategoricalPullback.fst p)).trans
          (CategoricalPullback.iso p)).hom ≫
        (StackHom.appFunctor f T).map (𝟙 (CategoricalPullback.snd p))
  /-- Contraction commutes with reindexing compatibly with the projection comparison, on the
  points of the base change. -/
  pullback {S T : Scheme.{u}} (h : S ⟶ T) (r : O.ring T)
      (p : StackFiber (baseChangeTotal C f) T) :
    (StackHom.appFunctor C.projection S).map
          ((C.contractionPullbackIso h r).app (CategoricalPullback.fst p)).hom ≫
        (CategoricalPullback.iso ((stackPullback (baseChangeTotal C f) h ⋙
          baseChangeContraction C f S (O.pullback h r)).obj p)).hom =
      (CategoricalPullback.iso ((baseChangeContraction C f T r ⋙
          stackPullback (baseChangeTotal C f) h).obj p)).hom ≫
        (StackHom.appFunctor f S).map
          (𝟙 ((stackPullback base' h).obj (CategoricalPullback.snd p)))

variable (hc : BaseChangeCoherence C f)

include hc

/-- Contraction by one on the base change is the identity. -/
noncomputable def baseChangeContractionOneIso (T : Scheme.{u}) :
    baseChangeContraction C f T 1 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun p => CategoricalPullback.mkIso
      ((C.contractionOneIso T).app (CategoricalPullback.fst p))
      (CategoryTheory.Iso.refl (CategoricalPullback.snd p)) (by
        dsimp [baseChangeContraction]
        rw [hc.one T (CategoricalPullback.fst p)]
        simp))
    (fun {p q} k => by
      apply CategoricalPullback.hom_ext
      · exact (C.contractionOneIso T).hom.naturality k.fst
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Contraction by a product on the base change is the composite of the two contractions. -/
noncomputable def baseChangeContractionMulIso (T : Scheme.{u}) (r s : O.ring T) :
    baseChangeContraction C f T (r * s) ≅
      baseChangeContraction C f T s ⋙ baseChangeContraction C f T r :=
  NatIso.ofComponents
    (fun p => CategoricalPullback.mkIso
      ((C.contractionMulIso T r s).app (CategoricalPullback.fst p))
      (CategoryTheory.Iso.refl (CategoricalPullback.snd p)) (by
        dsimp [baseChangeContraction]
        rw [← hc.mul T r s (CategoricalPullback.fst p)]
        simp))
    (fun {p q} k => by
      apply CategoricalPullback.hom_ext
      · exact (C.contractionMulIso T r s).hom.naturality k.fst
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Contraction by zero on the base change is the vertex section of its projection. -/
noncomputable def baseChangeContractionZeroIso (T : Scheme.{u}) :
    baseChangeContraction C f T 0 ≅
      StackHom.appFunctor (baseChangeProjection C f) T ⋙
        StackHom.appFunctor (baseChangeVertex C f) T :=
  NatIso.ofComponents
    (fun p => CategoricalPullback.mkIso
      (((C.contractionZeroIso T).app (CategoricalPullback.fst p)).trans
        ((StackHom.appFunctor C.vertex T).mapIso (CategoricalPullback.iso p)))
      (CategoryTheory.Iso.refl (CategoricalPullback.snd p)) (hc.zero T p))
    (fun {p q} k => by
      apply CategoricalPullback.hom_ext
      · change (C.contraction T 0).map k.fst ≫
            ((C.contractionZeroIso T).hom.app (CategoricalPullback.fst q) ≫
              (StackHom.appFunctor C.vertex T).map (CategoricalPullback.iso q).hom) =
          ((C.contractionZeroIso T).hom.app (CategoricalPullback.fst p) ≫
              (StackHom.appFunctor C.vertex T).map (CategoricalPullback.iso p).hom) ≫
            (StackHom.appFunctor C.vertex T).map ((StackHom.appFunctor f T).map k.snd)
        rw [← Category.assoc, (C.contractionZeroIso T).hom.naturality k.fst, Category.assoc,
          Category.assoc, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (fun m => (C.contractionZeroIso T).hom.app (CategoricalPullback.fst p) ≫
          (StackHom.appFunctor C.vertex T).map m) k.w
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The vertex of the base change is fixed by every contraction. -/
noncomputable def baseChangeContractionVertexIso (T : Scheme.{u}) (r : O.ring T) :
    StackHom.appFunctor (baseChangeVertex C f) T ⋙ baseChangeContraction C f T r ≅
      StackHom.appFunctor (baseChangeVertex C f) T :=
  NatIso.ofComponents
    (fun b => CategoricalPullback.mkIso
      ((C.contractionVertexIso T r).app ((StackHom.appFunctor f T).obj b))
      (CategoryTheory.Iso.refl b) (hc.vertex T r b))
    (fun {b b'} k => by
      apply CategoricalPullback.hom_ext
      · exact (C.contractionVertexIso T r).hom.naturality ((StackHom.appFunctor f T).map k)
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Contraction on the base change commutes with reindexing of the test scheme. -/
noncomputable def baseChangeContractionPullbackIso {S T : Scheme.{u}} (h : S ⟶ T)
    (r : O.ring T) :
    baseChangeContraction C f T r ⋙ stackPullback (baseChangeTotal C f) h ≅
      stackPullback (baseChangeTotal C f) h ⋙ baseChangeContraction C f S (O.pullback h r) :=
  NatIso.ofComponents
    (fun p => CategoricalPullback.mkIso
      ((C.contractionPullbackIso h r).app (CategoricalPullback.fst p))
      (CategoryTheory.Iso.refl ((stackPullback base' h).obj (CategoricalPullback.snd p)))
      (hc.pullback h r p))
    (fun {p q} k => by
      apply CategoricalPullback.hom_ext
      · exact (C.contractionPullbackIso h r).hom.naturality k.fst
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The base change of a cone stack along a morphism of base stacks, assuming the coherence
laws of `BaseChangeCoherence`.  Its total stack is the genuine two-pullback of the projection
along the base morphism, its projection is the second projection of that two-pullback, and its
vertex is the lift of the vertex of `C`. -/
noncomputable def baseChange : ConeStack base' O where
  total := baseChangeTotal C f
  projection := baseChangeProjection C f
  vertex := baseChangeVertex C f
  vertexProjectionIso := baseChangeVertexProjectionIso C f
  contraction := baseChangeContraction C f
  contractionOneIso := baseChangeContractionOneIso C f hc
  contractionMulIso := baseChangeContractionMulIso C f hc
  contractionZeroIso := baseChangeContractionZeroIso C f hc
  contractionVertexIso := baseChangeContractionVertexIso C f hc
  contractionProjectionIso := baseChangeContractionProjectionIso C f
  contractionPullbackIso := baseChangeContractionPullbackIso C f hc

end BaseChange

section Prod

variable {base : FppfStack.{u}} {O : FppfScalarRings.{u}} (C D : ConeStack base O)

/-- The total stack of the fibre product of two cone stacks over the same base: the genuine
two-pullback of their two projections.  Its fibres are the triples `(x, y, α)` with
`α : C.projection x ≅ D.projection y`. -/
noncomputable abbrev prodTotal : FppfStack.{u} :=
  fiberTwoPullbackStack C.projection D.projection

/-- The first projection of the fibre product. -/
noncomputable abbrev prodFst : StackHom (prodTotal C D) C.total :=
  fiberTwoPullbackFst C.projection D.projection

/-- The second projection of the fibre product. -/
noncomputable abbrev prodSnd : StackHom (prodTotal C D) D.total :=
  fiberTwoPullbackSnd C.projection D.projection

/-- The projection of the fibre product to the base, taken through the first factor. -/
noncomputable abbrev prodProjection : StackHom (prodTotal C D) base :=
  Pseudofunctor.StrongTrans.vcomp (prodFst C D) C.projection

/-- The bicategorical cone whose lift is the vertex of the fibre product: the two legs are the
two vertices, and the comparison cell is built from their section properties. -/
noncomputable def prodVertexCone :
    StackTwoPullback.Cone (f := C.projection) (g := D.projection) base where
  fst := C.vertex
  snd := D.vertex
  comparison := C.vertexProjectionIso.trans D.vertexProjectionIso.symm

/-- The vertex of the fibre product. -/
noncomputable def prodVertex : StackHom base (prodTotal C D) :=
  StackTwoPullback.canonicalLift C.projection D.projection (prodVertexCone C D)

/-- The vertex of the fibre product is a genuine section of its projection. -/
noncomputable def prodVertexProjectionIso :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (prodVertex C D) (prodProjection C D))
      (Pseudofunctor.StrongTrans.id base.toPseudofunctor) :=
  (StackIso2.associator (prodVertex C D) (prodFst C D) C.projection).symm.trans
    ((StackIso2.whiskerRight
        (StackTwoPullback.canonicalLiftFstIso C.projection D.projection (prodVertexCone C D))
        C.projection).trans C.vertexProjectionIso)

/-- Contraction of the fibre product on a fibre: contract both components and transport the
comparison isomorphism through the two projection comparisons. -/
noncomputable def prodContraction (T : Scheme.{u}) (r : O.ring T) :
    StackFiber (prodTotal C D) T ⥤ StackFiber (prodTotal C D) T where
  obj p :=
    { fst := (C.contraction T r).obj (CategoricalPullback.fst p)
      snd := (D.contraction T r).obj (CategoricalPullback.snd p)
      iso := ((C.contractionProjectionIso T r).app (CategoricalPullback.fst p)).trans
        ((CategoricalPullback.iso p).trans
          ((D.contractionProjectionIso T r).app (CategoricalPullback.snd p)).symm) }
  map {p q} k :=
    { fst := (C.contraction T r).map k.fst
      snd := (D.contraction T r).map k.snd
      w := by
        have hC : (StackHom.appFunctor C.projection T).map ((C.contraction T r).map k.fst) ≫
              ((C.contractionProjectionIso T r).app (CategoricalPullback.fst q)).hom =
            ((C.contractionProjectionIso T r).app (CategoricalPullback.fst p)).hom ≫
              (StackHom.appFunctor C.projection T).map k.fst :=
          (C.contractionProjectionIso T r).hom.naturality k.fst
        have hD : (StackHom.appFunctor D.projection T).map k.snd ≫
              ((D.contractionProjectionIso T r).app (CategoricalPullback.snd q)).inv =
            ((D.contractionProjectionIso T r).app (CategoricalPullback.snd p)).inv ≫
              (StackHom.appFunctor D.projection T).map ((D.contraction T r).map k.snd) :=
          (D.contractionProjectionIso T r).inv.naturality k.snd
        simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom, Category.assoc]
        slice_lhs 1 2 => rw [hC]
        slice_lhs 2 3 => rw [k.w]
        slice_lhs 3 4 => rw [hD] }
  map_id p := by
    apply CategoricalPullback.hom_ext
    · exact (C.contraction T r).map_id _
    · exact (D.contraction T r).map_id _
  map_comp k l := by
    apply CategoricalPullback.hom_ext
    · exact (C.contraction T r).map_comp _ _
    · exact (D.contraction T r).map_comp _ _

/-- The contraction of the fibre product lies over the base, through the projection comparison
of the first factor. -/
noncomputable def prodContractionProjectionIso (T : Scheme.{u}) (r : O.ring T) :
    prodContraction C D T r ⋙ StackHom.appFunctor (prodProjection C D) T ≅
      StackHom.appFunctor (prodProjection C D) T :=
  NatIso.ofComponents
    (fun p => (C.contractionProjectionIso T r).app (CategoricalPullback.fst p))
    (fun {_ _} k => (C.contractionProjectionIso T r).hom.naturality k.fst)

/-- The coherence laws needed to transport the contraction structures of two cone stacks to
their fibre product.  As for `BaseChangeCoherence`, they are compatibilities of the contraction
comparison cells with the projection comparisons, which `ConeStack` does not encode; they are
explicit hypotheses of `ConeStack.prod`. -/
structure ProdCoherence : Prop where
  /-- Contraction by one is compatible with both projection comparisons, on the points of the
  fibre product. -/
  one (T : Scheme.{u}) (p : StackFiber (prodTotal C D) T) :
    (StackHom.appFunctor C.projection T).map
          ((C.contractionOneIso T).app (CategoricalPullback.fst p)).hom ≫
        (CategoricalPullback.iso p).hom =
      (CategoricalPullback.iso ((prodContraction C D T 1).obj p)).hom ≫
        (StackHom.appFunctor D.projection T).map
          ((D.contractionOneIso T).app (CategoricalPullback.snd p)).hom
  /-- Contraction by a product is compatible with both projection comparisons, on the points of
  the fibre product. -/
  mul (T : Scheme.{u}) (r s : O.ring T) (p : StackFiber (prodTotal C D) T) :
    (StackHom.appFunctor C.projection T).map
          ((C.contractionMulIso T r s).app (CategoricalPullback.fst p)).hom ≫
        (CategoricalPullback.iso
          ((prodContraction C D T s ⋙ prodContraction C D T r).obj p)).hom =
      (CategoricalPullback.iso ((prodContraction C D T (r * s)).obj p)).hom ≫
        (StackHom.appFunctor D.projection T).map
          ((D.contractionMulIso T r s).app (CategoricalPullback.snd p)).hom
  /-- Contraction of the two vertices is compatible with both projection comparisons. -/
  vertex (T : Scheme.{u}) (r : O.ring T) (b : StackFiber base T) :
    (StackHom.appFunctor C.projection T).map
          ((C.contractionVertexIso T r).app b).hom ≫
        (CategoricalPullback.iso ((StackHom.appFunctor (prodVertex C D) T).obj b)).hom =
      (CategoricalPullback.iso ((StackHom.appFunctor (prodVertex C D) T ⋙
          prodContraction C D T r).obj b)).hom ≫
        (StackHom.appFunctor D.projection T).map
          ((D.contractionVertexIso T r).app b).hom
  /-- Contraction by zero is compatible with the two projection comparisons and the two section
  properties of the vertices, on the points of the fibre product. -/
  zero (T : Scheme.{u}) (p : StackFiber (prodTotal C D) T) :
    (StackHom.appFunctor C.projection T).map
          ((C.contractionZeroIso T).app (CategoricalPullback.fst p)).hom ≫
        (CategoricalPullback.iso ((StackHom.appFunctor (prodVertex C D) T).obj
          ((StackHom.appFunctor (prodProjection C D) T).obj p))).hom =
      (CategoricalPullback.iso ((prodContraction C D T 0).obj p)).hom ≫
        (StackHom.appFunctor D.projection T).map
          (((D.contractionZeroIso T).app (CategoricalPullback.snd p)).trans
            ((StackHom.appFunctor D.vertex T).mapIso (CategoricalPullback.iso p).symm)).hom
  /-- Contraction commutes with reindexing compatibly with the two projection comparisons, on
  the points of the fibre product. -/
  pullback {S T : Scheme.{u}} (h : S ⟶ T) (r : O.ring T)
      (p : StackFiber (prodTotal C D) T) :
    (StackHom.appFunctor C.projection S).map
          ((C.contractionPullbackIso h r).app (CategoricalPullback.fst p)).hom ≫
        (CategoricalPullback.iso ((stackPullback (prodTotal C D) h ⋙
          prodContraction C D S (O.pullback h r)).obj p)).hom =
      (CategoricalPullback.iso ((prodContraction C D T r ⋙
          stackPullback (prodTotal C D) h).obj p)).hom ≫
        (StackHom.appFunctor D.projection S).map
          ((D.contractionPullbackIso h r).app (CategoricalPullback.snd p)).hom

variable (hp : ProdCoherence C D)

include hp

/-- Contraction by one on the fibre product is the identity. -/
noncomputable def prodContractionOneIso (T : Scheme.{u}) :
    prodContraction C D T 1 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun p => CategoricalPullback.mkIso
      ((C.contractionOneIso T).app (CategoricalPullback.fst p))
      ((D.contractionOneIso T).app (CategoricalPullback.snd p)) (hp.one T p))
    (fun {p q} k => by
      apply CategoricalPullback.hom_ext
      · exact (C.contractionOneIso T).hom.naturality k.fst
      · exact (D.contractionOneIso T).hom.naturality k.snd)

/-- Contraction by a product on the fibre product is the composite of the two contractions. -/
noncomputable def prodContractionMulIso (T : Scheme.{u}) (r s : O.ring T) :
    prodContraction C D T (r * s) ≅ prodContraction C D T s ⋙ prodContraction C D T r :=
  NatIso.ofComponents
    (fun p => CategoricalPullback.mkIso
      ((C.contractionMulIso T r s).app (CategoricalPullback.fst p))
      ((D.contractionMulIso T r s).app (CategoricalPullback.snd p)) (hp.mul T r s p))
    (fun {p q} k => by
      apply CategoricalPullback.hom_ext
      · exact (C.contractionMulIso T r s).hom.naturality k.fst
      · exact (D.contractionMulIso T r s).hom.naturality k.snd)

/-- The vertex of the fibre product is fixed by every contraction. -/
noncomputable def prodContractionVertexIso (T : Scheme.{u}) (r : O.ring T) :
    StackHom.appFunctor (prodVertex C D) T ⋙ prodContraction C D T r ≅
      StackHom.appFunctor (prodVertex C D) T :=
  NatIso.ofComponents
    (fun b => CategoricalPullback.mkIso ((C.contractionVertexIso T r).app b)
      ((D.contractionVertexIso T r).app b) (hp.vertex T r b))
    (fun {b b'} k => by
      apply CategoricalPullback.hom_ext
      · exact (C.contractionVertexIso T r).hom.naturality k
      · exact (D.contractionVertexIso T r).hom.naturality k)

/-- Contraction by zero on the fibre product is the vertex section of its projection. -/
noncomputable def prodContractionZeroIso (T : Scheme.{u}) :
    prodContraction C D T 0 ≅
      StackHom.appFunctor (prodProjection C D) T ⋙ StackHom.appFunctor (prodVertex C D) T :=
  NatIso.ofComponents
    (fun p => CategoricalPullback.mkIso
      ((C.contractionZeroIso T).app (CategoricalPullback.fst p))
      (((D.contractionZeroIso T).app (CategoricalPullback.snd p)).trans
        ((StackHom.appFunctor D.vertex T).mapIso (CategoricalPullback.iso p).symm))
      (hp.zero T p))
    (fun {p q} k => by
      apply CategoricalPullback.hom_ext
      · exact (C.contractionZeroIso T).hom.naturality k.fst
      · change (D.contraction T 0).map k.snd ≫
            ((D.contractionZeroIso T).hom.app (CategoricalPullback.snd q) ≫
              (StackHom.appFunctor D.vertex T).map (CategoricalPullback.iso q).inv) =
          ((D.contractionZeroIso T).hom.app (CategoricalPullback.snd p) ≫
              (StackHom.appFunctor D.vertex T).map (CategoricalPullback.iso p).inv) ≫
            (StackHom.appFunctor D.vertex T).map
              ((StackHom.appFunctor C.projection T).map k.fst)
        rw [← Category.assoc, (D.contractionZeroIso T).hom.naturality k.snd, Category.assoc,
          Category.assoc, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (fun m => (D.contractionZeroIso T).hom.app (CategoricalPullback.snd p) ≫
          (StackHom.appFunctor D.vertex T).map m) k.w')

/-- Contraction on the fibre product commutes with reindexing of the test scheme. -/
noncomputable def prodContractionPullbackIso {S T : Scheme.{u}} (h : S ⟶ T) (r : O.ring T) :
    prodContraction C D T r ⋙ stackPullback (prodTotal C D) h ≅
      stackPullback (prodTotal C D) h ⋙ prodContraction C D S (O.pullback h r) :=
  NatIso.ofComponents
    (fun p => CategoricalPullback.mkIso
      ((C.contractionPullbackIso h r).app (CategoricalPullback.fst p))
      ((D.contractionPullbackIso h r).app (CategoricalPullback.snd p))
      (hp.pullback h r p))
    (fun {p q} k => by
      apply CategoricalPullback.hom_ext
      · exact (C.contractionPullbackIso h r).hom.naturality k.fst
      · exact (D.contractionPullbackIso h r).hom.naturality k.snd)

/-- The fibre product of two cone stacks over the same base, assuming the coherence laws of
`ProdCoherence`.  Its total stack is the genuine two-pullback of the two projections. -/
noncomputable def prod : ConeStack base O where
  total := prodTotal C D
  projection := prodProjection C D
  vertex := prodVertex C D
  vertexProjectionIso := prodVertexProjectionIso C D
  contraction := prodContraction C D
  contractionOneIso := prodContractionOneIso C D hp
  contractionMulIso := prodContractionMulIso C D hp
  contractionZeroIso := prodContractionZeroIso C D hp
  contractionVertexIso := prodContractionVertexIso C D hp
  contractionProjectionIso := prodContractionProjectionIso C D
  contractionPullbackIso := prodContractionPullbackIso C D hp

/-- The first projection of the fibre product, as a morphism of cone stacks.  Its comparison
with the base is an identity, its vertex comparison is the universal property's own cell, and it
is strictly equivariant for the contractions. -/
noncomputable def prodHomFst : Hom (prod C D hp) C where
  toStackHom := prodFst C D
  overBase := StackIso2.refl _
  mapVertex :=
    StackTwoPullback.canonicalLiftFstIso C.projection D.projection (prodVertexCone C D)
  equivariant _ _ := CategoryTheory.Iso.refl _

/-- The second projection of the fibre product, as a morphism of cone stacks.  Its comparison
with the base is the comparison 2-cell of the two-pullback. -/
noncomputable def prodHomSnd : Hom (prod C D hp) D where
  toStackHom := prodSnd C D
  overBase := (StackTwoPullback.canonical C.projection D.projection).comparison.symm
  mapVertex :=
    StackTwoPullback.canonicalLiftSndIso C.projection D.projection (prodVertexCone C D)
  equivariant _ _ := CategoryTheory.Iso.refl _

end Prod

end ConeStack

end GromovWitten.AlgebraicGeometry
