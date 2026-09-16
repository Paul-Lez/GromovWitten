/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.Picard
import GromovWitten.AlgebraicGeometry.Stacks.Algebraic
import GromovWitten.AlgebraicGeometry.Stacks.TwoPullback
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Cone stacks

Cone-stack data in this file use actual groupoid-valued fppf stacks.  Their vertex and
contraction action include unit, multiplication, and pullback comparison isomorphisms.  A closed
cone substack carries a representable closed immersion into its ambient cone, while abelian
addition and actions retain associativity and unit 2-cells fibrewise.  The higher pentagon,
triangle, symmetry, and reindexing coherence laws for these comparison cells are not yet encoded,
so the active structures are not yet the final coherent cone-stack interface required by the
roadmap.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

/-- A presheaf of scalar rings on schemes, with strict functoriality equations exposed. -/
structure FppfScalarRings where
  ring (T : Scheme.{u}) : Type u
  [commRing (T : Scheme.{u}) : CommRing (ring T)]
  pullback {S T : Scheme.{u}} (f : S ⟶ T) : ring T →+* ring S
  pullback_id (T : Scheme.{u}) : pullback (𝟙 T) = RingHom.id (ring T)
  pullback_comp {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    pullback (f ≫ g) = (pullback f).comp (pullback g)

attribute [instance] FppfScalarRings.commRing

/-- The canonical scalar rings on the big fppf site: regular functions on the underlying
scheme.  Cone-stack geometry uses this value; it is exposed as a definition only so its
pullback maps can be computed explicitly. -/
noncomputable def canonicalFppfScalarRings : FppfScalarRings.{u} where
  ring T := _root_.AlgebraicGeometry.Scheme.Γ.obj (Opposite.op T)
  pullback f := (_root_.AlgebraicGeometry.Scheme.Γ.map f.op).hom
  pullback_id T := by
    ext x
    rfl
  pullback_comp f g := by
    ext x
    rfl

/-- A graded cone stack over `base`.  The contraction laws are natural isomorphisms in every
groupoid fibre, and commute with change of test scheme. -/
structure ConeStack (base : FppfStack.{u}) (O : FppfScalarRings.{u}) where
  /-- Total stack of the cone. -/
  total : FppfStack.{u}
  /-- Projection to the base. -/
  projection : StackHom total base
  /-- Vertex section. -/
  vertex : StackHom base total
  /-- The vertex is genuinely a section of the projection, not merely an unrelated map from the
  base to the total stack. -/
  vertexProjectionIso : StackIso2
    (Pseudofunctor.StrongTrans.vcomp vertex projection)
    (Pseudofunctor.StrongTrans.id base.toPseudofunctor)
  /-- Scalar contraction in each fibre. -/
  contraction (T : Scheme.{u}) (r : O.ring T) : StackFiber total T ⥤ StackFiber total T
  /-- Contraction by one is the identity. -/
  contractionOneIso (T : Scheme.{u}) : contraction T 1 ≅ 𝟭 _
  /-- Multiplication of scalars agrees with composition of contractions. -/
  contractionMulIso (T : Scheme.{u}) (r s : O.ring T) :
    contraction T (r * s) ≅ contraction T s ⋙ contraction T r
  /-- Contraction by zero is the projection to the base followed by the vertex section. -/
  contractionZeroIso (T : Scheme.{u}) : contraction T 0 ≅
    StackHom.appFunctor projection T ⋙ StackHom.appFunctor vertex T
  /-- The vertex is fixed by every contraction. -/
  contractionVertexIso (T : Scheme.{u}) (r : O.ring T) :
    StackHom.appFunctor vertex T ⋙ contraction T r ≅
      StackHom.appFunctor vertex T
  /-- Contraction is over the base. -/
  contractionProjectionIso (T : Scheme.{u}) (r : O.ring T) :
    contraction T r ⋙ StackHom.appFunctor projection T ≅
      StackHom.appFunctor projection T
  /-- Contraction commutes with pullback of both points and scalars. -/
  contractionPullbackIso {S T : Scheme.{u}} (f : S ⟶ T) (r : O.ring T) :
    contraction T r ⋙ stackPullback total f ≅
      stackPullback total f ⋙ contraction S (O.pullback f r)

/-- Cone stacks over the canonical structure sheaf of regular functions. -/
abbrev CanonicalConeStack (base : FppfStack.{u}) :=
  ConeStack base canonicalFppfScalarRings

namespace ConeStack

variable {base : FppfStack.{u}} {O : FppfScalarRings.{u}}

/-- An object of a cone stack lying over a fixed object of the base fibre.  The comparison is
an isomorphism because the fibres are groupoids and stack geometry is 2-categorical. -/
structure FiberOver (C : ConeStack base O) (T : Scheme.{u}) (b : StackFiber base T) where
  object : StackFiber C.total T
  comparison : (StackHom.appFunctor C.projection T).obj object ≅ b

namespace FiberOver

variable {C : ConeStack base O} {T : Scheme.{u}} {b : StackFiber base T}

/-- A morphism over the fixed base object is a cone-stack arrow whose projection commutes with
the chosen comparisons. -/
structure Hom (x y : FiberOver C T b) where
  hom : x.object ⟶ y.object
  comm : (StackHom.appFunctor C.projection T).map hom ≫ y.comparison.hom =
    x.comparison.hom

@[ext]
theorem Hom.ext {x y : FiberOver C T b} (f g : Hom x y) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact h

/-- The fibre over a fixed base object is a category. -/
instance : Category (FiberOver C T b) where
  Hom := Hom
  id x := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by simp [f.comm, g.comm]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- Since the total stack fibre is a groupoid, so is the fibre over a fixed base object. -/
noncomputable instance : Groupoid (FiberOver C T b) where
  inv f :=
    { hom := inv f.hom
      comm := by
        apply (cancel_epi ((StackHom.appFunctor C.projection T).map f.hom)).1
        rw [← Category.assoc, ← Functor.map_comp]
        simp [f.comm] }
  inv_comp f := FiberOver.Hom.ext _ _ (by
    change inv f.hom ≫ f.hom = 𝟙 _
    simp)
  comp_inv f := FiberOver.Hom.ext _ _ (by
    change f.hom ≫ inv f.hom = 𝟙 _
    simp)

/-- Pullback of cone objects restricts to a functor between the groupoid fibres over a base
object and its pullback. -/
def pullback (C : ConeStack base O) {S T : Scheme.{u}} (f : S ⟶ T)
    (b : StackFiber base T) :
    FiberOver C T b ⥤
      FiberOver C S ((stackPullback base f).obj b) where
  obj x :=
    { object := (stackPullback C.total f).obj x.object
      comparison :=
        (Cat.Hom.toNatIso (C.projection.naturality ⟨f.op⟩)).app x.object ≪≫
          (stackPullback base f).mapIso x.comparison }
  map {x y} h :=
    { hom := (stackPullback C.total f).map h.hom
      comm := by
        have hn := (Cat.Hom.toNatIso
          (C.projection.naturality ⟨f.op⟩)).hom.naturality h.hom
        change
          ((stackPullback C.total f ⋙ StackHom.appFunctor C.projection S).map h.hom) ≫
              (Cat.Hom.toNatIso (C.projection.naturality ⟨f.op⟩)).hom.app _ ≫
                (stackPullback base f).map y.comparison.hom =
            (Cat.Hom.toNatIso (C.projection.naturality ⟨f.op⟩)).hom.app _ ≫
              (stackPullback base f).map x.comparison.hom
        rw [← Category.assoc]
        rw [show
          ((stackPullback C.total f ⋙ StackHom.appFunctor C.projection S).map h.hom) ≫
              (Cat.Hom.toNatIso (C.projection.naturality ⟨f.op⟩)).hom.app y.object =
            (Cat.Hom.toNatIso (C.projection.naturality ⟨f.op⟩)).hom.app x.object ≫
              (stackPullback base f).map
                ((StackHom.appFunctor C.projection T).map h.hom) by
            simpa only [StackHom.appFunctor, stackPullback, Functor.comp_map,
              Cat.Hom.comp_toFunctor] using hn]
        rw [Category.assoc, ← Functor.map_comp, h.comm] }
  map_id x := FiberOver.Hom.ext _ _ (by
    change (stackPullback C.total f).map (𝟙 x.object) = 𝟙 _
    simp)
  map_comp h k := FiberOver.Hom.ext _ _ (by
    change (stackPullback C.total f).map (h.hom ≫ k.hom) =
      (stackPullback C.total f).map h.hom ≫ (stackPullback C.total f).map k.hom
    simp)

/-- Reindex the displayed base comparison of a cone-fibre object along an isomorphism of base
objects.  The underlying total-space object and every vertical arrow are unchanged. -/
def changeBase (C : ConeStack base O) {T : Scheme.{u}}
    {b b' : StackFiber base T} (e : b ≅ b') :
    FiberOver C T b ⥤ FiberOver C T b' where
  obj x :=
    { object := x.object
      comparison := x.comparison.trans e }
  map {x y} h :=
    { hom := h.hom
      comm := by
        simp only [Iso.trans_hom]
        rw [← Category.assoc, h.comm] }
  map_id x := FiberOver.Hom.ext _ _ rfl
  map_comp h k := FiberOver.Hom.ext _ _ rfl

/-- Scalar contraction restricts to the groupoid fibre over every fixed base object. -/
def contraction (C : ConeStack base O) (T : Scheme.{u}) (b : StackFiber base T)
    (r : O.ring T) : FiberOver C T b ⥤ FiberOver C T b where
  obj x :=
    { object := (C.contraction T r).obj x.object
      comparison := (C.contractionProjectionIso T r).app x.object ≪≫ x.comparison }
  map f :=
    { hom := (C.contraction T r).map f.hom
      comm := by
        change
          ((C.contraction T r ⋙ StackHom.appFunctor C.projection T).map f.hom) ≫
              (C.contractionProjectionIso T r).hom.app _ ≫ _ =
            (C.contractionProjectionIso T r).hom.app _ ≫ _
        rw [← Category.assoc,
          (C.contractionProjectionIso T r).hom.naturality f.hom,
          Category.assoc, f.comm] }
  map_id x := FiberOver.Hom.ext _ _ (by
    change (C.contraction T r).map (𝟙 x.object) = 𝟙 _
    simp)
  map_comp f g := FiberOver.Hom.ext _ _ (by
    change (C.contraction T r).map (f.hom ≫ g.hom) =
      (C.contraction T r).map f.hom ≫ (C.contraction T r).map g.hom
    simp)

end FiberOver

/-- A morphism of cone stacks over the same base, with equivariance 2-cells. -/
structure Hom (C D : ConeStack base O) where
  toStackHom : StackHom C.total D.total
  overBase : StackIso2
    (Pseudofunctor.StrongTrans.vcomp toStackHom D.projection) C.projection
  mapVertex : StackIso2
    (Pseudofunctor.StrongTrans.vcomp C.vertex toStackHom) D.vertex
  equivariant (T : Scheme.{u}) (r : O.ring T) :
    C.contraction T r ⋙ StackHom.appFunctor toStackHom T ≅
      StackHom.appFunctor toStackHom T ⋙ D.contraction T r

namespace Hom

/-- The identity morphism of a cone stack, with its base and contraction comparisons supplied
by the categorical unitors. -/
noncomputable def id (C : ConeStack base O) : Hom C C where
  toStackHom := Pseudofunctor.StrongTrans.id C.total.toPseudofunctor
  overBase := StackIso2.leftUnitor C.projection
  mapVertex := StackIso2.rightUnitor C.vertex
  equivariant T r :=
    (Functor.rightUnitor (C.contraction T r)).trans
      (Functor.leftUnitor (C.contraction T r)).symm

end Hom

/-- Isomorphism data for cone-stack morphisms. -/
structure Iso (C D : ConeStack base O) where
  hom : Hom C D
  inv : Hom D C
  /-- The inverse laws are modifications of strong stack morphisms, hence are automatically
  compatible with pullback in the test scheme. -/
  homInv : StackIso2
    (Pseudofunctor.StrongTrans.vcomp hom.toStackHom inv.toStackHom)
    (Pseudofunctor.StrongTrans.id C.total.toPseudofunctor)
  invHom : StackIso2
    (Pseudofunctor.StrongTrans.vcomp inv.toStackHom hom.toStackHom)
    (Pseudofunctor.StrongTrans.id D.total.toPseudofunctor)

namespace Iso

/-- Every cone stack is isomorphic to itself through its constructed identity morphism. -/
noncomputable def refl (C : ConeStack base O) : Iso C C where
  hom := Hom.id C
  inv := Hom.id C
  homInv := StackIso2.leftUnitor
    (Pseudofunctor.StrongTrans.id C.total.toPseudofunctor)
  invHom := StackIso2.leftUnitor
    (Pseudofunctor.StrongTrans.id C.total.toPseudofunctor)

end Iso

/-- Forget an isomorphism of cone stacks to a bicategorical equivalence of total stacks. -/
def Iso.stackEquivalence {C D : ConeStack base O} (e : Iso C D) :
    StackEquivalenceData C.total D.total where
  hom := e.hom.toStackHom
  inv := e.inv.toStackHom
  homInv := e.homInv
  invHom := e.invHom

/-- Reverse an isomorphism of cone stacks. -/
def Iso.symm {C D : ConeStack base O} (e : Iso C D) : Iso D C where
  hom := e.inv
  inv := e.hom
  homInv := e.invHom
  invHom := e.homInv

end ConeStack

/-
Retired provisional cone-stack base change.  The former record supplied the pullback cone and
its comparison with a bicategorical pullback as fields, without constructing the cone structure
or proving compatibility of the comparison with its vertex and contractions.

/-- Base change of a cone stack along a stack morphism.  Its total stack is identified with the
genuine bicategorical pullback, and its displayed projection is the pullback projection. -/
structure ConeStackBaseChange
    {X Y : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (C : ConeStack Y O) (f : StackHom X Y) where
  pullback : ConeStack X O
  square : StackTwoPullback.Genuine C.projection f
  totalEquivalence : StackEquivalenceData pullback.total square.pullback
  projectionComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp totalEquivalence.hom square.snd)
    pullback.projection

-/

/-- A closed cone substack, with closedness imposed on every scheme base change through the
representable-morphism API. -/
structure ClosedConeSubstack {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (ambient : ConeStack base O) where
  cone : ConeStack base O
  inclusion : ConeStack.Hom cone ambient
  inclusion_closed : inclusion.toStackHom.ClosedImmersion

/-- An abelian cone stack has fibrewise addition and zero compatible with contraction. -/
structure AbelianConeStack (base : FppfStack.{u}) (O : FppfScalarRings.{u})
    extends ConeStack base O where
  add (T : Scheme.{u}) (b : StackFiber base T) :
    (toConeStack.FiberOver T b × toConeStack.FiberOver T b) ⥤
      toConeStack.FiberOver T b
  zero (T : Scheme.{u}) (b : StackFiber base T) : toConeStack.FiberOver T b
  neg (T : Scheme.{u}) (b : StackFiber base T) :
    toConeStack.FiberOver T b ⥤ toConeStack.FiberOver T b
  /-- Addition, zero, and negation commute with reindexing in the base stack. -/
  addPullbackIso {S T : Scheme.{u}} (f : S ⟶ T) (b : StackFiber base T) :
    add T b ⋙ ConeStack.FiberOver.pullback toConeStack f b ≅
      ((ConeStack.FiberOver.pullback toConeStack f b).prod
        (ConeStack.FiberOver.pullback toConeStack f b)) ⋙
          add S ((stackPullback base f).obj b)
  zeroPullbackIso {S T : Scheme.{u}} (f : S ⟶ T) (b : StackFiber base T) :
    (ConeStack.FiberOver.pullback toConeStack f b).obj (zero T b) ≅
      zero S ((stackPullback base f).obj b)
  negPullbackIso {S T : Scheme.{u}} (f : S ⟶ T) (b : StackFiber base T) :
    neg T b ⋙ ConeStack.FiberOver.pullback toConeStack f b ≅
      ConeStack.FiberOver.pullback toConeStack f b ⋙
        neg S ((stackPullback base f).obj b)
  addAssocIso (T : Scheme.{u}) (b : StackFiber base T)
      (x y z : toConeStack.FiberOver T b) :
    (add T b).obj ((add T b).obj (x, y), z) ≅
      (add T b).obj (x, (add T b).obj (y, z))
  addAssoc_naturality (T : Scheme.{u}) (b : StackFiber base T)
      {x x' y y' z z' : toConeStack.FiberOver T b}
      (fx : x ⟶ x') (fy : y ⟶ y') (fz : z ⟶ z') :
    (add T b).map ((add T b).map (fx, fy), fz) ≫
        (addAssocIso T b x' y' z').hom =
      (addAssocIso T b x y z).hom ≫
        (add T b).map (fx, (add T b).map (fy, fz))
  addCommIso (T : Scheme.{u}) (b : StackFiber base T)
      (x y : toConeStack.FiberOver T b) :
    (add T b).obj (x, y) ≅ (add T b).obj (y, x)
  addComm_naturality (T : Scheme.{u}) (b : StackFiber base T)
      {x x' y y' : toConeStack.FiberOver T b}
      (fx : x ⟶ x') (fy : y ⟶ y') :
    (add T b).map (fx, fy) ≫ (addCommIso T b x' y').hom =
      (addCommIso T b x y).hom ≫ (add T b).map (fy, fx)
  zeroAddIso (T : Scheme.{u}) (b : StackFiber base T)
      (x : toConeStack.FiberOver T b) :
    (add T b).obj (zero T b, x) ≅ x
  addZeroIso (T : Scheme.{u}) (b : StackFiber base T)
      (x : toConeStack.FiberOver T b) :
    (add T b).obj (x, zero T b) ≅ x
  addNegIso (T : Scheme.{u}) (b : StackFiber base T)
      (x : toConeStack.FiberOver T b) :
    (add T b).obj (x, (neg T b).obj x) ≅ zero T b
  contractionAddIso (T : Scheme.{u}) (b : StackFiber base T) (r : O.ring T)
      (x y : toConeStack.FiberOver T b) :
    (ConeStack.FiberOver.contraction toConeStack T b r).obj ((add T b).obj (x, y)) ≅
      (add T b).obj
        ((ConeStack.FiberOver.contraction toConeStack T b r).obj x,
          (ConeStack.FiberOver.contraction toConeStack T b r).obj y)

/-- The two-term complex of finite free modules represented by a matrix. -/
def freeTwoTermComplex {R : Type u} [CommRing R] {r₀ r₁ : ℕ}
    (d : Matrix (Fin r₁) (Fin r₀) R) : LinearTwoTermComplex R where
  degreeZero := Fin r₀ → R
  degreeOne := Fin r₁ → R
  differential := d.mulVecLin

/-- Extension of scalars sends the translation groupoid of a free two-term complex to the
translation groupoid of the entrywise base-changed matrix.  This functor acts on both objects
and translation arrows, so it retains stabilizers. -/
def freeTwoTermBaseChangeFunctor
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {r₀ r₁ : ℕ}
    (d : Matrix (Fin r₁) (Fin r₀) R) :
    (freeTwoTermComplex d).quotient ⥤
      (freeTwoTermComplex (d.map φ)).quotient where
  obj x := ⟨fun i ↦ φ (x.back i)⟩
  map {x y} a :=
    { val := fun j ↦ φ (a.val j)
      translate := by
        funext i
        have ha := congrArg φ (congrFun a.translate i)
        have hm :
            (d.map φ).mulVec (fun j ↦ φ (a.val j)) i =
              φ (d.mulVec a.val i) := by
          convert (RingHom.map_mulVec φ d a.val i).symm using 1
          apply congrArg (fun v ↦ (d.map φ).mulVec v i)
          funext j
          rfl
        change φ (x.back i + d.mulVec a.val i) = φ (y.back i) at ha
        change φ (x.back i) +
            (d.map φ).mulVec (fun j ↦ φ (a.val j)) i =
          φ (y.back i)
        rw [hm, ← map_add]
        exact ha }
  map_id x := by
    apply TwoTermQuotient.Hom.ext
    funext j
    exact map_zero φ
  map_comp a b := by
    apply TwoTermQuotient.Hom.ext
    funext j
    exact map_add φ _ _

@[simp]
theorem freeTwoTermBaseChangeFunctor_obj_back
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {r₀ r₁ : ℕ}
    (d : Matrix (Fin r₁) (Fin r₀) R)
    (x : (freeTwoTermComplex d).quotient) (i : Fin r₁) :
    ((freeTwoTermBaseChangeFunctor φ d).obj x).back i = φ (x.back i) :=
  rfl

@[simp]
theorem freeTwoTermBaseChangeFunctor_map_val
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {r₀ r₁ : ℕ}
    (d : Matrix (Fin r₁) (Fin r₀) R)
    {x y : (freeTwoTermComplex d).quotient} (a : x ⟶ y) (j : Fin r₀) :
    ((freeTwoTermBaseChangeFunctor φ d).map a).val j = φ (a.val j) :=
  rfl

/-- The local quotient base-change functor written with the scalar-ring presheaf's direct
pullback along a composite. -/
def freeTwoTermPullbackFunctor
    (O : FppfScalarRings.{u}) {R S T : Scheme.{u}}
    (g : R ⟶ S) (f : S ⟶ T) {r₀ r₁ : ℕ}
    (d : Matrix (Fin r₁) (Fin r₀) (O.ring T)) :
    (freeTwoTermComplex (d.map (O.pullback f))).quotient ⥤
      (freeTwoTermComplex (d.map (O.pullback (g ≫ f)))).quotient := by
  rw [O.pullback_comp]
  exact freeTwoTermBaseChangeFunctor (O.pullback g) (d.map (O.pullback f))

/-- A genuine local presentation of an abelian cone stack as `[E¹/E⁰]`.  The chart is an
actual smooth-surjective scheme chart.  The two bundles are the finite free modules of ranks
`rankDegreeZero` and `rankDegreeOne`, their differential is an actual matrix of regular
functions, and every scheme mapping to the chart identifies the corresponding cone fibre with
the translation quotient of the pulled-back matrix.  Thus neither the ranks nor the quotient
groupoids are unattached labels. -/
structure LocalTwoTermQuotientPresentation
    {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (E : AbelianConeStack base O) where
  chart : StackChart base
  chart_smoothSurjective : chart.IsSmoothSurjective
  rankDegreeZero : ℕ
  rankDegreeOne : ℕ
  differential :
    Matrix (Fin rankDegreeOne) (Fin rankDegreeZero) (O.ring chart.scheme)
  fiberEquivalence (T : Scheme.{u}) (f : T ⟶ chart.scheme) :
    E.toConeStack.FiberOver T (chart.obj T f) ≌
      (freeTwoTermComplex
        (differential.map (O.pullback f))).quotient
  /-- The local quotient description commutes with every change of test scheme.  The left route
  pulls a cone object back and changes its displayed base comparison using chart
  pseudonaturality; the right route extends both the object vector and every translation arrow
  along the scalar-ring pullback. -/
  fiberEquivalence_pullback {S T : Scheme.{u}} (g : S ⟶ T)
      (f : T ⟶ chart.scheme) :
    ConeStack.FiberOver.pullback E.toConeStack g (chart.obj T f) ⋙
          ConeStack.FiberOver.changeBase E.toConeStack
            (chart.objPullbackIso g f).symm ⋙
          (fiberEquivalence S (g ≫ f)).functor ≅
      (fiberEquivalence T f).functor ⋙
        freeTwoTermPullbackFunctor O g f differential
  /-- The fibre equivalence preserves addition on objects. -/
  fiberEquivalence_add_obj (T : Scheme.{u}) (f : T ⟶ chart.scheme)
      (x y : E.toConeStack.FiberOver T (chart.obj T f)) :
    ((fiberEquivalence T f).functor.obj ((E.add T (chart.obj T f)).obj (x, y))).back =
      ((fiberEquivalence T f).functor.obj x).back +
        ((fiberEquivalence T f).functor.obj y).back
  /-- The fibre equivalence preserves addition on translation arrows. -/
  fiberEquivalence_add_map (T : Scheme.{u}) (f : T ⟶ chart.scheme)
      {x x' y y' : E.toConeStack.FiberOver T (chart.obj T f)}
      (a : x ⟶ x') (b : y ⟶ y') :
    ((fiberEquivalence T f).functor.map
      ((E.add T (chart.obj T f)).map
        (show (x, y) ⟶ (x', y') from (a, b)))).val =
        ((fiberEquivalence T f).functor.map a).val +
          ((fiberEquivalence T f).functor.map b).val
  /-- The distinguished zero is sent to the zero vector. -/
  fiberEquivalence_zero_obj (T : Scheme.{u}) (f : T ⟶ chart.scheme) :
    ((fiberEquivalence T f).functor.obj (E.zero T (chart.obj T f))).back = 0
  /-- The fibre equivalence preserves negation on objects. -/
  fiberEquivalence_neg_obj (T : Scheme.{u}) (f : T ⟶ chart.scheme)
      (x : E.toConeStack.FiberOver T (chart.obj T f)) :
    ((fiberEquivalence T f).functor.obj
      ((E.neg T (chart.obj T f)).obj x)).back =
        -((fiberEquivalence T f).functor.obj x).back
  /-- The fibre equivalence preserves negation on arrows. -/
  fiberEquivalence_neg_map (T : Scheme.{u}) (f : T ⟶ chart.scheme)
      {x y : E.toConeStack.FiberOver T (chart.obj T f)} (a : x ⟶ y) :
    ((fiberEquivalence T f).functor.map
      ((E.neg T (chart.obj T f)).map a)).val =
        -((fiberEquivalence T f).functor.map a).val

/-- A vector-bundle stack is an abelian cone stack equipped with an actual local two-term
quotient presentation.  Its rank is derived below from that presentation and is therefore not
stored as an independently selectable integer. -/
structure VectorBundleStack (base : FppfStack.{u}) (O : FppfScalarRings.{u})
    extends AbelianConeStack base O where
  presentation : LocalTwoTermQuotientPresentation toAbelianConeStack

namespace VectorBundleStack

variable {base : FppfStack.{u}} {O : FppfScalarRings.{u}}

/-- The intrinsic displayed rank of a vector-bundle stack, computed from its actual local
two-term quotient presentation. -/
def stackRank (E : VectorBundleStack base O) : ℤ :=
  (E.presentation.rankDegreeOne : ℤ) - E.presentation.rankDegreeZero

@[simp]
theorem stackRank_eq (E : VectorBundleStack base O) :
    E.stackRank =
      (E.presentation.rankDegreeOne : ℤ) - E.presentation.rankDegreeZero :=
  rfl

end VectorBundleStack

/-- Abelian cone stacks over the canonical fppf structure sheaf. -/
abbrev CanonicalAbelianConeStack (base : FppfStack.{u}) :=
  AbelianConeStack base canonicalFppfScalarRings

/-- Vector-bundle stacks over the canonical fppf structure sheaf. -/
abbrev CanonicalVectorBundleStack (base : FppfStack.{u}) :=
  VectorBundleStack base canonicalFppfScalarRings

/-! ## The rank-zero vector-bundle stack -/

/-- The zero cone over a stack.  Its total stack, projection, and vertex are the base and its
identity morphism; scalar contraction is the identity on every fibre. -/
noncomputable def zeroConeStack (base : FppfStack.{u}) (O : FppfScalarRings.{u}) :
    ConeStack base O where
  total := base
  projection := Pseudofunctor.StrongTrans.id base.toPseudofunctor
  vertex := Pseudofunctor.StrongTrans.id base.toPseudofunctor
  vertexProjectionIso := StackIso2.leftUnitor
    (Pseudofunctor.StrongTrans.id base.toPseudofunctor)
  contraction T _ := Functor.id (StackFiber base T)
  contractionOneIso _ := Iso.refl _
  contractionMulIso := by
    intro T r s
    exact (Functor.leftUnitor (Functor.id (StackFiber base T))).symm
  contractionZeroIso := by
    intro T
    change Functor.id (StackFiber base T) ≅
      (Functor.id (StackFiber base T) ⋙ Functor.id (StackFiber base T))
    exact (Functor.leftUnitor _).symm
  contractionVertexIso := by
    intro T r
    change (Functor.id (StackFiber base T) ⋙ Functor.id (StackFiber base T)) ≅
      Functor.id (StackFiber base T)
    exact Functor.leftUnitor _
  contractionProjectionIso := by
    intro T r
    change (Functor.id (StackFiber base T) ⋙ Functor.id (StackFiber base T)) ≅
      Functor.id (StackFiber base T)
    exact Functor.leftUnitor _
  contractionPullbackIso := by
    intro S T f r
    exact (Functor.leftUnitor (stackPullback base f)).trans
      (Functor.rightUnitor (stackPullback base f)).symm

namespace ZeroConeStack

variable {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
  {T : Scheme.{u}} {b : StackFiber base T}

/-- The fibre groupoid of the zero cone over a fixed base object. -/
abbrev Fiber (T : Scheme.{u}) (b : StackFiber base T) :=
  (zeroConeStack base O).FiberOver T b

/-- The distinguished zero object in a zero-cone fibre. -/
def zero (T : Scheme.{u}) (b : StackFiber base T) : Fiber (O := O) T b where
  object := b
  comparison := Iso.refl b

/-- There is a canonical arrow between any two objects in a zero-cone fibre, obtained by
composing their displayed comparisons with the fixed base object. -/
noncomputable def hom (x y : Fiber (O := O) T b) : x ⟶ y where
  hom := x.comparison.hom ≫ y.comparison.inv
  comm := by
    change (x.comparison.hom ≫ y.comparison.inv) ≫ y.comparison.hom =
      x.comparison.hom
    simp

/-- Each hom-set of a zero-cone fibre is a singleton. -/
instance homSubsingleton (x y : Fiber (O := O) T b) : Subsingleton (x ⟶ y) where
  allEq f g := by
    apply ConeStack.FiberOver.Hom.ext
    apply (cancel_mono y.comparison.hom).1
    exact f.comm.trans g.comm.symm

/-- Any two objects in a zero-cone fibre are canonically isomorphic. -/
noncomputable def iso (x y : Fiber (O := O) T b) : x ≅ y where
  hom := hom x y
  inv := hom y x
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Addition on the contractible zero-cone fibre, implemented by the first projection. -/
noncomputable def add (T : Scheme.{u}) (b : StackFiber base T) :
    (Fiber (O := O) T b × Fiber (O := O) T b) ⥤ Fiber (O := O) T b :=
  CategoryTheory.Prod.fst _ _

/-- Negation on the zero-cone fibre. -/
noncomputable def neg (T : Scheme.{u}) (b : StackFiber base T) :
    Fiber (O := O) T b ⥤ Fiber (O := O) T b :=
  Functor.id _

end ZeroConeStack

/-- The zero cone with its canonical abelian group structure.  All coherence follows from the
fact, proved above, that every hom-set in a fibre is a singleton. -/
noncomputable def zeroAbelianConeStack (base : FppfStack.{u}) (O : FppfScalarRings.{u}) :
    AbelianConeStack base O where
  toConeStack := zeroConeStack base O
  add := ZeroConeStack.add
  zero := ZeroConeStack.zero
  neg := ZeroConeStack.neg
  addPullbackIso := by
    intro S T f b
    exact Iso.refl _
  zeroPullbackIso := by
    intro S T f b
    exact ZeroConeStack.iso _ _
  negPullbackIso := by
    intro S T f b
    exact (Functor.leftUnitor _).trans (Functor.rightUnitor _).symm
  addAssocIso := by
    intro T b x y z
    exact ZeroConeStack.iso _ _
  addAssoc_naturality := by
    intros
    exact Subsingleton.elim _ _
  addCommIso := by
    intro T b x y
    exact ZeroConeStack.iso _ _
  addComm_naturality := by
    intros
    exact Subsingleton.elim _ _
  zeroAddIso := by
    intro T b x
    exact ZeroConeStack.iso _ _
  addZeroIso := by
    intro T b x
    exact ZeroConeStack.iso _ _
  addNegIso := by
    intro T b x
    exact ZeroConeStack.iso _ _
  contractionAddIso := by
    intro T b r x y
    exact ZeroConeStack.iso _ _

namespace ZeroTwoTermQuotient

variable (R : Type u) [CommRing R]

/-- The translation quotient of the zero complex `0 → 0`. -/
abbrev Q :=
  (freeTwoTermComplex (0 : Matrix (Fin 0) (Fin 0) R)).quotient

/-- Its unique object. -/
def vertex : Q R := TwoTermQuotient.vertex _

/-- Its unique arrow between any two objects. -/
def hom (x y : Q R) : x ⟶ y where
  val := 0
  translate := by
    have hx : x.back = 0 := by
      funext i
      exact Fin.elim0 i
    have hy : y.back = 0 := by
      funext i
      exact Fin.elim0 i
    simp [hx, hy]

instance homSubsingleton (x y : Q R) : Subsingleton (x ⟶ y) where
  allEq f g := by
    apply TwoTermQuotient.Hom.ext
    funext i
    exact Fin.elim0 i

/-- Any two objects of the quotient of the zero complex are canonically isomorphic. -/
def iso (x y : Q R) : x ≅ y where
  hom := hom R x y
  inv := hom R y x
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

end ZeroTwoTermQuotient

namespace ZeroConeStack

variable {base : FppfStack.{u}} {O : FppfScalarRings.{u}}

private def toZeroQuotient (T : Scheme.{u}) (b : StackFiber base T) :
    Fiber (O := O) T b ⥤ ZeroTwoTermQuotient.Q (O.ring T) where
  obj _ := ZeroTwoTermQuotient.vertex _
  map _ := 𝟙 _
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private noncomputable def fromZeroQuotient (T : Scheme.{u}) (b : StackFiber base T) :
    ZeroTwoTermQuotient.Q (O.ring T) ⥤ Fiber (O := O) T b where
  obj _ := zero T b
  map _ := 𝟙 _
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- A zero-cone fibre is explicitly equivalent to the translation quotient of the pulled-back
zero two-term complex. -/
noncomputable def fiberEquivalence (T : Scheme.{u}) (b : StackFiber base T) :
    Fiber (O := O) T b ≌ ZeroTwoTermQuotient.Q (O.ring T) where
  functor := toZeroQuotient T b
  inverse := fromZeroQuotient T b
  unitIso := NatIso.ofComponents (fun x ↦ iso x _)
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun x ↦ ZeroTwoTermQuotient.iso _ _ x)
    (fun _ ↦ Subsingleton.elim _ _)

end ZeroConeStack

/-- The rank-zero vector-bundle stack on an algebraic stack.  Its smooth local presentation is
the actual zero matrix between free modules of ranks zero and zero. -/
noncomputable def zeroVectorBundleStack (X : AlgebraicStack.{u}) :
    CanonicalVectorBundleStack X.toStack where
  toAbelianConeStack := zeroAbelianConeStack X.toStack canonicalFppfScalarRings
  presentation :=
    { chart := Classical.choose X.smoothAtlas
      chart_smoothSurjective := Classical.choose_spec X.smoothAtlas
      rankDegreeZero := 0
      rankDegreeOne := 0
      differential := 0
      fiberEquivalence := fun T _f ↦ ZeroConeStack.fiberEquivalence T _
      fiberEquivalence_pullback := by
        intro S T g f
        exact NatIso.ofComponents
          (fun x ↦ ZeroTwoTermQuotient.iso (canonicalFppfScalarRings.ring S) _ _)
          (fun _ ↦ by
            apply TwoTermQuotient.Hom.ext
            funext i
            exact Fin.elim0 i)
      fiberEquivalence_add_obj := by
        intro T f x y
        funext i
        exact Fin.elim0 i
      fiberEquivalence_add_map := by
        intro T f x x' y y' a b
        funext i
        exact Fin.elim0 i
      fiberEquivalence_zero_obj := by
        intro T f
        funext i
        exact Fin.elim0 i
      fiberEquivalence_neg_obj := by
        intro T f x
        funext i
        exact Fin.elim0 i
      fiberEquivalence_neg_map := by
        intro T f x y a
        funext i
        exact Fin.elim0 i }

/-- A fibrewise action of an abelian cone stack `E` on a cone stack `C`, with unit and
associativity 2-cells. -/
structure ConeStackAction {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (E : AbelianConeStack base O) (C : ConeStack base O) where
  action (T : Scheme.{u}) (b : StackFiber base T) :
    (E.toConeStack.FiberOver T b × C.FiberOver T b) ⥤ C.FiberOver T b
  actionPullbackIso {S T : Scheme.{u}} (f : S ⟶ T) (b : StackFiber base T) :
    action T b ⋙ ConeStack.FiberOver.pullback C f b ≅
      ((ConeStack.FiberOver.pullback E.toConeStack f b).prod
        (ConeStack.FiberOver.pullback C f b)) ⋙
          action S ((stackPullback base f).obj b)
  unitIso (T : Scheme.{u}) (b : StackFiber base T) (x : C.FiberOver T b) :
    (action T b).obj (E.zero T b, x) ≅ x
  unit_naturality (T : Scheme.{u}) (b : StackFiber base T)
      {x y : C.FiberOver T b} (f : x ⟶ y) :
    (action T b).map (𝟙 (E.zero T b), f) ≫ (unitIso T b y).hom =
      (unitIso T b x).hom ≫ f
  assocIso (T : Scheme.{u}) (b : StackFiber base T)
      (e₁ e₂ : E.toConeStack.FiberOver T b) (x : C.FiberOver T b) :
    (action T b).obj ((E.add T b).obj (e₁, e₂), x) ≅
      (action T b).obj (e₁, (action T b).obj (e₂, x))
  assoc_naturality (T : Scheme.{u}) (b : StackFiber base T)
      {e₁ e₁' e₂ e₂' : E.toConeStack.FiberOver T b}
      {x x' : C.FiberOver T b} (f₁ : e₁ ⟶ e₁') (f₂ : e₂ ⟶ e₂')
      (g : x ⟶ x') :
    (action T b).map ((E.add T b).map (f₁, f₂), g) ≫
        (assocIso T b e₁' e₂' x').hom =
      (assocIso T b e₁ e₂ x).hom ≫
        (action T b).map (f₁, (action T b).map (f₂, g))
  contractionIso (T : Scheme.{u}) (b : StackFiber base T) (r : O.ring T)
      (e : E.toConeStack.FiberOver T b) (x : C.FiberOver T b) :
    (ConeStack.FiberOver.contraction C T b r).obj ((action T b).obj (e, x)) ≅
      (action T b).obj
        ((ConeStack.FiberOver.contraction E.toConeStack T b r).obj e,
          (ConeStack.FiberOver.contraction C T b r).obj x)

/-- A representative of an arrow in the action quotient: translate the source by an object of
the acting cone groupoid and then map to the target. -/
structure ConeActionArrow {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    {E : AbelianConeStack base O} {C : ConeStack base O}
    (A : ConeStackAction E C) {T : Scheme.{u}} {b : StackFiber base T}
    (x y : C.FiberOver T b) where
  translate : E.toConeStack.FiberOver T b
  hom : (A.action T b).obj (translate, x) ⟶ y

namespace ConeActionArrow

variable {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
  {E : AbelianConeStack base O} {C : ConeStack base O}
  {A : ConeStackAction E C} {T : Scheme.{u}} {b : StackFiber base T}
  {x y : C.FiberOver T b}

/-- The zero translation represents the identity orbit arrow. -/
def identity (A : ConeStackAction E C) (x : C.FiberOver T b) :
    ConeActionArrow A x x where
  translate := E.zero T b
  hom := A.unitIso T b x |>.hom

/-- Compose action-arrow representatives using addition in the acting abelian cone and the
associator of the action.  The second arrow acts after the first, hence its translating object
is the first summand. -/
def comp {z : C.FiberOver T b}
    (a : ConeActionArrow A x y) (a' : ConeActionArrow A y z) :
    ConeActionArrow A x z where
  translate := (E.add T b).obj (a'.translate, a.translate)
  hom := (A.assocIso T b a'.translate a.translate x).hom ≫
    (A.action T b).map (𝟙 a'.translate, a.hom) ≫ a'.hom

/-- Two action-arrow representatives agree when a morphism between their translating objects
intertwines the displayed arrows. -/
def Rel (a a' : ConeActionArrow A x y) : Prop :=
  ∃ e : a.translate ⟶ a'.translate,
    (A.action T b).map (e, 𝟙 x) ≫ a'.hom = a.hom

private theorem rel_refl (a : ConeActionArrow A x y) : Rel a a := by
  refine ⟨𝟙 _, ?_⟩
  have hpair :
      ((𝟙 a.translate, 𝟙 x) :
        ((a.translate, x) ⟶ (a.translate, x))) = 𝟙 (a.translate, x) := by
    ext <;> rfl
  rw [hpair]
  have hm := congrArg (fun k ↦ k ≫ a.hom)
    ((A.action T b).map_id (a.translate, x))
  simpa only [Category.id_comp] using hm

private theorem rel_symm {a a' : ConeActionArrow A x y} (h : Rel a a') : Rel a' a := by
  obtain ⟨e, he⟩ := h
  refine ⟨inv e, ?_⟩
  rw [← he]
  rw [← Category.assoc, ← Functor.map_comp]
  simp

private theorem rel_trans {a a' a'' : ConeActionArrow A x y}
    (h : Rel a a') (h' : Rel a' a'') : Rel a a'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨e ≫ e', ?_⟩
  change (A.action T b).map ((e ≫ e'), 𝟙 x) ≫ a''.hom = a.hom
  let h₁ : (a.translate, x) ⟶ (a'.translate, x) := (e, 𝟙 x)
  let h₂ : (a'.translate, x) ⟶ (a''.translate, x) := (e', 𝟙 x)
  have hpair :
      ((e ≫ e', 𝟙 x) : ((a.translate, x) ⟶ (a''.translate, x))) =
        h₁ ≫ h₂ := by
    apply Prod.ext <;> simp [h₁, h₂]
  rw [hpair, Functor.map_comp, Category.assoc, he', he]

/-- The setoid of action-arrow representatives. -/
def setoid (A : ConeStackAction E C) {T : Scheme.{u}} {b : StackFiber base T}
    (x y : C.FiberOver T b) : Setoid (ConeActionArrow A x y) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- Arrows in the orbit groupoid, before identifying that groupoid with a proposed quotient
stack fibre. -/
abbrev Orbit (A : ConeStackAction E C) {T : Scheme.{u}} {b : StackFiber base T}
    (x y : C.FiberOver T b) := Quotient (setoid A x y)

end ConeActionArrow

set_option backward.isDefEq.respectTransparency false in
/-- A stack morphism between total cone stacks, together with an invertible over-base cell,
induces a functor on every strict groupoid fibre over a chosen base object. -/
def coneFiberFunctorOfOverBase {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (C D : ConeStack base O) (q : StackHom C.total D.total)
    (overBase : StackIso2
      (Pseudofunctor.StrongTrans.vcomp q D.projection) C.projection)
    (T : Scheme.{u}) (b : StackFiber base T) :
    (C.FiberOver T b) ⥤ (D.FiberOver T b) where
  obj x :=
    { object := (StackHom.appFunctor q T).obj x.object
      comparison := (overBase.appIso T).app x.object ≪≫ x.comparison }
  map {x y} h :=
    { hom := (StackHom.appFunctor q T).map h.hom
      comm := by
        change
          (StackHom.appFunctor
              (Pseudofunctor.StrongTrans.vcomp q D.projection) T).map h.hom ≫
              (overBase.appIso T).hom.app y.object ≫ y.comparison.hom =
            (overBase.appIso T).hom.app x.object ≫ x.comparison.hom
        rw [← Category.assoc,
          (overBase.appIso T).hom.naturality h.hom,
          Category.assoc, h.comm] }
  map_id x := ConeStack.FiberOver.Hom.ext _ _ (by
    change (StackHom.appFunctor q T).map (𝟙 x.object) = 𝟙 _
    simp)
  map_comp h k := ConeStack.FiberOver.Hom.ext _ _ (by
    change (StackHom.appFunctor q T).map (h.hom ≫ k.hom) =
      (StackHom.appFunctor q T).map h.hom ≫
        (StackHom.appFunctor q T).map k.hom
    simp)

/-
Retired provisional quotient and abelian-hull interfaces.  `ConeQuotientPresentation` supplied
the desired quotient cone plus essential surjectivity and orbit-hom bijectivity as fields, and
`AbelianHull` supplied an arbitrary closed equivariant embedding without a hull universal
property.  The action groupoid constructions above remain available; these claimed geometric
outputs will return only after they are constructed.

/-- A quotient presentation `[C/E]` of a cone stack.  Essential surjectivity alone would allow
an arbitrary collapse or enlargement of stabilizers, so the structure also identifies every
target hom-set bijectively with the genuine groupoid orbit of action-arrow representatives. -/
structure ConeQuotientPresentation {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (E : AbelianConeStack base O) (C : ConeStack base O) where
  action : ConeStackAction E C
  quotient : ConeStack base O
  /-- The quotient map is a single morphism of fppf stacks.  In particular, its fibre functors
  commute coherently with every change of test scheme rather than being independently chosen. -/
  quotientMap : StackHom C.total quotient.total
  /-- The quotient map lies over the base by a global 2-isomorphism. -/
  quotientProjectionIso : StackIso2
    (Pseudofunctor.StrongTrans.vcomp quotientMap quotient.projection) C.projection
  /-- Translating an object does not change its image in the quotient fibre. -/
  actionComparison (T : Scheme.{u}) (b : StackFiber base T)
      (e : E.toConeStack.FiberOver T b) (x : C.FiberOver T b) :
    (coneFiberFunctorOfOverBase C quotient quotientMap quotientProjectionIso T b).obj
        ((action.action T b).obj (e, x)) ≅
      (coneFiberFunctorOfOverBase C quotient quotientMap quotientProjectionIso T b).obj x
  /-- The translation comparison is natural in the translating groupoid object. -/
  actionComparison_naturality (T : Scheme.{u}) (b : StackFiber base T)
      {e e' : E.toConeStack.FiberOver T b} (h : e ⟶ e')
      (x : C.FiberOver T b) :
    (coneFiberFunctorOfOverBase C quotient quotientMap quotientProjectionIso T b).map
          ((action.action T b).map (h, 𝟙 x)) ≫
        (actionComparison T b e' x).hom =
      (actionComparison T b e x).hom
  /-- The zero-translation comparison is forced by the action unit isomorphism. -/
  actionComparison_zero (T : Scheme.{u}) (b : StackFiber base T)
      (x : C.FiberOver T b) :
    (actionComparison T b (E.zero T b) x).hom =
      (coneFiberFunctorOfOverBase C quotient quotientMap quotientProjectionIso T b).map
        (action.unitIso T b x).hom
  /-- Translation comparisons commute with change of test scheme.  Both sides are arrows from
  the pullback of the translated source to the pullback of the un-translated quotient object;
  the displayed stack-morphism and action pseudonaturality isomorphisms are part of the
  equation, so fibrewise comparison choices cannot vary independently. -/
  actionComparison_pullback {S T : Scheme.{u}} (f : S ⟶ T)
      (b : StackFiber base T) (e : E.toConeStack.FiberOver T b)
      (x : C.FiberOver T b) :
    (StackHom.appFunctor quotientMap S).map
          ((action.actionPullbackIso f b).hom.app (e, x)).hom ≫
        (actionComparison S ((stackPullback base f).obj b)
          ((ConeStack.FiberOver.pullback E.toConeStack f b).obj e)
          ((ConeStack.FiberOver.pullback C f b).obj x)).hom.hom ≫
        (Cat.Hom.toNatIso (quotientMap.naturality ⟨f.op⟩)).hom.app x.object =
      (Cat.Hom.toNatIso (quotientMap.naturality ⟨f.op⟩)).hom.app
          ((action.action T b).obj (e, x)).object ≫
        (stackPullback quotient.total f).map (actionComparison T b e x).hom.hom
  /-- The comparison cocycle carries the explicit addition-and-action composition of orbit
  representatives to composition in the quotient fibre. -/
  actionComparison_comp (T : Scheme.{u}) (b : StackFiber base T)
      {x y z : C.FiberOver T b}
      (a : ConeActionArrow action x y) (a' : ConeActionArrow action y z) :
    (actionComparison T b a.translate x).inv ≫
          (coneFiberFunctorOfOverBase C quotient quotientMap quotientProjectionIso T b).map
            a.hom ≫
        (actionComparison T b a'.translate y).inv ≫
          (coneFiberFunctorOfOverBase C quotient quotientMap quotientProjectionIso T b).map
            a'.hom =
      (actionComparison T b (ConeActionArrow.comp a a').translate x).inv ≫
        (coneFiberFunctorOfOverBase C quotient quotientMap quotientProjectionIso T b).map
          (ConeActionArrow.comp a a').hom
  locallyEssentiallySurjective (T : Scheme.{u}) (b : StackFiber base T) :
    (coneFiberFunctorOfOverBase C quotient quotientMap quotientProjectionIso T b).EssSurj
  /-- Every quotient arrow is represented by a translation arrow, uniquely modulo morphisms
  of translating objects. -/
  orbitHom_bijective (T : Scheme.{u}) (b : StackFiber base T)
      (x y : C.FiberOver T b) : Function.Bijective
    (@Quotient.lift _ _ (ConeActionArrow.setoid action x y)
      (fun a : ConeActionArrow action x y ↦
        (actionComparison T b a.translate x).inv ≫
          (coneFiberFunctorOfOverBase C quotient quotientMap quotientProjectionIso T b).map
            a.hom)
      (by
        intro a a' h
        change ConeActionArrow.Rel a a' at h
        obtain ⟨e, he⟩ := h
        apply (cancel_epi (actionComparison T b a.translate x).hom).1
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
        rw [← actionComparison_naturality T b e x]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rw [← Functor.map_comp]
        exact congrArg
          (fun h ↦
            (coneFiberFunctorOfOverBase C quotient quotientMap
              quotientProjectionIso T b).map h)
          he.symm))

namespace ConeQuotientPresentation

variable {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
  {E : AbelianConeStack base O} {C : ConeStack base O}

/-- An ordinary arrow is the orbit representative with zero translation. -/
def ordinaryRepresentative (Q : ConeQuotientPresentation E C)
    {T : Scheme.{u}} {b : StackFiber base T} {x y : C.FiberOver T b}
    (h : x ⟶ y) : ConeActionArrow Q.action x y where
  translate := E.zero T b
  hom := (Q.action.unitIso T b x).hom ≫ h

/-- The canonical map from action-orbit arrows to arrows in the proposed quotient fibre. -/
def orbitArrowMap (Q : ConeQuotientPresentation E C)
    (T : Scheme.{u}) (b : StackFiber base T) (x y : C.FiberOver T b) :
    ConeActionArrow.Orbit Q.action x y →
      ((coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
          Q.quotientProjectionIso T b).obj x ⟶
        (coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
          Q.quotientProjectionIso T b).obj y) :=
  @Quotient.lift _ _ (ConeActionArrow.setoid Q.action x y)
    (fun a : ConeActionArrow Q.action x y ↦
      (Q.actionComparison T b a.translate x).inv ≫
        (coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
          Q.quotientProjectionIso T b).map a.hom)
    (by
      intro a a' h
      change ConeActionArrow.Rel a a' at h
      obtain ⟨e, he⟩ := h
      apply (cancel_epi (Q.actionComparison T b a.translate x).hom).1
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← Q.actionComparison_naturality T b e x]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Functor.map_comp]
      exact congrArg
        (fun h ↦
          (coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
            Q.quotientProjectionIso T b).map h)
        he.symm)

/-- The quotient-presentation axiom yields an equivalence of each orbit hom-set with the
corresponding hom-set in the quotient stack fibre. -/
noncomputable def orbitHomEquiv (Q : ConeQuotientPresentation E C)
    (T : Scheme.{u}) (b : StackFiber base T) (x y : C.FiberOver T b) :
    ConeActionArrow.Orbit Q.action x y ≃
      ((coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
          Q.quotientProjectionIso T b).obj x ⟶
        (coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
          Q.quotientProjectionIso T b).obj y) :=
  Equiv.ofBijective (Q.orbitArrowMap T b x y) (by
    simpa only [orbitArrowMap] using Q.orbitHom_bijective T b x y)

/-- The explicit addition-and-action composite of representatives maps to categorical
composition in the quotient fibre. -/
theorem orbitArrowMap_compRepresentative (Q : ConeQuotientPresentation E C)
    {T : Scheme.{u}} {b : StackFiber base T}
    {x y z : C.FiberOver T b}
    (a : ConeActionArrow Q.action x y) (a' : ConeActionArrow Q.action y z) :
    Q.orbitArrowMap T b x z
        (Quotient.mk (ConeActionArrow.setoid Q.action x z)
          (ConeActionArrow.comp a a')) =
      Q.orbitArrowMap T b x y
          (Quotient.mk (ConeActionArrow.setoid Q.action x y) a) ≫
        Q.orbitArrowMap T b y z
          (Quotient.mk (ConeActionArrow.setoid Q.action y z) a') := by
  simpa only [orbitArrowMap, Quotient.lift_mk, Category.assoc] using
    (Q.actionComparison_comp T b a a').symm

/-- The orbit groupoid of the action over a fixed base object.  It is wrapped so its homs can
carry the quotient composition without conflicting with the pre-existing category structure
on the source cone fibre. -/
structure OrbitFiber (Q : ConeQuotientPresentation E C)
    (T : Scheme.{u}) (b : StackFiber base T) where
  object : C.FiberOver T b

noncomputable def orbitIdentity (Q : ConeQuotientPresentation E C)
    (T : Scheme.{u}) (b : StackFiber base T) (x : C.FiberOver T b) :
    ConeActionArrow.Orbit Q.action x x :=
  (Q.orbitHomEquiv T b x x).symm (𝟙 _)

noncomputable def orbitComposition (Q : ConeQuotientPresentation E C)
    (T : Scheme.{u}) (b : StackFiber base T)
    {x y z : C.FiberOver T b}
    (h : ConeActionArrow.Orbit Q.action x y)
    (k : ConeActionArrow.Orbit Q.action y z) :
    ConeActionArrow.Orbit Q.action x z :=
  (Q.orbitHomEquiv T b x z).symm
    (Q.orbitHomEquiv T b x y h ≫ Q.orbitHomEquiv T b y z k)

/-- The transported identity is represented by zero translation. -/
theorem orbitIdentity_eq_mk_identity (Q : ConeQuotientPresentation E C)
    {T : Scheme.{u}} {b : StackFiber base T} (x : C.FiberOver T b) :
    Q.orbitIdentity T b x =
      Quotient.mk (ConeActionArrow.setoid Q.action x x)
        (ConeActionArrow.identity Q.action x) := by
  apply (Q.orbitHomEquiv T b x x).injective
  unfold orbitIdentity
  rw [Equiv.apply_symm_apply]
  change 𝟙 _ =
    (Q.actionComparison T b (E.zero T b) x).inv ≫
      (coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
        Q.quotientProjectionIso T b).map (Q.action.unitIso T b x).hom
  rw [← Q.actionComparison_zero T b x]
  simp

/-- Transported orbit composition is represented by the explicit sum of translations and
the action associator. -/
theorem orbitComposition_mk (Q : ConeQuotientPresentation E C)
    {T : Scheme.{u}} {b : StackFiber base T}
    {x y z : C.FiberOver T b}
    (a : ConeActionArrow Q.action x y) (a' : ConeActionArrow Q.action y z) :
    Q.orbitComposition T b
        (Quotient.mk (ConeActionArrow.setoid Q.action x y) a)
        (Quotient.mk (ConeActionArrow.setoid Q.action y z) a') =
      Quotient.mk (ConeActionArrow.setoid Q.action x z)
        (ConeActionArrow.comp a a') := by
  apply (Q.orbitHomEquiv T b x z).injective
  unfold orbitComposition
  rw [Equiv.apply_symm_apply]
  change Q.orbitArrowMap T b x y
          (Quotient.mk (ConeActionArrow.setoid Q.action x y) a) ≫
        Q.orbitArrowMap T b y z
          (Quotient.mk (ConeActionArrow.setoid Q.action y z) a') =
      Q.orbitArrowMap T b x z
        (Quotient.mk (ConeActionArrow.setoid Q.action x z)
          (ConeActionArrow.comp a a'))
  exact (Q.orbitArrowMap_compRepresentative a a').symm

noncomputable instance orbitFiberCategory (Q : ConeQuotientPresentation E C)
    (T : Scheme.{u}) (b : StackFiber base T) : Category (OrbitFiber Q T b) where
  Hom x y := ConeActionArrow.Orbit Q.action x.object y.object
  id x := Q.orbitIdentity T b x.object
  comp h k := Q.orbitComposition T b h k
  id_comp f := by
    apply (Q.orbitHomEquiv T b _ _).injective
    simp [orbitIdentity, orbitComposition]
  comp_id f := by
    apply (Q.orbitHomEquiv T b _ _).injective
    simp [orbitIdentity, orbitComposition]
  assoc f g h := by
    apply (Q.orbitHomEquiv T b _ _).injective
    simp [orbitComposition, Category.assoc]

/-- The canonical functor from the constructed orbit groupoid to the vertical fibre of the
quotient cone stack. -/
noncomputable def orbitFiberFunctor (Q : ConeQuotientPresentation E C)
    (T : Scheme.{u}) (b : StackFiber base T) :
    OrbitFiber Q T b ⥤ Q.quotient.FiberOver T b where
  obj x := (coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
    Q.quotientProjectionIso T b).obj x.object
  map {x y} h := Q.orbitArrowMap T b x.object y.object h
  map_id x := (Q.orbitHomEquiv T b x.object x.object).apply_symm_apply (𝟙 _)
  map_comp h k :=
    (Q.orbitHomEquiv T b _ _).apply_symm_apply
      (Q.orbitHomEquiv T b _ _ h ≫ Q.orbitHomEquiv T b _ _ k)

/-- The orbit functor is fully faithful, with inverse on every hom-set supplied by the proved
orbit-hom equivalence. -/
noncomputable def orbitFiberFunctorFullyFaithful (Q : ConeQuotientPresentation E C)
    (T : Scheme.{u}) (b : StackFiber base T) :
    (Q.orbitFiberFunctor T b).FullyFaithful where
  preimage {x y} h := (Q.orbitHomEquiv T b x.object y.object).symm h
  map_preimage {x y} h := (Q.orbitHomEquiv T b x.object y.object).apply_symm_apply h
  preimage_map {x y} h := (Q.orbitHomEquiv T b x.object y.object).symm_apply_apply h

noncomputable instance orbitFiberGroupoid (Q : ConeQuotientPresentation E C)
    (T : Scheme.{u}) (b : StackFiber base T) : Groupoid (OrbitFiber Q T b) :=
  Groupoid.ofFullyFaithfulToGroupoid (Q.orbitFiberFunctor T b)
    (Q.orbitFiberFunctorFullyFaithful T b)

/-- The vertical quotient fibre is equivalent to the genuine orbit groupoid.  This is the
categorical quotient universal property: it includes objects, stabilizers, composition, and
inverses, not merely a bijection of raw total-stack hom-sets. -/
noncomputable def orbitFiberEquivalence (Q : ConeQuotientPresentation E C)
    (T : Scheme.{u}) (b : StackFiber base T) :
    OrbitFiber Q T b ≌ Q.quotient.FiberOver T b := by
  let F := Q.orbitFiberFunctor T b
  letI : F.Faithful :=
    { map_injective := fun e ↦
        (Q.orbitHomEquiv T b _ _).injective e }
  letI : F.Full :=
    { map_surjective := fun h ↦
        ⟨(Q.orbitHomEquiv T b _ _).symm h,
          (Q.orbitHomEquiv T b _ _).apply_symm_apply h⟩ }
  letI : F.EssSurj := by
    refine { mem_essImage := fun y ↦ ?_ }
    obtain ⟨x, ⟨e⟩⟩ :=
      (Q.locallyEssentiallySurjective T b).mem_essImage y
    exact ⟨⟨x⟩, ⟨e⟩⟩
  letI : F.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact F.asEquivalence

/-- On a zero-translation representative, the orbit map is exactly the original quotient
functor on arrows. -/
@[simp]
theorem orbitArrowMap_ordinary (Q : ConeQuotientPresentation E C)
    {T : Scheme.{u}} {b : StackFiber base T} {x y : C.FiberOver T b}
    (h : x ⟶ y) :
    Q.orbitArrowMap T b x y
        (Quotient.mk (ConeActionArrow.setoid Q.action x y)
      (Q.ordinaryRepresentative h)) =
      (coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
        Q.quotientProjectionIso T b).map h := by
  change (Q.actionComparison T b (E.zero T b) x).inv ≫
      (coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
        Q.quotientProjectionIso T b).map
        ((Q.action.unitIso T b x).hom ≫ h) =
    (coneFiberFunctorOfOverBase C Q.quotient Q.quotientMap
      Q.quotientProjectionIso T b).map h
  rw [Functor.map_comp, ← Q.actionComparison_zero T b x]
  simp

end ConeQuotientPresentation

/-- An abelian hull is a closed equivariant embedding into an abelian cone stack. -/
structure AbelianHull {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (C : ConeStack base O) where
  hull : AbelianConeStack base O
  inclusion : StackHom C.total hull.total
  closed : inclusion.ClosedImmersion
  equivariant (T : Scheme.{u}) (r : O.ring T) :
    C.contraction T r ⋙ StackHom.appFunctor inclusion T ≅
      StackHom.appFunctor inclusion T ⋙ hull.contraction T r

-/

end GromovWitten.AlgebraicGeometry
