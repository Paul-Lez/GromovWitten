/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Spaces.Properties
import GromovWitten.AlgebraicGeometry.Stacks.Discrete
import GromovWitten.AlgebraicGeometry.Stacks.GroupoidValued
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.Topology.KrullDimension

/-!
# Algebraic and Deligne--Mumford stacks

This file packages the geometric conditions on a groupoid-valued fppf stack.  Charts are actual
strong morphisms from represented scheme stacks, so their action on arrows and their pullback
coherences are retained.  Representability of a chart is stated
by an honest scheme satisfying a pullback universal property over every test object of the
stack.  The same scheme-valued universal property represents the diagonal through its sheaf of
isomorphisms.

The definitions are deliberately presentation-free.  An algebraic stack contains the existence
of a smooth surjective chart, while a Deligne--Mumford stack contains an etale surjective chart;
neither exposes a preferred chart through the public morphism type.

## Universes

`FppfStack.{u}` has fibres in `Cat.{u + 1, u + 1}`, one universe above the site `Scheme.{u}`, so
that stacks whose fibres are groupoids of `Type u`-valued sheaf data — notably the quotient stacks
`[U/G]` and `BG` of `Stacks/TorsorStackBundle.lean`, whose fibres are the groupoids
`ActionTorsor G U T : Type (u + 1)` — are literally `FppfStack.{u}`-valued.  Represented stacks
reach that universe through `uliftSheafFunctor` below, a fully faithful functor lifting a
`Type u`-valued fppf sheaf to a `Type (u + 1)`-valued one, so the fibre of `representedStack X`
over `T` is `Discrete (ULift (T ⟶ X))` rather than `Discrete (T ⟶ X)`.
-/

open CategoryTheory
open CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open scoped Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u v

abbrev Scheme := _root_.AlgebraicGeometry.Scheme

/-- Groupoid-valued stacks on the big fppf site of schemes.  Fibres live in `Cat.{u + 1, u + 1}`
so that quotient stacks `[U/G]` (whose fibres are groupoids of torsors, one universe above the
base) are literally `FppfStack.{u}`-valued; see `GromovWitten.AlgebraicGeometry.LargeFppfStack`,
which is now a plain alias for this same type. -/
abbrev FppfStack :=
  StackInGroupoids.{u, u + 1, u + 1, u + 1} Scheme.{u}
    (_root_.AlgebraicGeometry.Scheme.fppfTopology : GrothendieckTopology Scheme.{u})

/-- The groupoid of objects of a stack over a scheme. -/
abbrev StackFiber (X : FppfStack.{u}) (T : Scheme.{u}) :=
  X.toPseudofunctor.obj ⟨Opposite.op T⟩

/-- Pullback of objects and arrows in a stack along a scheme morphism. -/
abbrev stackPullback (X : FppfStack.{u}) {S T : Scheme.{u}} (f : S ⟶ T) :
    StackFiber X T ⥤ StackFiber X S :=
  (X.toPseudofunctor.map ⟨f.op⟩).toFunctor

/-- Pseudofunctorial comparison between iterated pullback and pullback along a composite. -/
noncomputable def stackPullbackCompIso (X : FppfStack.{u})
    {R S T : Scheme.{u}} (g : R ⟶ S) (f : S ⟶ T)
    (x : StackFiber X T) :
    (stackPullback X g).obj ((stackPullback X f).obj x) ≅
      (stackPullback X (g ≫ f)).obj x :=
  (Cat.Hom.toNatIso
    (X.toPseudofunctor.mapComp ⟨f.op⟩ ⟨g.op⟩)).symm.app x

/-- Pull an isomorphism of stack objects back along a scheme morphism, with the
pseudofunctorial comparison to the composite built in. -/
noncomputable def stackPullbackIso (X : FppfStack.{u})
    {R S T : Scheme.{u}} (g : R ⟶ S) (f : S ⟶ T)
    {x y : StackFiber X T}
    (e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y) :
    (stackPullback X (g ≫ f)).obj x ≅
      (stackPullback X (g ≫ f)).obj y :=
  ((stackPullbackCompIso X g f x).symm.trans
    ((stackPullback X g).mapIso e)).trans
      (stackPullbackCompIso X g f y)

/-- Equality of scheme maps canonically identifies the corresponding pullbacks of an object. -/
noncomputable def stackPullbackObjIsoOfEq (X : FppfStack.{u})
    {R T : Scheme.{u}} {f g : R ⟶ T} (h : f = g)
    (x : StackFiber X T) :
    (stackPullback X f).obj x ≅ (stackPullback X g).obj x := by
  subst g
  exact Iso.refl _

/-- A morphism of fppf stacks is a strong transformation, so its comparison with pullback is an
invertible 2-cell rather than a definitional equality. -/
abbrev StackHom (X Y : FppfStack.{u}) :=
  Pseudofunctor.StrongTrans X.toPseudofunctor Y.toPseudofunctor

/-- Invertible 2-morphisms between stack morphisms, expressed directly as mutually inverse
modifications. -/
structure StackIso2 {X Y : FppfStack.{u}} (f g : StackHom X Y) where
  hom : Pseudofunctor.StrongTrans.Modification f g
  inv : Pseudofunctor.StrongTrans.Modification g f
  hom_inv_id : Pseudofunctor.StrongTrans.Modification.vcomp hom inv =
    Pseudofunctor.StrongTrans.Modification.id f
  inv_hom_id : Pseudofunctor.StrongTrans.Modification.vcomp inv hom =
    Pseudofunctor.StrongTrans.Modification.id g

namespace StackIso2

variable {X Y : FppfStack.{u}} {f g h : StackHom X Y}

/-- Identity invertible 2-cell. -/
def refl (f : StackHom X Y) : StackIso2 f f :=
  { hom := Pseudofunctor.StrongTrans.Modification.id f
    inv := Pseudofunctor.StrongTrans.Modification.id f
    hom_inv_id := by
      apply Pseudofunctor.StrongTrans.Modification.ext
      funext a
      simp [Pseudofunctor.StrongTrans.Modification.vcomp,
        Pseudofunctor.StrongTrans.Modification.id]
    inv_hom_id := by
      apply Pseudofunctor.StrongTrans.Modification.ext
      funext a
      simp [Pseudofunctor.StrongTrans.Modification.vcomp,
        Pseudofunctor.StrongTrans.Modification.id] }

/-- Reverse an invertible 2-cell. -/
def symm (e : StackIso2 f g) : StackIso2 g f :=
  { hom := e.inv
    inv := e.hom
    hom_inv_id := e.inv_hom_id
    inv_hom_id := e.hom_inv_id }

/-- Compose invertible 2-cells. -/
def trans (e : StackIso2 f g) (e' : StackIso2 g h) : StackIso2 f h :=
  { hom := Pseudofunctor.StrongTrans.Modification.vcomp e.hom e'.hom
    inv := Pseudofunctor.StrongTrans.Modification.vcomp e'.inv e.inv
    hom_inv_id := by
      apply Pseudofunctor.StrongTrans.Modification.ext
      funext a
      have he' := congrArg
        (fun m ↦ Pseudofunctor.StrongTrans.Modification.app m a) e'.hom_inv_id
      have he := congrArg
        (fun m ↦ Pseudofunctor.StrongTrans.Modification.app m a) e.hom_inv_id
      simp only [Pseudofunctor.StrongTrans.Modification.vcomp,
        Pseudofunctor.StrongTrans.Modification.id] at he' he ⊢
      simp only [Category.assoc]
      rw [← Category.assoc (e'.hom.app a) (e'.inv.app a) (e.inv.app a),
        he', Category.id_comp, he]
    inv_hom_id := by
      apply Pseudofunctor.StrongTrans.Modification.ext
      funext a
      have he := congrArg
        (fun m ↦ Pseudofunctor.StrongTrans.Modification.app m a) e.inv_hom_id
      have he' := congrArg
        (fun m ↦ Pseudofunctor.StrongTrans.Modification.app m a) e'.inv_hom_id
      simp only [Pseudofunctor.StrongTrans.Modification.vcomp,
        Pseudofunctor.StrongTrans.Modification.id] at he he' ⊢
      simp only [Category.assoc]
      rw [← Category.assoc (e.inv.app a) (e.hom.app a) (e'.hom.app a),
        he, Category.id_comp, he'] }

set_option backward.isDefEq.respectTransparency false in
/-- Whisker an invertible stack 2-cell on the right by a stack morphism. -/
noncomputable def whiskerRight {Z : FppfStack.{u}} (e : StackIso2 f g)
    (q : StackHom Y Z) : StackIso2
      (Pseudofunctor.StrongTrans.vcomp f q)
      (Pseudofunctor.StrongTrans.vcomp g q) where
  hom := (Pseudofunctor.StrongTrans.whiskerRight
    (Pseudofunctor.StrongTrans.Hom.of e.hom) q).as
  inv := (Pseudofunctor.StrongTrans.whiskerRight
    (Pseudofunctor.StrongTrans.Hom.of e.inv) q).as
  hom_inv_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    have he := congrArg
      (fun m ↦ Pseudofunctor.StrongTrans.Modification.app m a) e.hom_inv_id
    simp only [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id] at he ⊢
    rw [← comp_whiskerRight, he, id_whiskerRight]
    rfl
  inv_hom_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    have he := congrArg
      (fun m ↦ Pseudofunctor.StrongTrans.Modification.app m a) e.inv_hom_id
    simp only [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id] at he ⊢
    rw [← comp_whiskerRight, he, id_whiskerRight]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Whisker an invertible stack 2-cell on the left by a stack morphism. -/
noncomputable def whiskerLeft {W : FppfStack.{u}} (q : StackHom W X)
    (e : StackIso2 f g) : StackIso2
      (Pseudofunctor.StrongTrans.vcomp q f)
      (Pseudofunctor.StrongTrans.vcomp q g) where
  hom := (Pseudofunctor.StrongTrans.whiskerLeft q
    (Pseudofunctor.StrongTrans.Hom.of e.hom)).as
  inv := (Pseudofunctor.StrongTrans.whiskerLeft q
    (Pseudofunctor.StrongTrans.Hom.of e.inv)).as
  hom_inv_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    have he := congrArg
      (fun m ↦ Pseudofunctor.StrongTrans.Modification.app m a) e.hom_inv_id
    have hei := congrArg
      (fun m ↦ Pseudofunctor.StrongTrans.Modification.app m a) e.inv_hom_id
    simp only [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id] at he hei ⊢
    let ea : f.app a ≅ g.app a :=
      { hom := e.hom.app a
        inv := e.inv.app a
        hom_inv_id := he
        inv_hom_id := hei }
    change q.app a ◁ ea.hom ≫ q.app a ◁ ea.inv =
      𝟙 (q.app a ≫ f.app a)
    exact whiskerLeft_hom_inv (q.app a) ea
  inv_hom_id := by
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext a
    have he := congrArg
      (fun m ↦ Pseudofunctor.StrongTrans.Modification.app m a) e.hom_inv_id
    have hei := congrArg
      (fun m ↦ Pseudofunctor.StrongTrans.Modification.app m a) e.inv_hom_id
    simp only [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id] at he hei ⊢
    let ea : f.app a ≅ g.app a :=
      { hom := e.hom.app a
        inv := e.inv.app a
        hom_inv_id := he
        inv_hom_id := hei }
    change q.app a ◁ ea.inv ≫ q.app a ◁ ea.hom =
      𝟙 (q.app a ≫ g.app a)
    exact whiskerLeft_inv_hom (q.app a) ea
/-- Left unitor as an invertible stack 2-cell. -/
noncomputable def leftUnitor (f : StackHom X Y) : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor) f) f := by
  let e := Pseudofunctor.StrongTrans.leftUnitor f
  exact
    { hom := e.hom.as
      inv := e.inv.as
      hom_inv_id := congrArg Pseudofunctor.StrongTrans.Hom.as e.hom_inv_id
      inv_hom_id := congrArg Pseudofunctor.StrongTrans.Hom.as e.inv_hom_id }

/-- Right unitor as an invertible stack 2-cell. -/
noncomputable def rightUnitor (f : StackHom X Y) : StackIso2
    (Pseudofunctor.StrongTrans.vcomp f
      (Pseudofunctor.StrongTrans.id Y.toPseudofunctor)) f := by
  let e := Pseudofunctor.StrongTrans.rightUnitor f
  exact
    { hom := e.hom.as
      inv := e.inv.as
      hom_inv_id := congrArg Pseudofunctor.StrongTrans.Hom.as e.hom_inv_id
      inv_hom_id := congrArg Pseudofunctor.StrongTrans.Hom.as e.inv_hom_id }

/-- Associativity of vertical composition, exposed as an invertible stack 2-cell. -/
noncomputable def associator
    {A B C D : FppfStack.{u}}
    (f : StackHom A B) (g : StackHom B C) (h : StackHom C D) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp f g) h)
      (Pseudofunctor.StrongTrans.vcomp f
        (Pseudofunctor.StrongTrans.vcomp g h)) := by
  let e := Pseudofunctor.StrongTrans.associator f g h
  exact
    { hom := e.hom.as
      inv := e.inv.as
      hom_inv_id := congrArg Pseudofunctor.StrongTrans.Hom.as e.hom_inv_id
      inv_hom_id := congrArg Pseudofunctor.StrongTrans.Hom.as e.inv_hom_id }

end StackIso2

/-- Equivalence data between two stacks, expressed with strong transformations and invertible
modifications. -/
structure StackEquivalenceData (X Y : FppfStack.{u}) where
  hom : StackHom X Y
  inv : StackHom Y X
  homInv : StackIso2 (Pseudofunctor.StrongTrans.vcomp hom inv)
    (Pseudofunctor.StrongTrans.id X.toPseudofunctor)
  invHom : StackIso2 (Pseudofunctor.StrongTrans.vcomp inv hom)
    (Pseudofunctor.StrongTrans.id Y.toPseudofunctor)

namespace StackEquivalenceData

/-- Every stack is equivalent to itself through the identity strong transformation. -/
noncomputable def refl (X : FppfStack.{u}) : StackEquivalenceData X X where
  hom := Pseudofunctor.StrongTrans.id X.toPseudofunctor
  inv := Pseudofunctor.StrongTrans.id X.toPseudofunctor
  homInv := StackIso2.leftUnitor
    (Pseudofunctor.StrongTrans.id X.toPseudofunctor)
  invHom := StackIso2.leftUnitor
    (Pseudofunctor.StrongTrans.id X.toPseudofunctor)

end StackEquivalenceData

/-- The value of a stack morphism on a test scheme. -/
abbrev StackHom.appFunctor {X Y : FppfStack.{u}} (f : StackHom X Y) (T : Scheme.{u}) :
    StackFiber X T ⥤ StackFiber Y T :=
  (f.app (LocallyDiscrete.mk (Opposite.op T))).toFunctor

namespace StackIso2

variable {X Y : FppfStack.{u}} {f g : StackHom X Y}

/-- An invertible 2-cell of stack morphisms induces a natural isomorphism on every scheme
fibre.  This exposes the componentwise equivalence needed to transport geometric
presentations across 2-isomorphic morphisms. -/
def appIso (e : StackIso2 f g) (T : Scheme.{u}) :
    StackHom.appFunctor f T ≅ StackHom.appFunctor g T where
  hom := (e.hom.app (LocallyDiscrete.mk (Opposite.op T))).toNatTrans
  inv := (e.inv.app (LocallyDiscrete.mk (Opposite.op T))).toNatTrans
  hom_inv_id := by
    ext x
    have h := congrArg
      (fun m ↦ ((m.app (LocallyDiscrete.mk (Opposite.op T))).toNatTrans).app x)
      e.hom_inv_id
    simpa [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id] using h
  inv_hom_id := by
    ext x
    have h := congrArg
      (fun m ↦ ((m.app (LocallyDiscrete.mk (Opposite.op T))).toNatTrans).app x)
      e.inv_hom_id
    simpa [Pseudofunctor.StrongTrans.Modification.vcomp,
      Pseudofunctor.StrongTrans.Modification.id] using h

end StackIso2

/-- Universe-lift a `Type u`-valued fppf sheaf to a `Type (u + 1)`-valued sheaf of the same
presheaf, up to `ULift`.  This is the device that lets `FppfSheaf.{u}`-valued data (represented
sheaves, torsor sheaves, ...) be promoted to `FppfStack.{u}`-valued stacks, whose fibres live in
`Cat.{u + 1, u + 1}`.

Deliberately built by hand from a bare anonymous-constructor sheaf and `whiskerRight`/
`Functor.FullyFaithful.whiskeringRight` at the *presheaf* level, instead of through Mathlib's
`sheafCompose`/`fullyFaithfulSheafCompose` (which factor through `ObjectProperty.lift` and
`sheafToPresheaf`): the extra layers of that generic construction made later kernel checks in
`Stacks/Scheme.lean` time out once fibres moved to `Cat.{u + 1, u + 1}`.  Downstream files should
only use `.obj`, `.map` and `uliftSheafFunctor.fullyFaithful`, never the body. -/
noncomputable def uliftSheafFunctor :
    FppfSheaf.{u} ⥤
      Sheaf (_root_.AlgebraicGeometry.Scheme.fppfTopology : GrothendieckTopology Scheme.{u})
        (Type (u + 1)) where
  obj P := ⟨P.obj ⋙ CategoryTheory.uliftFunctor.{u + 1},
    (isSheaf_iff_isSheaf_of_type _ _).2 <|
      Presieve.isSheaf_comp_uliftFunctor _ ((isSheaf_iff_isSheaf_of_type _ _).1 P.property)⟩
  map η := ObjectProperty.homMk
    (CategoryTheory.Functor.whiskerRight η.hom CategoryTheory.uliftFunctor.{u + 1})
  map_id _ := by apply ObjectProperty.hom_ext; simp
  map_comp _ _ := by apply ObjectProperty.hom_ext; simp

/-- `uliftSheafFunctor` is fully faithful, because `uliftFunctor` is. -/
noncomputable def uliftSheafFunctor.fullyFaithful : uliftSheafFunctor.{u}.FullyFaithful where
  preimage {P Q} f := ObjectProperty.homMk
    (((CategoryTheory.fullyFaithfulULiftFunctor.{u + 1, u}).whiskeringRight
      Scheme.{u}ᵒᵖ).preimage f.hom)
  map_preimage {P Q} f := by
    apply ObjectProperty.hom_ext
    exact ((CategoryTheory.fullyFaithfulULiftFunctor.{u + 1, u}).whiskeringRight
      Scheme.{u}ᵒᵖ).map_preimage f.hom
  preimage_map {P Q} f := by
    apply ObjectProperty.hom_ext
    exact ((CategoryTheory.fullyFaithfulULiftFunctor.{u + 1, u}).whiskeringRight
      Scheme.{u}ᵒᵖ).preimage_map f.hom

instance : uliftSheafFunctor.{u}.Faithful := uliftSheafFunctor.fullyFaithful.faithful

/-- The `Type (u + 1)`-valued sheaf underlying `representedStack`: the fppf-sheaf Yoneda
embedding of `X`, universe-lifted from `Type u` to `Type (u + 1)`. -/
noncomputable def representedSheaf (X : Scheme.{u}) :
    Sheaf (_root_.AlgebraicGeometry.Scheme.fppfTopology : GrothendieckTopology Scheme.{u})
      (Type (u + 1)) :=
  uliftSheafFunctor.obj (fppfYoneda.obj X)

/-- The represented fppf sheaf of a scheme as a discrete groupoid-valued stack.  Its fibre over
`T` is `Discrete (ULift (T ⟶ X))`: every object is `⟨⟨g⟩⟩` for a scheme morphism `g`, and
`x.as.down` recovers `g` from an object `x`. -/
noncomputable def representedStack (X : Scheme.{u}) : FppfStack.{u} :=
  StackInGroupoids.ofSheafOfTypes
    (_root_.AlgebraicGeometry.Scheme.fppfTopology : GrothendieckTopology Scheme.{u})
    (representedSheaf X)

/-- Reindexing an object of a represented stack is ordinary composition of scheme maps. -/
@[simp]
theorem representedStack_map_obj {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    ((representedStack T).toPseudofunctor.map ⟨f.op⟩).toFunctor.obj
      (Discrete.mk (ULift.up g)) = Discrete.mk (ULift.up (f ≫ g)) :=
  rfl

/-- A scheme chart is an actual strong morphism from the represented scheme stack. -/
structure StackChart (X : FppfStack.{u}) where
  /-- The scheme furnishing the chart. -/
  scheme : Scheme.{u}
  /-- The chart morphism, including its invertible pseudonaturality comparisons and laws. -/
  map : StackHom (representedStack scheme) X

namespace StackChart

variable {X : FppfStack.{u}} (A : StackChart X)

/-- A test-scheme map into the chart scheme gives an object of the target stack fibre. -/
noncomputable def obj (T : Scheme.{u}) (g : T ⟶ A.scheme) : StackFiber X T :=
  (A.map.appFunctor T).obj (Discrete.mk (ULift.up g))

/-- Equality of maps into the chart scheme induces the corresponding isomorphism between
their chart objects. -/
noncomputable def objIsoOfEq {S : Scheme.{u}} {f g : S ⟶ A.scheme} (h : f = g) :
    A.obj S f ≅ A.obj S g := by
  subst g
  exact Iso.refl _

/-- The object isomorphism attached to equality is the chart functor applied to the unique
arrow of the represented discrete fibre. -/
@[simp]
theorem objIsoOfEq_hom {S : Scheme.{u}} {f g : S ⟶ A.scheme} (h : f = g) :
    (A.objIsoOfEq h).hom =
      (A.map.appFunctor S).map (Discrete.eqToHom (congrArg ULift.up h)) := by
  subst g
  exact ((A.map.appFunctor S).map_id (Discrete.mk (ULift.up f))).symm

/-- Pseudonaturality of a chart identifies the object obtained from a composite scheme map with
the pullback of the corresponding chart object. -/
noncomputable def objPullbackIso {S T : Scheme.{u}} (g : S ⟶ T)
    (f : T ⟶ A.scheme) :
    A.obj S (g ≫ f) ≅ (stackPullback X g).obj (A.obj T f) :=
  (Cat.Hom.toNatIso (A.map.naturality ⟨g.op⟩)).app (Discrete.mk (ULift.up f))

/-- Pull the universal chart comparison back along a candidate scheme map, retaining the
strong-transformation naturality and stack pseudofunctor coherence. -/
noncomputable def inducedComparison
    {T U : Scheme.{u}} (fst : U ⟶ T) (snd : U ⟶ A.scheme)
    {x : StackFiber X T}
    (universal : A.obj U snd ≅ (stackPullback X fst).obj x)
    {S : Scheme.{u}} (m : S ⟶ U) :
    A.obj S (m ≫ snd) ≅ (stackPullback X (m ≫ fst)).obj x :=
  (((Cat.Hom.toNatIso (A.map.naturality ⟨m.op⟩)).app (Discrete.mk (ULift.up snd))).trans
    ((stackPullback X m).mapIso universal)).trans
      (stackPullbackCompIso X m fst x)

/-- A map to a chart pullback presentation classifies both scheme legs and the supplied
2-cell.  The comparison equation prevents the universal property from forgetting stabilizer
or descent data. -/
def Classifies {T U : Scheme.{u}} (fst : U ⟶ T) (snd : U ⟶ A.scheme)
    {x : StackFiber X T}
    (universal : A.obj U snd ≅ (stackPullback X fst).obj x)
    {S : Scheme.{u}} (toBase : S ⟶ T) (toChart : S ⟶ A.scheme)
    (comparison : A.obj S toChart ≅ (stackPullback X toBase).obj x)
    (m : S ⟶ U) : Prop :=
  ∃ fst_eq : m ≫ fst = toBase, ∃ snd_eq : m ≫ snd = toChart,
    (A.objIsoOfEq snd_eq).symm.trans
      ((A.inducedComparison fst snd universal m).trans
        (stackPullbackObjIsoOfEq X fst_eq x)) = comparison

/-- A scheme with the complete two-cartesian comparison data for the base change of a chart by
an object `x : X(T)`.  The universal property retains the isomorphism between the two objects
over the pullback scheme. -/
structure PullbackPresentation (T : Scheme.{u}) (x : StackFiber X T) where
  /-- The representing scheme. -/
  space : Scheme.{u}
  /-- Projection to the test scheme. -/
  fst : space ⟶ T
  /-- Projection to the atlas scheme. -/
  snd : space ⟶ A.scheme
  /-- The specified 2-cell in the stack fibre. -/
  comparison : A.obj space snd ≅ (stackPullback X fst).obj x
  /-- A map to both legs, together with the required 2-cell, factors through the representing
  scheme. -/
  lift {S : Scheme.{u}} (toBase : S ⟶ T) (toChart : S ⟶ A.scheme)
      (comparison : A.obj S toChart ≅ (stackPullback X toBase).obj x) : S ⟶ space
  lift_fst {S : Scheme.{u}} (toBase : S ⟶ T) (toChart : S ⟶ A.scheme)
      (comparison : A.obj S toChart ≅ (stackPullback X toBase).obj x) :
    lift toBase toChart comparison ≫ fst = toBase
  lift_snd {S : Scheme.{u}} (toBase : S ⟶ T) (toChart : S ⟶ A.scheme)
      (comparison : A.obj S toChart ≅ (stackPullback X toBase).obj x) :
    lift toBase toChart comparison ≫ snd = toChart
  lift_compatible {S : Scheme.{u}} (toBase : S ⟶ T) (toChart : S ⟶ A.scheme)
      (c : A.obj S toChart ≅ (stackPullback X toBase).obj x) :
    A.Classifies fst snd comparison toBase toChart c
      (lift toBase toChart c)
  lift_unique {S : Scheme.{u}} (toBase : S ⟶ T) (toChart : S ⟶ A.scheme)
      (c : A.obj S toChart ≅ (stackPullback X toBase).obj x)
      (m : S ⟶ space)
      (compatible : A.Classifies fst snd comparison toBase toChart c m) :
    m = lift toBase toChart c

/-- The chart object classified by `f : S ⟶ U` is canonically the pullback along `f` of
the identity object of the chart scheme. -/
noncomputable def identityObjectPullbackComparison
    {S : Scheme.{u}} (f : S ⟶ A.scheme) :
    A.obj S f ≅
      (stackPullback X f).obj (A.obj A.scheme (𝟙 A.scheme)) :=
  (A.objIsoOfEq (by simp)).trans (A.objPullbackIso f (𝟙 A.scheme))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical identity-object comparison is stable under further pullback. -/
theorem inducedComparison_identityObjectPullbackComparison
    {U S : Scheme.{u}} (f : U ⟶ A.scheme) (m : S ⟶ U) :
    A.inducedComparison f f (A.identityObjectPullbackComparison f) m =
      A.identityObjectPullbackComparison (m ≫ f) := by
  apply Iso.ext
  let hf : f = f ≫ 𝟙 A.scheme := by simp
  let hmf : m ≫ f = (m ≫ f) ≫ 𝟙 A.scheme := by simp
  let huf : ULift.up f = ULift.up (f ≫ 𝟙 A.scheme) := congrArg ULift.up hf
  let humf : ULift.up (m ≫ f) = ULift.up ((m ≫ f) ≫ 𝟙 A.scheme) := congrArg ULift.up hmf
  let d : (Discrete.mk (ULift.up f) : StackFiber (representedStack A.scheme) U) ≅
      Discrete.mk (ULift.up (f ≫ 𝟙 A.scheme)) := Discrete.eqToIso huf
  let sourceComp := Cat.Hom.toNatIso
    ((representedStack A.scheme).toPseudofunctor.mapComp ⟨f.op⟩ ⟨m.op⟩)
  have hdisc :
      (Discrete.eqToIso humf).hom ≫
          sourceComp.hom.app (Discrete.mk (ULift.up (𝟙 A.scheme))) =
        ((stackPullback (representedStack A.scheme) m).mapIso d).hom := by
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  have hsource := congrArg
    (fun k ↦ (A.map.appFunctor S).map k) hdisc
  have hnat :=
    (Cat.Hom.toNatIso (A.map.naturality ⟨m.op⟩)).hom.naturality d.hom
  have hnat' :
      (A.map.appFunctor S).map
            (((stackPullback (representedStack A.scheme) m).mapIso d).hom) ≫
          (A.objPullbackIso m (f ≫ 𝟙 A.scheme)).hom =
        (A.objPullbackIso m f).hom ≫
          (stackPullback X m).map ((A.map.appFunctor U).map d.hom) := by
    exact hnat
  dsimp only [d] at hnat'
  have hnat'' :
      ((Cat.Hom.toNatIso (A.map.naturality ⟨m.op⟩)).app
            (Discrete.mk (ULift.up f))).hom ≫
          (stackPullback X m).map
            ((A.map.appFunctor U).map (Discrete.eqToIso huf).hom) =
        (A.map.appFunctor S).map
            (((stackPullback (representedStack A.scheme) m).mapIso
              (Discrete.eqToIso huf)).hom) ≫
          ((Cat.Hom.toNatIso (A.map.naturality ⟨m.op⟩)).app
            (Discrete.mk (ULift.up (f ≫ 𝟙 A.scheme)))).hom := by
    exact hnat'.symm
  have h := Pseudofunctor.StrongTrans.naturality_comp_hom_app
    A.map ⟨f.op⟩ ⟨m.op⟩ (Discrete.mk (ULift.up (𝟙 A.scheme)))
  dsimp [representedStack, StackInGroupoids.ofSheafOfTypes,
    Pseudofunctor.ofPresheafOfTypes, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete, typeToCat] at h
  let fop : LocallyDiscrete.mk (Opposite.op A.scheme) ⟶
      LocallyDiscrete.mk (Opposite.op U) := ⟨f.op⟩
  let mop : LocallyDiscrete.mk (Opposite.op U) ⟶
      LocallyDiscrete.mk (Opposite.op S) := ⟨m.op⟩
  let mfop : LocallyDiscrete.mk (Opposite.op A.scheme) ⟶
      LocallyDiscrete.mk (Opposite.op S) := ⟨(m ≫ f).op⟩
  have hop : fop ≫ mop = mfop := by
    rfl
  change (A.map.naturality (fop ≫ mop)).hom.toNatTrans.app
      (Discrete.mk (ULift.up (𝟙 A.scheme))) = _ at h
  cases hop
  simp only [Functor.map_comp] at hsource
  simp only [identityObjectPullbackComparison, inducedComparison, Iso.trans_hom,
    Functor.mapIso, Functor.map_comp, Category.assoc]
  erw [A.objIsoOfEq_hom]
  have hd_hom : Discrete.eqToHom huf = (Discrete.eqToIso huf).hom := by
    apply Subsingleton.elim
  rw [hd_hom]
  rw [← Category.assoc]
  rw [hnat'']
  simp only [Category.assoc]
  rw [← hsource]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, eqToIso_refl, Iso.refl_hom,
    Discrete.functor_map_id, Category.comp_id, Iso.app_hom,
    Cat.Hom.toNatIso_hom, objIsoOfEq_hom, eqToHom_refl]
  convert h.symm using 1
  · rfl
  · rw [CategoryTheory.Functor.map_id]
    rfl
  · exact Category.id_comp _

/-- Reverse the comparison cell of a self-pullback of a chart.  This is the groupoid symmetry
that exchanges the two atlas legs, with pseudonaturality comparisons inserted explicitly. -/
noncomputable def PullbackPresentation.selfSwapComparison
    (p : A.PullbackPresentation A.scheme
      (A.obj A.scheme (𝟙 A.scheme))) :
    A.obj p.space p.fst ≅
      (stackPullback X p.snd).obj (A.obj A.scheme (𝟙 A.scheme)) :=
  (A.identityObjectPullbackComparison p.fst).trans
    (p.comparison.symm.trans (A.identityObjectPullbackComparison p.snd))

/-- Reverse a test comparison for the self-pullback of a chart. -/
noncomputable def selfSwapTestComparison
    {S : Scheme.{u}} {toBase toChart : S ⟶ A.scheme}
    (c : A.obj S toChart ≅
      (stackPullback X toBase).obj (A.obj A.scheme (𝟙 A.scheme))) :
    A.obj S toBase ≅
      (stackPullback X toChart).obj (A.obj A.scheme (𝟙 A.scheme)) :=
  (A.identityObjectPullbackComparison toBase).trans
    (c.symm.trans (A.identityObjectPullbackComparison toChart))

/-- Reversing a self-pullback comparison twice recovers the original comparison. -/
@[simp]
theorem selfSwapTestComparison_selfSwap
    {S : Scheme.{u}} {toBase toChart : S ⟶ A.scheme}
    (c : A.obj S toChart ≅
      (stackPullback X toBase).obj (A.obj A.scheme (𝟙 A.scheme))) :
    A.selfSwapTestComparison (A.selfSwapTestComparison c) = c := by
  simp [selfSwapTestComparison]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back a reversed self-overlap comparison is the reversal of the pulled-back
comparison.  This is the coherence needed to exchange the two projections in the represented
groupoid relation. -/
theorem inducedComparison_selfSwap
    (p : A.PullbackPresentation A.scheme
      (A.obj A.scheme (𝟙 A.scheme)))
    {S : Scheme.{u}} (m : S ⟶ p.space) :
    A.inducedComparison p.snd p.fst p.selfSwapComparison m =
      A.selfSwapTestComparison
        (A.inducedComparison p.fst p.snd p.comparison m) := by
  unfold PullbackPresentation.selfSwapComparison selfSwapTestComparison
  rw [← A.inducedComparison_identityObjectPullbackComparison p.fst m,
    ← A.inducedComparison_identityObjectPullbackComparison p.snd m]
  apply Iso.ext
  dsimp only [inducedComparison, Iso.trans, Iso.symm,
    CategoryTheory.Functor.mapIso]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]

/-- Classifying a point of the reversed self-pullback is equivalent to classifying the same
scheme map in the original self-pullback with the two legs and the comparison exchanged. -/
theorem classifies_selfSwap_iff
    (p : A.PullbackPresentation A.scheme
      (A.obj A.scheme (𝟙 A.scheme)))
    {S : Scheme.{u}} (toBase toChart : S ⟶ A.scheme)
    (c : A.obj S toChart ≅
      (stackPullback X toBase).obj (A.obj A.scheme (𝟙 A.scheme)))
    (m : S ⟶ p.space) :
    A.Classifies p.snd p.fst p.selfSwapComparison toBase toChart c m ↔
      A.Classifies p.fst p.snd p.comparison toChart toBase
        (A.selfSwapTestComparison c) m := by
  constructor
  · rintro ⟨fst_eq, snd_eq, h⟩
    refine ⟨snd_eq, fst_eq, ?_⟩
    subst toBase
    subst toChart
    simp only [objIsoOfEq, stackPullbackObjIsoOfEq, Iso.refl_symm,
      Iso.refl_trans, Iso.trans_refl] at h ⊢
    rw [A.inducedComparison_selfSwap p m] at h
    have h' := congrArg A.selfSwapTestComparison h
    simpa using h'
  · rintro ⟨fst_eq, snd_eq, h⟩
    refine ⟨snd_eq, fst_eq, ?_⟩
    subst toBase
    subst toChart
    simp only [objIsoOfEq, stackPullbackObjIsoOfEq, Iso.refl_symm,
      Iso.refl_trans, Iso.trans_refl] at h ⊢
    rw [A.inducedComparison_selfSwap p m]
    simpa using congrArg A.selfSwapTestComparison h

/-- The self-pullback presentation with its two atlas projections exchanged.  Its universal
property is derived from the original one by reversing the comparison 2-cell. -/
noncomputable def PullbackPresentation.selfSwap
    (p : A.PullbackPresentation A.scheme
      (A.obj A.scheme (𝟙 A.scheme))) :
    A.PullbackPresentation A.scheme
      (A.obj A.scheme (𝟙 A.scheme)) where
  space := p.space
  fst := p.snd
  snd := p.fst
  comparison := p.selfSwapComparison
  lift toBase toChart c :=
    p.lift toChart toBase (A.selfSwapTestComparison c)
  lift_fst toBase toChart c :=
    p.lift_snd toChart toBase (A.selfSwapTestComparison c)
  lift_snd toBase toChart c :=
    p.lift_fst toChart toBase (A.selfSwapTestComparison c)
  lift_compatible toBase toChart c :=
    (A.classifies_selfSwap_iff p toBase toChart c
      (p.lift toChart toBase (A.selfSwapTestComparison c))).2
        (p.lift_compatible toChart toBase (A.selfSwapTestComparison c))
  lift_unique toBase toChart c m compatible :=
    p.lift_unique toChart toBase (A.selfSwapTestComparison c) m
      ((A.classifies_selfSwap_iff p toBase toChart c m).1 compatible)

/-- A chart is representable with property `P` if all its two-pullbacks by objects over schemes
are represented by schemes and every representing presentation has projection in `P`.

The universal property makes any two presentations uniquely isomorphic, but recording `P` for
all presentations here keeps the definition independent of a silently preferred model even when
`P` is supplied abstractly. -/
def HasRepresentableProperty (P : MorphismProperty Scheme.{u}) : Prop :=
  (∀ (T : Scheme.{u}) (x : StackFiber X T),
    Nonempty (A.PullbackPresentation T x)) ∧
  ∀ (T : Scheme.{u}) (x : StackFiber X T)
    (p : A.PullbackPresentation T x), P p.fst

/-- A representable chart. -/
abbrev IsRepresentable : Prop :=
  A.HasRepresentableProperty ⊤

/-- A smooth representable chart. -/
abbrev IsSmooth : Prop :=
  A.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u})

/-- An etale representable chart. -/
abbrev IsEtale : Prop :=
  A.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})

/-- A representably surjective chart. -/
abbrev IsSurjective : Prop :=
  A.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})

/-- Smooth surjective atlas condition, checked on every scheme base change. -/
abbrev IsSmoothSurjective : Prop :=
  A.HasRepresentableProperty
    ((@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective) :
      MorphismProperty Scheme.{u})

/-- Etale surjective atlas condition, checked on every scheme base change. -/
abbrev IsEtaleSurjective : Prop :=
  A.HasRepresentableProperty
    ((@_root_.AlgebraicGeometry.Etale ⊓ @_root_.AlgebraicGeometry.Surjective) :
      MorphismProperty Scheme.{u})

theorem isRepresentable_of_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) (h : A.HasRepresentableProperty P) :
    A.IsRepresentable := by
  exact ⟨h.1, fun _ _ _ ↦ trivial⟩

end StackChart

/-- Pull the universal isomorphism of a proposed diagonal presentation back along a candidate
scheme map. -/
noncomputable def diagonalInducedIso (X : FppfStack.{u})
    {U T : Scheme.{u}} (map : U ⟶ T) {x y : StackFiber X T}
    (universal : (stackPullback X map).obj x ≅ (stackPullback X map).obj y)
    {S : Scheme.{u}} (g : S ⟶ U) :
    (stackPullback X (g ≫ map)).obj x ≅
      (stackPullback X (g ≫ map)).obj y :=
  stackPullbackIso X g map universal

/-- A candidate map to an isomorphism scheme classifies a supplied isomorphism exactly when
its pullback of the universal isomorphism is that isomorphism. -/
def DiagonalClassifies (X : FppfStack.{u})
    {U T : Scheme.{u}} (map : U ⟶ T) {x y : StackFiber X T}
    (universal : (stackPullback X map).obj x ≅ (stackPullback X map).obj y)
    {S : Scheme.{u}} (f : S ⟶ T)
    (e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y)
  (g : S ⟶ U) : Prop :=
  ∃ map_eq : g ≫ map = f,
    (stackPullbackObjIsoOfEq X map_eq x).symm.trans
      ((diagonalInducedIso X map universal g).trans
        (stackPullbackObjIsoOfEq X map_eq y)) = e

/-- A scheme representing the isomorphism sheaf between two objects in one stack fibre.  This
is the scheme base change of the diagonal. -/
structure DiagonalPresentation (X : FppfStack.{u}) (T : Scheme.{u})
    (x y : StackFiber X T) where
  /-- The scheme of isomorphisms. -/
  space : Scheme.{u}
  /-- Its structural map to the test scheme. -/
  map : space ⟶ T
  /-- The universal isomorphism after pullback. -/
  universalIso : (stackPullback X map).obj x ≅ (stackPullback X map).obj y
  /-- Pull an isomorphism over `S` back from the universal one. -/
  lift {S : Scheme.{u}} (f : S ⟶ T)
      (e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y) : S ⟶ space
  lift_map {S : Scheme.{u}} (f : S ⟶ T)
      (e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y) :
    lift f e ≫ map = f
  lift_compatible {S : Scheme.{u}} (f : S ⟶ T)
      (e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y) :
    DiagonalClassifies X map universalIso f e (lift f e)
  lift_unique {S : Scheme.{u}} (f : S ⟶ T)
      (e : (stackPullback X f).obj x ≅ (stackPullback X f).obj y)
      (g : S ⟶ space) (compatible : DiagonalClassifies X map universalIso f e g) :
    g = lift f e

/-- The diagonal of a stack is representable if every isomorphism sheaf has a representing
scheme. -/
def HasRepresentableDiagonal (X : FppfStack.{u}) : Prop :=
  ∀ (T : Scheme.{u}) (x y : StackFiber X T),
    Nonempty (DiagonalPresentation X T x y)

/-- The comparison classified by a map into a proposed base-change presentation.  It is
obtained from the universal source object and universal comparison by actual stack pullback,
including the strong-transformation and pseudofunctor coherence isomorphisms. -/
noncomputable def stackMorphismInducedComparison
    {X Y : FppfStack.{u}} (f : StackHom X Y)
    {U T : Scheme.{u}} (map : U ⟶ T) (object : StackFiber X U)
    (y : StackFiber Y T)
    (universal : (StackHom.appFunctor f U).obj object ≅
      (stackPullback Y map).obj y)
    {S : Scheme.{u}} (g : S ⟶ U) (x : StackFiber X S)
    (objectIso : x ≅ (stackPullback X g).obj object) :
    (StackHom.appFunctor f S).obj x ≅
      (stackPullback Y (g ≫ map)).obj y :=
  (((StackHom.appFunctor f S).mapIso objectIso).trans
    ((Cat.Hom.toNatIso (f.naturality ⟨g.op⟩)).app object)).trans
      (((stackPullback Y g).mapIso universal).trans
        (stackPullbackCompIso Y g map y))

/-- A candidate map into a morphism presentation classifies the supplied source object and
comparison precisely when the comparison induced from the universal family is the supplied
one.  This equation is what prevents distinct stabilizer arrows from being collapsed by the
scheme-valued universal property. -/
def StackMorphismClassifies
    {X Y : FppfStack.{u}} (f : StackHom X Y)
    {U T : Scheme.{u}} (map : U ⟶ T) (object : StackFiber X U)
    (y : StackFiber Y T)
    (universal : (StackHom.appFunctor f U).obj object ≅
      (stackPullback Y map).obj y)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (comparison : (StackHom.appFunctor f S).obj x ≅
      (stackPullback Y toBase).obj y)
    (g : S ⟶ U)
    (objectIso : x ≅ (stackPullback X g).obj object) : Prop :=
  ∃ map_eq : g ≫ map = toBase,
    (stackMorphismInducedComparison f map object y universal g x objectIso).trans
      (stackPullbackObjIsoOfEq Y map_eq y) = comparison


/-- A scheme presentation of the base change of a stack morphism by an object over a scheme.
Besides the representing scheme it includes the universal source object and the comparison
2-cell to the pulled-back target object. -/
structure StackMorphismPresentation {X Y : FppfStack.{u}} (f : StackHom X Y)
    (T : Scheme.{u}) (y : StackFiber Y T) where
  /-- The scheme representing `X ×_Y T`. -/
  space : Scheme.{u}
  /-- Projection to `T`. -/
  map : space ⟶ T
  /-- The universal source object. -/
  object : StackFiber X space
  /-- Its image is identified with the pullback of `y`. -/
  comparison : (StackHom.appFunctor f space).obj object ≅
    (stackPullback Y map).obj y
  /-- Universal classifying map for an object and a comparison 2-cell. -/
  lift {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
      (comparison : (StackHom.appFunctor f S).obj x ≅
        (stackPullback Y toBase).obj y) : S ⟶ space
  lift_map {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
      (comparison : (StackHom.appFunctor f S).obj x ≅
        (stackPullback Y toBase).obj y) :
    lift toBase x comparison ≫ map = toBase
  /-- The source object is locally the pullback of the universal one. -/
  liftObjectIso {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
      (comparison : (StackHom.appFunctor f S).obj x ≅
        (stackPullback Y toBase).obj y) :
    x ≅ (stackPullback X (lift toBase x comparison)).obj object
  /-- The chosen lift really classifies the supplied comparison, after pulling back the
  universal object and universal comparison. -/
  lift_compatible {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
      (c : (StackHom.appFunctor f S).obj x ≅
        (stackPullback Y toBase).obj y) :
    StackMorphismClassifies f map object y comparison toBase x c
      (lift toBase x c) (liftObjectIso toBase x c)
  /-- Once the classifying scheme map is fixed, the isomorphism with the pulled-back universal
  object is uniquely forced by the supplied comparison.  This excludes nontrivial relative
  automorphisms from being forgotten by a merely set-valued universal property. -/
  liftObjectIso_unique {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
      (c : (StackHom.appFunctor f S).obj x ≅
        (stackPullback Y toBase).obj y)
      (objectIso : x ≅ (stackPullback X (lift toBase x c)).obj object)
      (compatible : StackMorphismClassifies f map object y comparison
        toBase x c (lift toBase x c) objectIso) :
    objectIso = liftObjectIso toBase x c
  lift_unique {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
      (c : (StackHom.appFunctor f S).obj x ≅
        (stackPullback Y toBase).obj y)
      (g : S ⟶ space)
      (objectIso : x ≅ (stackPullback X g).obj object)
      (compatible : StackMorphismClassifies f map object y comparison
        toBase x c g objectIso) :
    g = lift toBase x c

namespace StackHom

variable {X Y : FppfStack.{u}} (f : StackHom X Y)

private theorem identityPresentation_map_eq {S T : Scheme.{u}} (toBase : S ⟶ T) :
    toBase ≫ 𝟙 T = toBase :=
  Category.comp_id _

/-- The component functor of the identity strong transformation is fully faithful. -/
def identityAppFullyFaithful (X : FppfStack.{u}) (S : Scheme.{u}) :
    (StackHom.appFunctor
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor) S).FullyFaithful := by
  exact Functor.FullyFaithful.id _

/-- The fixed coherence tail occurring when the identity stack morphism classifies an object
after pullback.  Isolating it lets the universal object isomorphism be chosen so that the
classified comparison is definitionally forced to be the supplied one. -/
noncomputable def identityClassificationTail (X : FppfStack.{u})
    {S T : Scheme.{u}} (toBase : S ⟶ T) (y : StackFiber X T) :
    (StackHom.appFunctor
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor) S).obj
        ((stackPullback X toBase).obj y) ≅
      (stackPullback X toBase).obj y :=
  ((Cat.Hom.toNatIso
      ((Pseudofunctor.StrongTrans.id X.toPseudofunctor).naturality
        ⟨toBase.op⟩)).app y).trans
    (((stackPullback X toBase).mapIso
      ((Cat.Hom.toNatIso
        (X.toPseudofunctor.mapId
          (LocallyDiscrete.mk (Opposite.op T)))).symm.app y)).trans
      ((stackPullbackCompIso X toBase (𝟙 T) y).trans
        (stackPullbackObjIsoOfEq X (identityPresentation_map_eq toBase) y)))

/-- The source-object isomorphism for the identity presentation is the unique preimage of the
supplied comparison with the fixed coherence tail removed. -/
noncomputable def identityClassificationObjectIso (X : FppfStack.{u})
    {S T : Scheme.{u}} (toBase : S ⟶ T) (y : StackFiber X T)
    (x : StackFiber X S)
    (c : (StackHom.appFunctor
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor) S).obj x ≅
        (stackPullback X toBase).obj y) :
    x ≅ (stackPullback X toBase).obj y := by
  exact (identityAppFullyFaithful X S).preimageIso
    (c.trans (identityClassificationTail X toBase y).symm)

@[simp]
theorem identityClassificationObjectIso_map (X : FppfStack.{u})
    {S T : Scheme.{u}} (toBase : S ⟶ T) (y : StackFiber X T)
    (x : StackFiber X S)
    (c : (StackHom.appFunctor
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor) S).obj x ≅
        (stackPullback X toBase).obj y) :
    (StackHom.appFunctor
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor) S).map
        (identityClassificationObjectIso X toBase y x c).hom =
      (c.trans (identityClassificationTail X toBase y).symm).hom := by
  unfold identityClassificationObjectIso
  exact (identityAppFullyFaithful X S).map_preimage _

/-- For the identity presentation, the general induced-comparison formula is its mapped source
isomorphism followed by the fixed identity coherence tail. -/
theorem identityInducedComparison_eq (X : FppfStack.{u})
    {S T : Scheme.{u}} (toBase : S ⟶ T) (y : StackFiber X T)
    (x : StackFiber X S)
    (objectIso : x ≅ (stackPullback X toBase).obj y) :
    (stackMorphismInducedComparison
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor)
      (𝟙 T) y y
      ((Cat.Hom.toNatIso
        (X.toPseudofunctor.mapId
          (LocallyDiscrete.mk (Opposite.op T)))).symm.app y)
      toBase x objectIso).trans
        (stackPullbackObjIsoOfEq X
          (identityPresentation_map_eq toBase) y) =
      ((StackHom.appFunctor
        (Pseudofunctor.StrongTrans.id X.toPseudofunctor) S).mapIso
          objectIso).trans (identityClassificationTail X toBase y) := by
  unfold stackMorphismInducedComparison identityClassificationTail
  simp only [Iso.trans_assoc]
  congr 1

/-- The scheme `T` itself represents the base change of the identity of a stack by an object
`y : X(T)`.  The comparison 2-cell is the unit constraint of the stack pseudofunctor. -/
noncomputable def identityPresentation (X : FppfStack.{u})
    (T : Scheme.{u}) (y : StackFiber X T) :
    StackMorphismPresentation
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor : StackHom X X) T y where
  space := T
  map := 𝟙 T
  object := y
  comparison := (Cat.Hom.toNatIso
    (X.toPseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op T)))).symm.app y
  lift toBase _ _ := toBase
  lift_map toBase _ _ := identityPresentation_map_eq toBase
  liftObjectIso toBase x c := identityClassificationObjectIso X toBase y x c
  lift_compatible toBase x c := by
    refine ⟨identityPresentation_map_eq toBase, ?_⟩
    have hcanonical :
        (stackMorphismInducedComparison
          (Pseudofunctor.StrongTrans.id X.toPseudofunctor)
          (𝟙 T) y y
          ((Cat.Hom.toNatIso
            (X.toPseudofunctor.mapId
              (LocallyDiscrete.mk (Opposite.op T)))).symm.app y)
          toBase x (identityClassificationObjectIso X toBase y x c)).trans
            (stackPullbackObjIsoOfEq X
              (identityPresentation_map_eq toBase) y) = c := by
      rw [identityInducedComparison_eq]
      apply Iso.ext
      simp only [Iso.trans_hom]
      simp
    convert hcanonical using 1
  liftObjectIso_unique toBase x c objectIso compatible := by
    obtain ⟨mapEq, hcomparison⟩ := compatible
    have hcomparison' :
        (stackMorphismInducedComparison
          (Pseudofunctor.StrongTrans.id X.toPseudofunctor)
          (𝟙 T) y y
          ((Cat.Hom.toNatIso
            (X.toPseudofunctor.mapId
              (LocallyDiscrete.mk (Opposite.op T)))).symm.app y)
          toBase x objectIso).trans
            (stackPullbackObjIsoOfEq X
              (identityPresentation_map_eq toBase) y) = c := by
      convert hcomparison using 1
    rw [identityInducedComparison_eq] at hcomparison'
    apply Iso.ext
    apply (identityAppFullyFaithful X _).map_injective
    apply (cancel_mono (identityClassificationTail X toBase y).hom).1
    have hchosen := identityClassificationObjectIso_map X toBase y x c
    rw [hchosen]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    simpa only [Iso.trans_hom, Functor.mapIso_hom] using
      congrArg Iso.hom hcomparison'
  lift_unique _ _ _ m _ hcompatible := by
    obtain ⟨hm, -⟩ := hcompatible
    simpa using hm

/-- Raw representability means that every scheme base change is represented by a scheme whose
projection has the corresponding Mathlib scheme property. -/
def HasRepresentablePropertyRaw (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (T : Scheme.{u}) (y : StackFiber Y T),
    Nonempty {p : StackMorphismPresentation f T y // P p.map}

/-- Representable properties are the 2-isomorphism-invariant closure of the raw universal
property.  The witness is still an actual strong stack morphism with actual compatible scheme
presentations; taking the closure here avoids transporting those presentations through a
modification before that coherence theorem has been established. -/
def HasRepresentableProperty (P : MorphismProperty Scheme.{u}) : Prop :=
  ∃ g : StackHom X Y, Nonempty (StackIso2 f g) ∧ g.HasRepresentablePropertyRaw P

/-- Representable geometric properties depend only on the 2-isomorphism class of a stack
morphism, by composition of the displayed invertible 2-cells. -/
theorem hasRepresentableProperty_congr
    {f g : StackHom X Y} (P : MorphismProperty Scheme.{u}) (e : StackIso2 f g) :
    f.HasRepresentableProperty P ↔ g.HasRepresentableProperty P := by
  constructor
  · rintro ⟨h, ⟨eh⟩, hh⟩
    exact ⟨h, ⟨e.symm.trans eh⟩, hh⟩
  · rintro ⟨h, ⟨eh⟩, hh⟩
    exact ⟨h, ⟨e.trans eh⟩, hh⟩

/-- Every scheme-morphism property containing identities holds representably on the identity
of every stack. -/
theorem id_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    (X : FppfStack.{u}) :
    HasRepresentableProperty
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor : StackHom X X) P := by
  refine ⟨Pseudofunctor.StrongTrans.id X.toPseudofunctor,
    ⟨StackIso2.refl _⟩, ?_⟩
  intro T y
  exact ⟨⟨identityPresentation X T y, MorphismProperty.id_mem P T⟩⟩

/-- Representability by schemes. -/
abbrev IsRepresentable : Prop :=
  f.HasRepresentableProperty ⊤

theorem isRepresentable_of_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) (h : f.HasRepresentableProperty P) :
    f.IsRepresentable := by
  obtain ⟨g, eg, hg⟩ := h
  refine ⟨g, eg, ?_⟩
  intro T y
  obtain ⟨⟨p, hp⟩⟩ := hg T y
  exact ⟨⟨p, trivial⟩⟩

/-- Representably smooth morphisms of stacks. -/
abbrev Smooth : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u})

/-- Representably etale morphisms of stacks. -/
abbrev Etale : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})

/-- Representably unramified morphisms of stacks. -/
abbrev Unramified : Prop :=
  f.HasRepresentableProperty
    (@GromovWitten.AlgebraicGeometry.Unramified : MorphismProperty Scheme.{u})

/-- Representably flat morphisms of stacks. -/
abbrev Flat : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.Flat : MorphismProperty Scheme.{u})

/-- Representably proper morphisms of stacks. -/
abbrev Proper : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u})

/-- Representably separated morphisms of stacks. -/
abbrev Separated : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u})

/-- Representably locally finitely presented morphisms of stacks. -/
abbrev LocallyOfFinitePresentation : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation : MorphismProperty Scheme.{u})

/-- Representably locally finite-type morphisms of stacks. -/
abbrev LocallyOfFiniteType : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u})

/-- Representably quasi-compact morphisms of stacks. -/
abbrev QuasiCompact : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})

/-- Representably finite-type morphisms of stacks. -/
abbrev FiniteType : Prop :=
  f.HasRepresentableProperty
    ((@_root_.AlgebraicGeometry.QuasiCompact ⊓
      @_root_.AlgebraicGeometry.LocallyOfFiniteType) : MorphismProperty Scheme.{u})

/-- Representably finite-presentation morphisms of stacks. -/
abbrev FinitePresentation : Prop :=
  f.HasRepresentableProperty
    ((@_root_.AlgebraicGeometry.QuasiCompact ⊓
      @_root_.AlgebraicGeometry.LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})

/-- Representable immersions of stacks. -/
abbrev Immersion : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u})

/-- Representable local immersions of stacks. -/
abbrev LocalImmersion : Prop :=
  f.Immersion

/-- Representable open immersions of stacks. -/
abbrev OpenImmersion : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})

/-- Representable closed immersions of stacks. -/
abbrev ClosedImmersion : Prop :=
  f.HasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})

/-- Representable regular immersions of stacks. -/
abbrev RegularImmersion : Prop :=
  f.HasRepresentableProperty
    ((@_root_.AlgebraicGeometry.IsClosedImmersion ⊓
      @GromovWitten.AlgebraicGeometry.LocallyCompleteIntersection) :
      MorphismProperty Scheme.{u})

end StackHom

/-- A representable property of the diagonal, expressed on each actual isomorphism scheme. -/
def DiagonalHasProperty (X : FppfStack.{u}) (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (T : Scheme.{u}) (x y : StackFiber X T),
    Nonempty {p : DiagonalPresentation X T x y // P p.map}

theorem diagonal_representable_of_property (X : FppfStack.{u})
    (P : MorphismProperty Scheme.{u}) (h : DiagonalHasProperty X P) :
    HasRepresentableDiagonal X := by
  intro T x y
  obtain ⟨⟨p, hp⟩⟩ := h T x y
  exact ⟨p⟩

/-- Algebraic-stack data on an actual groupoid-valued fppf stack. -/
structure AlgebraicStack where
  /-- The underlying stack in groupoids. -/
  toStack : FppfStack.{u}
  /-- Its diagonal is representable. -/
  diagonal_representable : HasRepresentableDiagonal toStack
  /-- A smooth surjective scheme atlas exists. -/
  smoothAtlas : ∃ A : StackChart toStack, A.IsSmoothSurjective

/-- Deligne--Mumford-stack data: an algebraic stack equipped with an etale surjective scheme
atlas.

The unramifiedness of the diagonal is deliberately not a field: its equivalence with the
existence of an etale atlas is a theorem of Deligne--Mumford stack geometry and must be proved,
not requested again from every constructor. -/
structure DeligneMumfordStack extends AlgebraicStack.{u} where
  /-- A representable etale surjective scheme atlas exists. -/
  etaleAtlas : ∃ A : StackChart toStack, A.IsEtaleSurjective

namespace DeligneMumfordStack

/-- A DM stack is, in particular, an algebraic stack. -/
abbrev asAlgebraicStack (X : DeligneMumfordStack.{u}) : AlgebraicStack.{u} :=
  X.toAlgebraicStack

/-- The inertia group at an object is its actual automorphism group in the fibre groupoid. -/
abbrev inertia (X : DeligneMumfordStack.{u}) (T : Scheme.{u})
    (x : StackFiber X.toStack T) :=
  x ⟶ x

end DeligneMumfordStack

/-- A scheme is pure of dimension `d` when every irreducible component has topological Krull
dimension `d`.  Unlike a bare integer label, this proposition is determined by the underlying
topological space of the scheme. -/
def SchemePureDimension (X : Scheme.{u}) (d : ℕ) : Prop :=
  ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d

/-- The spectrum of a field is genuinely pure zero-dimensional. -/
theorem schemePureDimension_spec_field (k : Type u) [Field k] :
    SchemePureDimension (_root_.AlgebraicGeometry.Spec (.of k)) 0 := by
  intro Z hZ
  let _ : Nonempty Z := Set.nonempty_coe_sort.mpr hZ.1.nonempty
  let _ : Subsingleton Z :=
    ⟨fun x y ↦ Subtype.ext (Subsingleton.elim x.1 y.1)⟩
  let _ : Unique Z :=
    { default := Classical.choice (inferInstance : Nonempty Z)
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  let _ : Nonempty (TopologicalSpace.IrreducibleCloseds Z) :=
    ⟨⟨closure ({default} : Set Z), isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology Z)
    (by
      change 0 ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds Z)
      exact Order.krullDim_nonneg)

/-- A scheme morphism has pure relative dimension `d` when it is locally of finite type and every
irreducible component of every scheme-theoretic fibre has dimension `d`. -/
def SchemeMorphismPureRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) : Prop :=
  _root_.AlgebraicGeometry.LocallyOfFiniteType f ∧
    ∀ y : Y, ∀ Z ∈ irreducibleComponents (f.fiber y), topologicalKrullDim Z = d

/-- Raw pure-relative-dimension data for a displayed stack morphism: every compatible scheme
presentation of every base change has the prescribed scheme-theoretic fibre dimension. -/
def StackHom.HasPureRelativeDimensionRaw {X Y : FppfStack.{u}}
    (f : StackHom X Y) (d : ℕ) : Prop :=
  ∀ (T : Scheme.{u}) (y : StackFiber Y T),
    Nonempty {p : StackMorphismPresentation f T y //
      SchemeMorphismPureRelativeDimension p.map d}

/-- Pure relative dimension is the 2-isomorphism-invariant closure of the raw geometric
predicate.  The dimension remains certified on actual scheme presentations of the witness. -/
def StackHom.HasPureRelativeDimension {X Y : FppfStack.{u}}
    (f : StackHom X Y) (d : ℕ) : Prop :=
  ∃ g : StackHom X Y, Nonempty (StackIso2 f g) ∧ g.HasPureRelativeDimensionRaw d

theorem StackHom.hasPureRelativeDimension_congr
    {X Y : FppfStack.{u}} {f g : StackHom X Y} {d : ℕ}
    (e : StackIso2 f g) :
    f.HasPureRelativeDimension d ↔ g.HasPureRelativeDimension d := by
  constructor
  · rintro ⟨h, ⟨eh⟩, hh⟩
    exact ⟨h, ⟨e.symm.trans eh⟩, hh⟩
  · rintro ⟨h, ⟨eh⟩, hh⟩
    exact ⟨h, ⟨e.trans eh⟩, hh⟩

theorem StackHom.HasPureRelativeDimension.isRepresentable
    {X Y : FppfStack.{u}} {f : StackHom X Y} {d : ℕ}
    (h : f.HasPureRelativeDimension d) : f.IsRepresentable :=
  by
    obtain ⟨g, eg, hg⟩ := h
    refine ⟨g, eg, ?_⟩
    intro T y
    obtain ⟨⟨p, hp⟩⟩ := hg T y
    exact ⟨⟨p, trivial⟩⟩

theorem StackHom.HasPureRelativeDimension.witness
    {X Y : FppfStack.{u}} {f : StackHom X Y} {d : ℕ}
    (h : f.HasPureRelativeDimension d) :
    ∃ g : StackHom X Y, Nonempty (StackIso2 f g) ∧
      g.HasPureRelativeDimensionRaw d :=
  h

/-- A scheme isomorphism has pure relative dimension zero.  Its fibres are transported to
subsingletons by the underlying homeomorphism, so every nonempty irreducible closed subset of a
fibre has Krull dimension zero. -/
theorem schemeMorphismPureRelativeDimension_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    SchemeMorphismPureRelativeDimension f 0 := by
  refine ⟨by infer_instance, fun y Z hZ ↦ ?_⟩
  let e := _root_.AlgebraicGeometry.Scheme.Hom.fiberHomeo f y
  let _ : Subsingleton (f ⁻¹' {y}) := by
    constructor
    intro a b
    apply Subtype.ext
    apply (TopCat.mono_iff_injective f.base).mp (inferInstance : Mono f.base)
    exact a.property.trans b.property.symm
  let _ : Subsingleton (f.fiber y) := e.toEquiv.subsingleton
  let _ : Nonempty Z := Set.nonempty_coe_sort.mpr hZ.1.nonempty
  let _ : Subsingleton Z :=
    ⟨fun x z ↦ Subtype.ext (Subsingleton.elim x.1 z.1)⟩
  let _ : Unique Z :=
    { default := Classical.choice (inferInstance : Nonempty Z)
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  let _ : Nonempty (TopologicalSpace.IrreducibleCloseds Z) :=
    ⟨⟨closure ({default} : Set Z), isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology Z)
    (by
      change 0 ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds Z)
      exact Order.krullDim_nonneg)

/-- An identity morphism has pure relative dimension zero. -/
theorem schemeMorphismPureRelativeDimension_id (X : Scheme.{u}) :
    SchemeMorphismPureRelativeDimension (𝟙 X) 0 := by
  refine ⟨by infer_instance, fun x Z hZ ↦ ?_⟩
  let e := _root_.AlgebraicGeometry.Scheme.Hom.fiberHomeo (𝟙 X) x
  let _ : Subsingleton ((𝟙 X : X ⟶ X) ⁻¹' {x}) := by
    constructor
    intro a b
    apply Subtype.ext
    have ha : (𝟙 X : X ⟶ X) (a : X) = a := rfl
    have hb : (𝟙 X : X ⟶ X) (b : X) = b := rfl
    exact ha.symm.trans (a.property.trans b.property.symm) |>.trans hb
  let _ : Subsingleton ((𝟙 X : X ⟶ X).fiber x) := e.toEquiv.subsingleton
  let _ : Nonempty Z := Set.nonempty_coe_sort.mpr hZ.1.nonempty
  let _ : Subsingleton Z :=
    ⟨fun y z ↦ Subtype.ext (Subsingleton.elim y.1 z.1)⟩
  let _ : Unique Z :=
    { default := Classical.choice (inferInstance : Nonempty Z)
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  let _ : Nonempty (TopologicalSpace.IrreducibleCloseds Z) :=
    ⟨⟨closure ({default} : Set Z), isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology Z)
    (by
      change 0 ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds Z)
      exact Order.krullDim_nonneg)

/-- The identity of a stack has pure relative dimension zero.  For an arbitrary scheme
presentation of its base change, the universal property constructs an inverse to the presenting
scheme map; hence every fibre is a point. -/
theorem StackHom.id_hasPureRelativeDimension (X : FppfStack.{u}) :
    StackHom.HasPureRelativeDimension
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor : StackHom X X) 0 := by
  refine ⟨Pseudofunctor.StrongTrans.id X.toPseudofunctor,
    ⟨StackIso2.refl _⟩, ?_⟩
  intro T y
  exact ⟨⟨StackHom.identityPresentation X T y,
    schemeMorphismPureRelativeDimension_id T⟩⟩

namespace StackChart

/-- A representable chart has pure relative dimension `d` when every scheme presentation of every
base change has pure relative dimension `d`.  Quantifying over the actual pullback presentations
prevents an unrelated integer from being attached to the chart. -/
def HasPureRelativeDimension {X : FppfStack.{u}} (A : StackChart X) (d : ℕ) : Prop :=
  A.IsRepresentable ∧
    ∀ (T : Scheme.{u}) (x : StackFiber X T) (p : A.PullbackPresentation T x),
      SchemeMorphismPureRelativeDimension p.fst d

theorem HasPureRelativeDimension.isRepresentable
    {X : FppfStack.{u}} {A : StackChart X} {d : ℕ}
    (h : A.HasPureRelativeDimension d) : A.IsRepresentable :=
  h.1

theorem HasPureRelativeDimension.presentation
    {X : FppfStack.{u}} {A : StackChart X} {d : ℕ}
    (h : A.HasPureRelativeDimension d) (T : Scheme.{u}) (x : StackFiber X T)
    (p : A.PullbackPresentation T x) :
    SchemeMorphismPureRelativeDimension p.fst d :=
  h.2 T x p

end StackChart

/-- An atlas dimension presentation records the geometric evidence behind the correction
`dim(atlas) - relativeDimension(atlas/X)`.  Both numbers are natural because they are dimensions
of schemes; the corrected stack dimension may be negative. -/
structure StackDimensionPresentation (X : AlgebraicStack.{u}) where
  atlas : StackChart X.toStack
  isSmoothSurjective : atlas.IsSmoothSurjective
  atlasDimension : ℕ
  atlasPureDimension : SchemePureDimension atlas.scheme atlasDimension
  relativeDimension : ℕ
  atlasPureRelativeDimension : atlas.HasPureRelativeDimension relativeDimension

namespace StackDimensionPresentation

/-- The dimension computed by a smooth atlas. -/
def correctedDimension {X : AlgebraicStack.{u}} (A : StackDimensionPresentation X) : ℤ :=
  (A.atlasDimension : ℤ) - (A.relativeDimension : ℤ)

end StackDimensionPresentation

/-- A stack has pure dimension `d` when it admits a geometrically certified pure atlas whose
corrected dimension is `d`.  Atlas independence is deliberately *not* a field of this predicate:
it is a theorem to be proved from the geometry of smooth common refinements. -/
def PureStackDimension (X : AlgebraicStack.{u}) (d : ℤ) : Prop :=
  ∃ A : StackDimensionPresentation X, A.correctedDimension = d

/-- The atlas-independence statement for stack dimension, isolated as a theorem-shaped
proposition rather than silently bundled into every assertion of pure dimension. -/
def StackDimensionIndependent (X : AlgebraicStack.{u}) : Prop :=
  ∀ A B : StackDimensionPresentation X, A.correctedDimension = B.correctedDimension

theorem pureStackDimension_unique {X : AlgebraicStack.{u}} {d e : ℤ}
    (hIndependent : StackDimensionIndependent X)
    (hd : PureStackDimension X d) (he : PureStackDimension X e) : d = e := by
  obtain ⟨A, hA⟩ := hd
  obtain ⟨B, hB⟩ := he
  rw [← hA, hIndependent A B, hB]

/-
Retired numerical quotient-dimension placeholder.  The former record held two unrelated
integers and called their difference the dimension of a quotient without carrying a quotient
stack, a smooth group, or dimension proofs.

/-- A quotient-dimension presentation packages the standard smooth-group calculation. -/
structure SmoothQuotientDimension where
  spaceDimension : ℤ
  groupDimension : ℤ

namespace SmoothQuotientDimension

/-- `dim [U/G] = dim U - dim G`. -/
def quotientDimension (Q : SmoothQuotientDimension) : ℤ :=
  Q.spaceDimension - Q.groupDimension

@[simp]
theorem quotientDimension_eq (Q : SmoothQuotientDimension) :
    Q.quotientDimension = Q.spaceDimension - Q.groupDimension :=
  rfl

end SmoothQuotientDimension

-/

end GromovWitten.AlgebraicGeometry
