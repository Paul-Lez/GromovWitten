/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Groupoid

/-!
# Gluing a family of groupoids along transition equivalences

Behrend–Fantechi's intrinsic normal cone `𝔠_X` is *defined* by gluing the local presentations
`[C_{U_i/M_i} / T_{M_i}|_{U_i}]` attached to local embeddings of `X` into smooth schemes.  This is
not a gluing of sheaves: the local objects are groupoid-valued, the transition data are
equivalences of groupoids, and the compatibility on triple overlaps is an *isomorphism* of
functors, not an equality.  This file contains the unconditional, purely categorical half of that
construction: the descent of a family of groupoids along a cocycle of transition equivalences.

## The descent datum

`GluingData F` is descent data for a family of groupoids `F : ι → Type u`:

* transition functors `trans i j : F i ⥤ F j` for every ordered pair of charts;
* unit isomorphisms `unit i : trans i i ≅ 𝟭 (F i)`;
* cocycle isomorphisms `cocycle i j k : trans i j ⋙ trans j k ≅ trans i k`;
* the two unit coherences `cocycle_unit_left`, `cocycle_unit_right` and the **tetrahedron
  identity** `tetrahedron` relating the two contractions of a quadruple of charts.

All axioms are stated componentwise, which avoids any `eqToHom` juggling with the (definitional,
but not syntactic) unitors and associators of functor composition.

## The glued groupoid

`Glue G` has objects the pairs `⟨i, x⟩` with `x : F i` and morphisms
`⟨i, x⟩ ⟶ ⟨j, y⟩` the morphisms `(trans i j).obj x ⟶ y`, with composition twisted by the
cocycle.  This is the Grothendieck construction of the pseudofunctor `ι → Grpd` on the chaotic
category of charts; since that pseudofunctor is not a strict functor, Mathlib's
`CategoryTheory.Grothendieck` does not apply and the construction is carried out by hand.

The main results are:

* `Glue.instCategory` and `Glue.instGroupoid`: `Glue G` is a groupoid.  Invertibility is proved
  by showing that *every* morphism has a right inverse (which needs only the unit axioms) and
  then by the usual cancellation argument.
* `Glue.inc G i : F i ⥤ Glue G` is full, faithful and essentially surjective, hence an
  equivalence (`Glue.inc_isEquivalence`, `Glue.incEquivalence`): **every chart computes the
  glued groupoid**.  This is the prestack-level statement that the glued object is canonically
  equivalent to each of its local presentations.
* `GluingData.transEquivalence`: each transition functor is itself an equivalence, a formal
  consequence of the cocycle and unit isomorphisms.
* `Glue.incTransIso`: the canonical isomorphism `inc G i ≅ trans i j ⋙ inc G j` comparing the
  two chart presentations of a point of the glued groupoid.

## Naturality in the test object

A `GluingData` is the datum glued over one fixed test object.  Naturality in the test object is
provided by `GluingHom`, a morphism of gluing data: a family of functors between the charts
commuting with the transition functors up to a natural isomorphism compatible with the units and
the cocycles.  `GluingHom.glue` is the induced functor between the glued groupoids and
`GluingHom.incGlueIso` its compatibility with the charts.  So a family of `GluingData` indexed by
test objects, together with a `GluingHom` for every morphism of test objects, produces the
restriction functors of the glued prestack; what is *not* proved here is that this assignment is
itself functorial (there is no composition of `GluingHom`s yet), which is what would be needed to
package the result as a pseudofunctor.

Stackification (descent of *objects* rather than descent of the local groupoids along a given
cocycle) is not addressed here.
-/

namespace GromovWitten.AlgebraicGeometry

namespace GroupoidGluing

open CategoryTheory

universe v u u' w

variable {ι : Type w} {F : ι → Type u} [∀ i, Groupoid.{v} (F i)]

/-- In any category, a morphism which is both a left and a right inverse of a morphism `u` is the
unique such. -/
theorem eq_of_comp_eq_id {C : Type*} [Category C] {X Y : C} {u : X ⟶ Y} {a b : Y ⟶ X}
    (ha : a ≫ u = 𝟙 Y) (hb : u ≫ b = 𝟙 X) : a = b := by
  rw [← Category.comp_id a, ← hb, ← Category.assoc, ha, Category.id_comp]

/-- **Descent data for a family of groupoids.**  For each ordered pair of charts a transition
functor, together with unit and cocycle isomorphisms subject to the two unit coherences and the
tetrahedron identity on quadruples of charts.  This is exactly the data of a pseudofunctor into
groupoids on the chaotic category with object set `ι`. -/
structure GluingData (F : ι → Type u) [∀ i, Groupoid.{v} (F i)] where
  /-- The transition functor from the chart `i` to the chart `j`. -/
  trans : ∀ i j, F i ⥤ F j
  /-- The transition functor of a chart with itself is the identity. -/
  unit : ∀ i, trans i i ≅ 𝟭 (F i)
  /-- The cocycle isomorphism on a triple of charts. -/
  cocycle : ∀ i j k, trans i j ⋙ trans j k ≅ trans i k
  /-- Compatibility of the cocycle with the unit in the first variable. -/
  cocycle_unit_left : ∀ (i j) (x : F i),
    (trans i j).map ((unit i).hom.app x) = (cocycle i i j).hom.app x
  /-- Compatibility of the cocycle with the unit in the second variable. -/
  cocycle_unit_right : ∀ (i j) (x : F i),
    (unit j).hom.app ((trans i j).obj x) = (cocycle i j j).hom.app x
  /-- **The tetrahedron identity**: the two contractions of a quadruple of charts agree. -/
  tetrahedron : ∀ (i j k l) (x : F i),
    (trans k l).map ((cocycle i j k).hom.app x) ≫ (cocycle i k l).hom.app x =
      (cocycle j k l).hom.app ((trans i j).obj x) ≫ (cocycle i j l).hom.app x

namespace GluingData

variable (G : GluingData F)

/-- The tetrahedron identity read on the inverse isomorphisms.  This is the form in which it
enters the associativity of composition in the glued groupoid. -/
@[reassoc]
theorem tetrahedron_inv (i j k l : ι) (x : F i) :
    (G.cocycle i k l).inv.app x ≫ (G.trans k l).map ((G.cocycle i j k).inv.app x) =
      (G.cocycle i j l).inv.app x ≫ (G.cocycle j k l).inv.app ((G.trans i j).obj x) := by
  refine eq_of_comp_eq_id (u := (G.trans k l).map ((G.cocycle i j k).hom.app x) ≫
    (G.cocycle i k l).hom.app x) ?_ ?_
  · rw [Category.assoc, ← Category.assoc ((G.trans k l).map ((G.cocycle i j k).inv.app x)),
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app]
  · rw [G.tetrahedron i j k l x, Category.assoc,
      ← Category.assoc ((G.cocycle i j l).hom.app x), Iso.hom_inv_id_app, Category.id_comp,
      Iso.hom_inv_id_app]
    rfl

/-- Each transition functor is an equivalence of groupoids: a formal consequence of the unit and
cocycle isomorphisms. -/
def transEquivalence (i j : ι) : F i ≌ F j :=
  CategoryTheory.Equivalence.mk (G.trans i j) (G.trans j i)
    (G.cocycle i j i ≪≫ G.unit i).symm (G.cocycle j i j ≪≫ G.unit j)

end GluingData

/-- **The glued groupoid.**  An object is a point of one of the local groupoids, remembering the
chart in which it is presented. -/
structure Glue (G : GluingData F) where
  /-- The chart in which the object is presented. -/
  chart : ι
  /-- The point of the local groupoid attached to that chart. -/
  pt : F chart

namespace Glue

variable {G : GluingData F}

/-- A morphism of the glued groupoid from `⟨i, x⟩` to `⟨j, y⟩`: a morphism `e_{ij}(x) ⟶ y` of the
local groupoid of the target chart. -/
@[ext]
structure Hom (a b : Glue G) where
  /-- The underlying morphism of the local groupoid of the target chart. -/
  base : (G.trans a.chart b.chart).obj a.pt ⟶ b.pt

namespace Hom

/-- The identity morphism of the glued groupoid: the unit isomorphism of the chart. -/
def id' (a : Glue G) : Hom a a :=
  ⟨(G.unit a.chart).hom.app a.pt⟩

/-- Composition in the glued groupoid, twisted by the cocycle isomorphism. -/
def comp' {a b c : Glue G} (f : Hom a b) (g : Hom b c) : Hom a c :=
  ⟨(G.cocycle a.chart b.chart c.chart).inv.app a.pt ≫
    (G.trans b.chart c.chart).map f.base ≫ g.base⟩

@[simp]
theorem id'_base (a : Glue G) : (id' a).base = (G.unit a.chart).hom.app a.pt :=
  rfl

@[simp]
theorem comp'_base {a b c : Glue G} (f : Hom a b) (g : Hom b c) :
    (comp' f g).base = (G.cocycle a.chart b.chart c.chart).inv.app a.pt ≫
      (G.trans b.chart c.chart).map f.base ≫ g.base :=
  rfl

/-- The unit isomorphism is a left identity for the twisted composition. -/
theorem id'_comp' {a b : Glue G} (f : Hom a b) : comp' (id' a) f = f :=
  Hom.ext (by
    rw [comp'_base, id'_base, G.cocycle_unit_left, Iso.inv_hom_id_app_assoc])

/-- The unit isomorphism is a right identity for the twisted composition. -/
theorem comp'_id' {a b : Glue G} (f : Hom a b) : comp' f (id' b) = f :=
  Hom.ext (by
    rw [comp'_base, id'_base, (G.unit b.chart).hom.naturality f.base, G.cocycle_unit_right,
      Iso.inv_hom_id_app_assoc]
    rfl)

/-- The twisted composition is associative; this is exactly the tetrahedron identity. -/
theorem comp'_assoc {a b c d : Glue G} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
    comp' (comp' f g) h = comp' f (comp' g h) :=
  Hom.ext (by
    simp only [comp'_base, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [NatTrans.naturality_assoc, G.tetrahedron_inv_assoc]
    rfl)

/-- The candidate inverse of a morphism of the glued groupoid. -/
def inv' {a b : Glue G} (f : Hom a b) : Hom b a :=
  ⟨(G.trans b.chart a.chart).map (Groupoid.inv f.base) ≫
    (G.cocycle a.chart b.chart a.chart).hom.app a.pt ≫ (G.unit a.chart).hom.app a.pt⟩

/-- Every morphism of the glued groupoid has a right inverse.  Only the unit axioms are used. -/
theorem comp'_inv' {a b : Glue G} (f : Hom a b) : comp' f (inv' f) = id' a :=
  Hom.ext (by
    rw [comp'_base, id'_base, inv', ← Category.assoc ((G.trans b.chart a.chart).map f.base),
      ← CategoryTheory.Functor.map_comp, Groupoid.comp_inv, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app_assoc])

/-- The candidate inverse is also a left inverse, by the usual cancellation argument. -/
theorem inv'_comp' {a b : Glue G} (f : Hom a b) : comp' (inv' f) f = id' b := by
  have h1 := comp'_inv' f
  have h2 := comp'_inv' (inv' f)
  have h3 : inv' (inv' f) = f := by
    rw [← id'_comp' (inv' (inv' f)), ← h1, comp'_assoc, h2, comp'_id']
  rw [h3] at h2
  exact h2

end Hom

/-- **The glued category.**  A morphism `⟨i, x⟩ ⟶ ⟨j, y⟩` is a morphism `e_{ij}(x) ⟶ y` of the
local groupoid of the second chart; composition is twisted by the cocycle isomorphism and the
identity is the unit isomorphism. -/
instance instCategory : Category.{v} (Glue G) where
  Hom := Hom
  id := Hom.id'
  comp := Hom.comp'
  id_comp := Hom.id'_comp'
  comp_id := Hom.comp'_id'
  assoc := Hom.comp'_assoc

/-- **The glued groupoid.** -/
instance instGroupoid : Groupoid.{v} (Glue G) :=
  { instCategory with
    inv := Hom.inv'
    inv_comp := Hom.inv'_comp'
    comp_inv := Hom.comp'_inv' }

@[simp]
theorem id_base (a : Glue G) : (𝟙 a : a ⟶ a).base = (G.unit a.chart).hom.app a.pt :=
  rfl

@[simp]
theorem comp_base {a b c : Glue G} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).base = (G.cocycle a.chart b.chart c.chart).inv.app a.pt ≫
      (G.trans b.chart c.chart).map f.base ≫ g.base :=
  rfl

/-- **The chart inclusion.**  Every chart maps to the glued groupoid. -/
def inc (G : GluingData F) (i : ι) : F i ⥤ Glue G where
  obj x := ⟨i, x⟩
  map {x _} f := ⟨(G.unit i).hom.app x ≫ f⟩
  map_id x := Hom.ext (by
    change (G.unit i).hom.app x ≫ 𝟙 x = (G.unit i).hom.app x
    exact Category.comp_id _)
  map_comp {x y _} f g := Hom.ext (by
    change (G.unit i).hom.app x ≫ f ≫ g =
      (G.cocycle i i i).inv.app x ≫ (G.trans i i).map ((G.unit i).hom.app x ≫ f) ≫
        ((G.unit i).hom.app y ≫ g)
    rw [CategoryTheory.Functor.map_comp, G.cocycle_unit_left, Category.assoc,
      Iso.inv_hom_id_app_assoc, ← Category.assoc ((G.trans i i).map f),
      (G.unit i).hom.naturality f, Category.assoc]
    rfl)

@[simp]
theorem inc_obj (G : GluingData F) (i : ι) (x : F i) : (inc G i).obj x = ⟨i, x⟩ :=
  rfl

@[simp]
theorem inc_map_base (G : GluingData F) (i : ι) {x y : F i} (f : x ⟶ y) :
    ((inc G i).map f).base = (G.unit i).hom.app x ≫ f :=
  rfl

/-- The chart inclusion is faithful. -/
instance instFaithfulInc (G : GluingData F) (i : ι) : (inc G i).Faithful where
  map_injective {x _} {f g} hfg := by
    have hb : (G.unit i).hom.app x ≫ f = (G.unit i).hom.app x ≫ g := congrArg Hom.base hfg
    exact (cancel_epi ((G.unit i).hom.app x)).1 hb

/-- Every morphism of the glued groupoid between two objects of the same chart comes from that
chart. -/
theorem exists_inc_map (G : GluingData F) (i : ι) {x y : F i}
    (g : Hom (⟨i, x⟩ : Glue G) ⟨i, y⟩) : ∃ f : x ⟶ y, (inc G i).map f = g :=
  ⟨(G.unit i).inv.app x ≫ g.base, Hom.ext (by
    change (G.unit i).hom.app x ≫ (G.unit i).inv.app x ≫ g.base = g.base
    exact Iso.hom_inv_id_app_assoc _ _ _)⟩

/-- The chart inclusion is full. -/
instance instFullInc (G : GluingData F) (i : ι) : (inc G i).Full where
  map_surjective g := exists_inc_map G i g

/-- The chart inclusion is essentially surjective: every point of the glued groupoid is
isomorphic to one presented in the given chart. -/
instance instEssSurjInc (G : GluingData F) (i : ι) : (inc G i).EssSurj where
  mem_essImage b :=
    ⟨(G.trans b.chart i).obj b.pt, ⟨(Groupoid.isoEquivHom _ _).symm
      ⟨(G.cocycle b.chart i b.chart).hom.app b.pt ≫ (G.unit b.chart).hom.app b.pt⟩⟩⟩

/-- **Every chart computes the glued groupoid.**  The chart inclusion is an equivalence of
groupoids. -/
theorem inc_isEquivalence (G : GluingData F) (i : ι) : (inc G i).IsEquivalence where

/-- The equivalence between a chart and the glued groupoid. -/
noncomputable def incEquivalence (G : GluingData F) (i : ι) : F i ≌ Glue G :=
  have := inc_isEquivalence G i
  (inc G i).asEquivalence

/-- The canonical isomorphism comparing the presentations of a point in two charts. -/
def incTransIso (G : GluingData F) (i j : ι) : inc G i ≅ G.trans i j ⋙ inc G j :=
  NatIso.ofComponents
    (fun x ↦ (Groupoid.isoEquivHom (⟨i, x⟩ : Glue G) ⟨j, (G.trans i j).obj x⟩).symm
      ⟨𝟙 ((G.trans i j).obj x)⟩)
    (fun {x y} f ↦ Hom.ext (by
      change (G.cocycle i i j).inv.app x ≫ (G.trans i j).map ((G.unit i).hom.app x ≫ f) ≫
          𝟙 ((G.trans i j).obj y) =
        (G.cocycle i j j).inv.app x ≫ (G.trans j j).map (𝟙 ((G.trans i j).obj x)) ≫
          ((G.unit j).hom.app ((G.trans i j).obj x) ≫ (G.trans i j).map f)
      simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
        G.cocycle_unit_left, G.cocycle_unit_right, Category.comp_id, Iso.inv_hom_id_app_assoc]
      rw [show 𝟙 ((G.trans j j).obj ((G.trans i j).obj x)) ≫ (G.cocycle i j j).hom.app x ≫
            (G.trans i j).map f = (G.cocycle i j j).hom.app x ≫ (G.trans i j).map f from
          Category.id_comp _, Iso.inv_hom_id_app_assoc]))

end Glue

/-! ### Morphisms of gluing data -/

variable {F' : ι → Type u'} [∀ i, Groupoid.{v} (F' i)]

/-- **A morphism of gluing data**, for instance the restriction of the whole local datum along a
map of test objects: a family of functors between the charts, commuting with the transition
functors up to a specified natural isomorphism which is compatible with the units and with the
cocycles.  The cocycle compatibility is stated on the inverse isomorphisms, which is the form in
which it is used. -/
structure GluingHom (G : GluingData F) (G' : GluingData F') where
  /-- The functor on the chart `i`. -/
  map : ∀ i, F i ⥤ F' i
  /-- The comparison isomorphism with the transition functors. -/
  commIso : ∀ i j, map i ⋙ G'.trans i j ≅ G.trans i j ⋙ map j
  /-- Compatibility of the comparison with the units. -/
  commIso_unit : ∀ (i) (x : F i),
    (commIso i i).hom.app x ≫ (map i).map ((G.unit i).hom.app x) =
      (G'.unit i).hom.app ((map i).obj x)
  /-- Compatibility of the comparison with the cocycles. -/
  commIso_cocycle : ∀ (i j k) (x : F i),
    (G'.cocycle i j k).inv.app ((map i).obj x) ≫
        (G'.trans j k).map ((commIso i j).hom.app x) ≫
        (commIso j k).hom.app ((G.trans i j).obj x) =
      (commIso i k).hom.app x ≫ (map k).map ((G.cocycle i j k).inv.app x)

namespace GluingHom

variable {G : GluingData F} {G' : GluingData F'} (α : GluingHom G G')

/-- Naturality of the comparison isomorphism, in beta-reduced form. -/
@[reassoc]
theorem commIso_naturality (i j : ι) {x y : F i} (f : x ⟶ y) :
    (G'.trans i j).map ((α.map i).map f) ≫ (α.commIso i j).hom.app y =
      (α.commIso i j).hom.app x ≫ (α.map j).map ((G.trans i j).map f) :=
  (α.commIso i j).hom.naturality f

/-- The cocycle compatibility, in beta-reduced form. -/
@[reassoc]
theorem commIso_cocycle' (i j k : ι) (x : F i) :
    (G'.cocycle i j k).inv.app ((α.map i).obj x) ≫
        (G'.trans j k).map ((α.commIso i j).hom.app x) ≫
        (α.commIso j k).hom.app ((G.trans i j).obj x) =
      (α.commIso i k).hom.app x ≫ (α.map k).map ((G.cocycle i j k).inv.app x) :=
  α.commIso_cocycle i j k x

/-- **The glued functor** induced by a morphism of gluing data. -/
def glue : Glue G ⥤ Glue G' where
  obj a := ⟨a.chart, (α.map a.chart).obj a.pt⟩
  map {a b} f := ⟨(α.commIso a.chart b.chart).hom.app a.pt ≫ (α.map b.chart).map f.base⟩
  map_id a := Glue.Hom.ext (α.commIso_unit a.chart a.pt)
  map_comp {a b c} f g := Glue.Hom.ext (by
    simp only [Glue.comp_base, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [α.commIso_naturality_assoc, α.commIso_cocycle'_assoc])

@[simp]
theorem glue_obj (a : Glue G) : α.glue.obj a = ⟨a.chart, (α.map a.chart).obj a.pt⟩ :=
  rfl

@[simp]
theorem glue_map_base {a b : Glue G} (f : a ⟶ b) :
    (α.glue.map f).base =
      (α.commIso a.chart b.chart).hom.app a.pt ≫ (α.map b.chart).map f.base :=
  rfl

/-- The glued functor is compatible with the chart inclusions. -/
def incGlueIso (i : ι) : Glue.inc G i ⋙ α.glue ≅ α.map i ⋙ Glue.inc G' i :=
  NatIso.ofComponents (fun x ↦ CategoryTheory.Iso.refl (⟨i, (α.map i).obj x⟩ : Glue G'))
    (fun {x _} f ↦ by
      refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
      refine Glue.Hom.ext ?_
      change (α.commIso i i).hom.app x ≫ (α.map i).map ((G.unit i).hom.app x ≫ f) =
        (G'.unit i).hom.app ((α.map i).obj x) ≫ (α.map i).map f
      rw [CategoryTheory.Functor.map_comp, ← Category.assoc, α.commIso_unit])

end GluingHom

end GroupoidGluing

end GromovWitten.AlgebraicGeometry
