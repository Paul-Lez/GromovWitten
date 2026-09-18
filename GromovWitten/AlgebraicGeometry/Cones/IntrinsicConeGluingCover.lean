/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.IntrinsicConeGluingPoly
import GromovWitten.AlgebraicGeometry.Cones.SmoothAmbient
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Functoriality of the glued intrinsic cone, and gluing over a cover of flat charts

This file closes two gaps left open by `Cones/IntrinsicConeGluing.lean`,
`Cones/IntrinsicConeGluingPoly.lean` and `Cones/SmoothAmbient.lean`.

## Composition of morphisms of gluing data

`GroupoidGluing.GluingHom.id` and `GroupoidGluing.GluingHom.comp` make morphisms of gluing data
into a (strict) category, and `GluingHom.glue_id`, `GluingHom.glue_comp` say that the induced
functor between the glued groupoids is *strictly* functorial: `(α.comp β).glue = α.glue ⋙
β.glue` and `(GluingHom.id G).glue = 𝟭`.  For the polynomial model of
`Cones/IntrinsicConeGluingPoly.lean` the restriction morphisms compose strictly as well
(`PresentationFamily.restrictHom_id`, `PresentationFamily.restrictHom_comp`), so the glued
groupoid of `B`-points is an honest functor

* `PresentationFamily.intrinsicConeFunctor : CommRingCat ⥤ Cat`

on test algebras — a pseudofunctor which happens to be strict, not merely a family of
restriction functors.

## Gluing over a cover by flat charts

`Cones/SmoothAmbient.lean` provides, for a flat algebra `R` over the ambient polynomial ring `P`
and an `R`-algebra `B`, the bijection `ConeLocalisation.pointEquiv` between the `R`-algebra
points of `gr_{I·R}(R)` and the `P`-algebra points of `gr_I(P)`, compatible with the translation
action (`ConeLocalisation.locTranslatePoint_iff`).  Given a whole family `R j` of such charts —
for instance the localisations `P_{f_j}` of a basic open cover, which are flat by
`ConeLocalisation.flat_of_isLocalizationAway` — and a test algebra `B` which is an algebra over
each of them, transporting points through `pointEquiv` gives explicit transition functors

* `ConeCover.transFunctor j k : LocConeGroupoid (R j) I B ⥤ LocConeGroupoid (R k) I B`

whose unit and cocycle isomorphisms are the identifications of objects
`ConeCover.isoOfPointEq` (`ConeCover.unitIso`, `ConeCover.cocycleFunctorIso`).  All arrows of
these groupoids are translations by tangent vectors and the identifications translate by `0`, so
the two unit coherences and the tetrahedron identity are theorems
(`ConeCover.transFunctor_map_unit`, `ConeCover.unit_transFunctor`,
`ConeCover.tetrahedron_aux`).  Hence

* `ConeCover.gluingData : GluingData (fun j ↦ LocConeGroupoid (R j) I B)`

is unconditional, `ConeCover.intrinsicConeCover B` is the glued groupoid of the cover, every
chart computes it (`ConeCover.chartEquivalence`), and the glued groupoid is equivalent to the
`P`-algebra points of the polynomial model (`ConeCover.algEquivalence`): passing to any cover by
flat — in particular open — charts does not change `[C/T](B)`.

Finally `ConeCover.flat_awayChart`, `ConeCover.awayChartHom` and
`ConeCover.exists_algebra_of_isUnit` produce the hypotheses of the above for a basic open chart
`D(f)`: the localisation `P_f` is flat over `P`, and a test algebra in which the image of `f` is
a unit is canonically an algebra over `P_f`, compatibly with `P`.

## What is not here

The test algebras are always algebras over *all* the charts of the cover (that is the index set
of the gluing datum is the set of charts on which the test point lives).  Descending along a
Zariski cover of the test algebra itself — objects over the `B_{f_j}` glued by a cocycle over
the `B_{f_j f_k}` — is not formalised.
-/

namespace GromovWitten.AlgebraicGeometry

namespace GroupoidGluing

open CategoryTheory

universe v u u' u'' w

variable {ι : Type w} {F : ι → Type u} [∀ i, Groupoid.{v} (F i)]
  {F' : ι → Type u'} [∀ i, Groupoid.{v} (F' i)]
  {F'' : ι → Type u''} [∀ i, Groupoid.{v} (F'' i)]

namespace GluingHom

/-- Two morphisms of gluing data with the same chart functors and the same comparison
isomorphism are equal; the two remaining fields are propositions. -/
theorem ext_of_commIso {G : GluingData F} {G' : GluingData F'} {α β : GluingHom G G'}
    (hmap : α.map = β.map) (hcomm : HEq α.commIso β.commIso) : α = β := by
  revert hmap hcomm
  obtain ⟨m, c, hu, hc⟩ := α
  obtain ⟨m', c', hu', hc'⟩ := β
  intro hmap hcomm
  cases hmap
  cases hcomm
  rfl

/-- **The identity morphism of gluing data.** -/
def id (G : GluingData F) : GluingHom G G where
  map i := 𝟭 (F i)
  commIso i j := NatIso.ofComponents (fun x ↦ Iso.refl ((G.trans i j).obj x))
    (fun {_ _} _ ↦ (Category.comp_id _).trans (Eq.trans rfl (Category.id_comp _).symm))
  commIso_unit _ _ := Category.id_comp _
  commIso_cocycle i j k x := by
    change (G.cocycle i j k).inv.app x ≫ (G.trans j k).map (𝟙 ((G.trans i j).obj x)) ≫
      𝟙 ((G.trans j k).obj ((G.trans i j).obj x)) = 𝟙 _ ≫ (G.cocycle i j k).inv.app x
    simp

/-- **Composition of morphisms of gluing data**: the chart functors are composed and the
comparison isomorphism is the pasting of the two given ones.  The unit compatibility and the
cocycle compatibility are proved from those of the factors, the latter using the naturality of
the comparison isomorphism of the second factor. -/
def comp {G : GluingData F} {G' : GluingData F'} {G'' : GluingData F''} (α : GluingHom G G')
    (β : GluingHom G' G'') : GluingHom G G'' where
  map i := α.map i ⋙ β.map i
  commIso i j := NatIso.ofComponents
    (fun x ↦ (β.commIso i j).app ((α.map i).obj x) ≪≫
      (β.map j).mapIso ((α.commIso i j).app x))
    (fun {x y} f ↦ by
      change (G''.trans i j).map ((β.map i).map ((α.map i).map f)) ≫
          ((β.commIso i j).hom.app ((α.map i).obj y) ≫
            (β.map j).map ((α.commIso i j).hom.app y)) =
        ((β.commIso i j).hom.app ((α.map i).obj x) ≫
            (β.map j).map ((α.commIso i j).hom.app x)) ≫
          (β.map j).map ((α.map j).map ((G.trans i j).map f))
      rw [← Category.assoc, β.commIso_naturality, Category.assoc, Category.assoc,
        ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        α.commIso_naturality])
  commIso_unit i x := by
    change ((β.commIso i i).hom.app ((α.map i).obj x) ≫
        (β.map i).map ((α.commIso i i).hom.app x)) ≫
        (β.map i).map ((α.map i).map ((G.unit i).hom.app x)) =
      (G''.unit i).hom.app ((β.map i).obj ((α.map i).obj x))
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, α.commIso_unit, β.commIso_unit]
  commIso_cocycle i j k x := by
    have hnat : ∀ {W : F'' k}
        (h : (β.map k).obj ((G'.trans j k).obj ((α.map j).obj ((G.trans i j).obj x))) ⟶ W),
        (G''.trans j k).map ((β.map j).map ((α.commIso i j).hom.app x)) ≫
          (β.commIso j k).hom.app ((α.map j).obj ((G.trans i j).obj x)) ≫ h =
        (β.commIso j k).hom.app ((G'.trans i j).obj ((α.map i).obj x)) ≫
          (β.map k).map ((G'.trans j k).map ((α.commIso i j).hom.app x)) ≫ h :=
      fun h ↦ β.commIso_naturality_assoc j k ((α.commIso i j).hom.app x) h
    have hbeta : ∀ {W : F'' k}
        (h : (β.map k).obj ((G'.trans j k).obj ((G'.trans i j).obj ((α.map i).obj x))) ⟶ W),
        (G''.cocycle i j k).inv.app ((β.map i).obj ((α.map i).obj x)) ≫
          (G''.trans j k).map ((β.commIso i j).hom.app ((α.map i).obj x)) ≫
          (β.commIso j k).hom.app ((G'.trans i j).obj ((α.map i).obj x)) ≫ h =
        (β.commIso i k).hom.app ((α.map i).obj x) ≫
          (β.map k).map ((G'.cocycle i j k).inv.app ((α.map i).obj x)) ≫ h :=
      fun h ↦ β.commIso_cocycle'_assoc i j k ((α.map i).obj x) h
    have halpha : (G'.cocycle i j k).inv.app ((α.map i).obj x) ≫
        (G'.trans j k).map ((α.commIso i j).hom.app x) ≫
        (α.commIso j k).hom.app ((G.trans i j).obj x) =
      (α.commIso i k).hom.app x ≫ (α.map k).map ((G.cocycle i j k).inv.app x) :=
      α.commIso_cocycle' i j k x
    change (G''.cocycle i j k).inv.app ((β.map i).obj ((α.map i).obj x)) ≫
        (G''.trans j k).map ((β.commIso i j).hom.app ((α.map i).obj x) ≫
          (β.map j).map ((α.commIso i j).hom.app x)) ≫
        ((β.commIso j k).hom.app ((α.map j).obj ((G.trans i j).obj x)) ≫
          (β.map k).map ((α.commIso j k).hom.app ((G.trans i j).obj x))) =
      ((β.commIso i k).hom.app ((α.map i).obj x) ≫
          (β.map k).map ((α.commIso i k).hom.app x)) ≫
        (β.map k).map ((α.map k).map ((G.cocycle i j k).inv.app x))
    rw [CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, hnat,
      ← CategoryTheory.Functor.map_comp, hbeta, ← CategoryTheory.Functor.map_comp, halpha,
      CategoryTheory.Functor.map_comp]

/-- The comparison isomorphism of a composite, componentwise. -/
theorem comp_commIso_hom_app {G : GluingData F} {G' : GluingData F'} {G'' : GluingData F''}
    (α : GluingHom G G') (β : GluingHom G' G'') (i j : ι) (x : F i) :
    ((α.comp β).commIso i j).hom.app x =
      (β.commIso i j).hom.app ((α.map i).obj x) ≫
        (β.map j).map ((α.commIso i j).hom.app x) :=
  rfl

/-- The chart functors of a composite are the composites of the chart functors. -/
theorem comp_map {G : GluingData F} {G' : GluingData F'} {G'' : GluingData F''}
    (α : GluingHom G G') (β : GluingHom G' G'') (i : ι) :
    (α.comp β).map i = α.map i ⋙ β.map i :=
  rfl

/-- **The glued functor of the identity is the identity.** -/
theorem glue_id (G : GluingData F) : (GluingHom.id G).glue = 𝟭 (Glue G) := by
  refine CategoryTheory.Functor.ext (fun a ↦ rfl) fun a b f ↦ ?_
  change (GluingHom.id G).glue.map f = 𝟙 _ ≫ (𝟭 (Glue G)).map f ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  exact Glue.Hom.ext (Category.id_comp _)

/-- **The glued functor of a composite is the composite of the glued functors**: gluing is a
strict functor on morphisms of gluing data. -/
theorem glue_comp {G : GluingData F} {G' : GluingData F'} {G'' : GluingData F''}
    (α : GluingHom G G') (β : GluingHom G' G'') :
    (α.comp β).glue = α.glue ⋙ β.glue := by
  refine CategoryTheory.Functor.ext (fun a ↦ rfl) fun a b f ↦ ?_
  change (α.comp β).glue.map f = 𝟙 _ ≫ (α.glue ⋙ β.glue).map f ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  refine Glue.Hom.ext ?_
  change ((α.comp β).commIso a.chart b.chart).hom.app a.pt ≫
      (β.map b.chart).map ((α.map b.chart).map f.base) =
    (β.commIso a.chart b.chart).hom.app ((α.map a.chart).obj a.pt) ≫
      (β.map b.chart).map ((α.commIso a.chart b.chart).hom.app a.pt ≫
        (α.map b.chart).map f.base)
  rw [comp_commIso_hom_app, CategoryTheory.Functor.map_comp]
  exact Category.assoc _ _ _

end GluingHom

end GroupoidGluing

/-! ### Functoriality of the glued intrinsic cone in the test algebra -/

namespace IntrinsicConeGluing

namespace PresentationFamily

open CategoryTheory GroupoidGluing ConeRefinement

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S] {ι : Type u}
  (P : PresentationFamily A S ι) (B : Type u) [CommRing B]

/-- **Restriction along the identity is the identity morphism of gluing data.** -/
theorem restrictHom_id : P.restrictHom B (RingHom.id B) = GluingHom.id (P.gluingData B) :=
  rfl

variable {B}

/-- **Restriction is functorial in the test algebra**: restricting along `g ∘ f` is restricting
along `f` and then along `g`. -/
theorem restrictHom_comp {B' B'' : Type u} [CommRing B'] [CommRing B''] (f : B →+* B')
    (g : B' →+* B'') :
    P.restrictHom B (g.comp f) = (P.restrictHom B f).comp (P.restrictHom B' g) := by
  refine GluingHom.ext_of_commIso rfl (heq_of_eq (funext fun i ↦ funext fun j ↦ ?_))
  refine Iso.ext (NatTrans.ext (funext fun x ↦ ?_))
  refine ConeGroupoid.Hom.ext (funext fun t ↦ ?_)
  change (0 : B'') = 0 + g 0
  rw [map_zero, add_zero]

/-- **The glued intrinsic cone as a functor on test algebras.**  A test algebra is sent to the
groupoid of its points of the intrinsic normal cone, glued from all the presentations of the
family, and a ring map to the restriction of points; by `restrictHom_id`, `restrictHom_comp` and
`GluingHom.glue_id`, `GluingHom.glue_comp` this is a *strict* functor. -/
noncomputable def intrinsicConeFunctor : CommRingCat.{u} ⥤ Cat.{u, u} where
  obj B := Cat.of (P.intrinsicCone B)
  map f := (P.restrictHom _ f.hom).glue.toCatHom
  map_id B := Cat.Hom.ext (by
    rw [Cat.Hom.id_toFunctor]
    change (P.restrictHom B (RingHom.id B)).glue = 𝟭 (P.intrinsicCone B)
    rw [P.restrictHom_id B]
    exact GluingHom.glue_id _)
  map_comp f g := Cat.Hom.ext (by
    change (P.restrictHom _ (g.hom.comp f.hom)).glue =
      (P.restrictHom _ f.hom).glue ⋙ (P.restrictHom _ g.hom).glue
    rw [P.restrictHom_comp f.hom g.hom, GluingHom.glue_comp])

end PresentationFamily

end IntrinsicConeGluing


/-! ### Gluing over a cover by flat charts -/

namespace ConeCover

open CategoryTheory ConeTranslation ConeLocalisation GroupoidGluing

noncomputable section

variable {A : Type u} [CommRing A] {σ : Type u} (I : Ideal (Amb A σ)) {ι : Type u}
  (R : ι → Type u) [∀ j, CommRing (R j)] [∀ j, Algebra (Amb A σ) (R j)]
  [∀ j, Module.Flat (Amb A σ) (R j)] (B : Type u) [CommRing B] [Algebra (Amb A σ) B]
  [∀ j, Algebra (R j) B] [∀ j, IsScalarTower (Amb A σ) (R j) B]

/-- The groupoid of `B`-points of the quotient stack computed in the `j`-th chart of the cover,
`[C_{U/M_j} / T_{M_j}|_U](B)` for the flat ambient extension `M_j = Spec (R j)`. -/
abbrev chart (j : ι) : Type u := LocConeGroupoid (R j) I B

/-- **Transport of a point from one chart of the cover to another**: the charts all have the
same `P`-algebra points of `gr_I(P)` by `ConeLocalisation.pointEquiv`, and a point of the chart
`j` is sent to the point of the chart `k` with the same restriction to `gr_I(P)`. -/
def transPoint (j k : ι) (φ : GrLoc (R j) I →ₐ[R j] B) : GrLoc (R k) I →ₐ[R k] B :=
  (pointEquiv (R k) I B).symm (pointEquiv (R j) I B φ)

/-- Transport does not change the underlying `P`-algebra point. -/
theorem pointEquiv_transPoint (j k : ι) (φ : GrLoc (R j) I →ₐ[R j] B) :
    pointEquiv (R k) I B (transPoint I R B j k φ) = pointEquiv (R j) I B φ :=
  Equiv.apply_symm_apply _ _

/-- Transport from a chart to itself is the identity. -/
theorem transPoint_self (j : ι) (φ : GrLoc (R j) I →ₐ[R j] B) :
    transPoint I R B j j φ = φ :=
  Equiv.symm_apply_apply _ _

/-- Transport is transitive. -/
theorem transPoint_trans (j k l : ι) (φ : GrLoc (R j) I →ₐ[R j] B) :
    transPoint I R B k l (transPoint I R B j k φ) = transPoint I R B j l φ :=
  congrArg (pointEquiv (R l) I B).symm (pointEquiv_transPoint I R B j k φ)

/-- **The transition functor of the cover**: transport of points, keeping the translating
tangent vector, which is legitimate by `ConeLocalisation.locTranslatePoint_iff`. -/
def transFunctor (j k : ι) : chart I R B j ⥤ chart I R B k where
  obj x := ⟨transPoint I R B j k x.point⟩
  map {_ _} f := ⟨f.val, by
    refine (locTranslatePoint_iff (R k) I _ _ f.val).mpr ?_
    rw [pointEquiv_transPoint, pointEquiv_transPoint]
    exact (locTranslatePoint_iff (R j) I _ _ f.val).mp f.translate_eq⟩
  map_id _ := LocConeGroupoid.Hom.ext rfl
  map_comp _ _ := LocConeGroupoid.Hom.ext rfl

/-- The point of the transported object. -/
theorem transFunctor_obj_point (j k : ι) (x : chart I R B j) :
    ((transFunctor I R B j k).obj x).point = transPoint I R B j k x.point :=
  rfl

/-- The transition functors do not change the translating tangent vector. -/
theorem transFunctor_map_val (j k : ι) {x y : chart I R B j} (f : x ⟶ y) :
    ((transFunctor I R B j k).map f).val = f.val :=
  rfl

/-- **An identification of two points of a chart is an arrow translating by `0`.** -/
def homOfPointEq {j : ι} {x y : chart I R B j} (h : x.point = y.point) : x ⟶ y :=
  ⟨0, (locTranslatePoint_zero _).trans (congrArg AlgHom.toRingHom h)⟩

omit [Algebra (Amb A σ) B] [∀ j, IsScalarTower (Amb A σ) (R j) B] in
/-- The identifying arrow translates by the zero tangent vector. -/
theorem homOfPointEq_val {j : ι} {x y : chart I R B j} (h : x.point = y.point) :
    (homOfPointEq I R B h).val = 0 :=
  rfl

/-- **An identification of two points of a chart is an isomorphism.** -/
def isoOfPointEq {j : ι} {x y : chart I R B j} (h : x.point = y.point) : x ≅ y where
  hom := homOfPointEq I R B h
  inv := homOfPointEq I R B h.symm
  hom_inv_id := LocConeGroupoid.Hom.ext (add_zero 0)
  inv_hom_id := LocConeGroupoid.Hom.ext (add_zero 0)

omit [Algebra (Amb A σ) B] [∀ j, IsScalarTower (Amb A σ) (R j) B] in
/-- **Naturality is automatic for identifications of objects**: any two functors between chart
groupoids which keep the translating tangent vector commute with any family of arrows
translating by `0`, because composition adds tangent vectors. -/
theorem naturality_of_val {j k : ι} (F G : chart I R B j ⥤ chart I R B k)
    (hF : ∀ {x y : chart I R B j} (f : x ⟶ y), (F.map f).val = f.val)
    (hG : ∀ {x y : chart I R B j} (f : x ⟶ y), (G.map f).val = f.val)
    (e : ∀ x, F.obj x ⟶ G.obj x) (he : ∀ x, (e x).val = 0)
    {x y : chart I R B j} (f : x ⟶ y) :
    F.map f ≫ e y = e x ≫ G.map f :=
  LocConeGroupoid.Hom.ext (by
    rw [LocConeGroupoid.comp_val, LocConeGroupoid.comp_val, he, he, add_zero, zero_add, hF, hG])

/-- **The unit isomorphism**: the transition functor of a chart with itself is the identity. -/
def unitIso (j : ι) : transFunctor I R B j j ≅ 𝟭 (chart I R B j) :=
  NatIso.ofComponents
    (fun x ↦ isoOfPointEq I R B (transPoint_self I R B j x.point))
    (fun {_ _} f ↦ naturality_of_val I R B (transFunctor I R B j j) (𝟭 (chart I R B j))
      (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun x ↦ homOfPointEq I R B (transPoint_self I R B j x.point)) (fun _ ↦ rfl) f)

/-- The unit isomorphism translates by the zero tangent vector. -/
theorem unitIso_hom_app_val (j : ι) (x : chart I R B j) :
    ((unitIso I R B j).hom.app x).val = 0 :=
  rfl

/-- **The cocycle isomorphism**: transporting from the chart `j` to the chart `k` and then to
the chart `l` is transporting from `j` to `l`. -/
def cocycleFunctorIso (j k l : ι) :
    transFunctor I R B j k ⋙ transFunctor I R B k l ≅ transFunctor I R B j l :=
  NatIso.ofComponents
    (fun x ↦ isoOfPointEq I R B (transPoint_trans I R B j k l x.point))
    (fun {_ _} f ↦ naturality_of_val I R B
      (transFunctor I R B j k ⋙ transFunctor I R B k l) (transFunctor I R B j l)
      (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun x ↦ homOfPointEq I R B (transPoint_trans I R B j k l x.point)) (fun _ ↦ rfl) f)

/-- The cocycle isomorphism translates by the zero tangent vector. -/
theorem cocycleFunctorIso_hom_app_val (j k l : ι) (x : chart I R B j) :
    ((cocycleFunctorIso I R B j k l).hom.app x).val = 0 :=
  rfl

/-- The first unit coherence of the gluing datum of the cover. -/
theorem transFunctor_map_unit (j k : ι) (x : chart I R B j) :
    (transFunctor I R B j k).map ((unitIso I R B j).hom.app x) =
      (cocycleFunctorIso I R B j j k).hom.app x :=
  LocConeGroupoid.Hom.ext (by
    rw [transFunctor_map_val, unitIso_hom_app_val, cocycleFunctorIso_hom_app_val])

/-- The second unit coherence of the gluing datum of the cover. -/
theorem unit_transFunctor (j k : ι) (x : chart I R B j) :
    (unitIso I R B k).hom.app ((transFunctor I R B j k).obj x) =
      (cocycleFunctorIso I R B j k k).hom.app x :=
  LocConeGroupoid.Hom.ext (by
    rw [unitIso_hom_app_val, cocycleFunctorIso_hom_app_val])

/-- **The tetrahedron identity** for the cover: both contractions of a quadruple of charts are
the identification of the transported points. -/
theorem tetrahedron_aux (j k l m : ι) (x : chart I R B j) :
    (transFunctor I R B l m).map ((cocycleFunctorIso I R B j k l).hom.app x) ≫
        (cocycleFunctorIso I R B j l m).hom.app x =
      (cocycleFunctorIso I R B k l m).hom.app ((transFunctor I R B j k).obj x) ≫
        (cocycleFunctorIso I R B j k m).hom.app x :=
  LocConeGroupoid.Hom.ext (by
    rw [LocConeGroupoid.comp_val, LocConeGroupoid.comp_val, transFunctor_map_val,
      cocycleFunctorIso_hom_app_val, cocycleFunctorIso_hom_app_val,
      cocycleFunctorIso_hom_app_val, cocycleFunctorIso_hom_app_val])

/-- **The gluing datum of a cover by flat charts.**  All coherences are theorems. -/
def gluingData : GluingData (chart I R B) where
  trans := transFunctor I R B
  unit := unitIso I R B
  cocycle := cocycleFunctorIso I R B
  cocycle_unit_left := transFunctor_map_unit I R B
  cocycle_unit_right := unit_transFunctor I R B
  tetrahedron := tetrahedron_aux I R B

/-- **The glued groupoid of the cover**: the `B`-points of the intrinsic quotient stack, glued
from all the flat charts of the cover at once. -/
abbrev intrinsicConeCover : Type u := Glue (gluingData I R B)

/-- **Every chart of the cover computes the glued groupoid.** -/
theorem inc_isEquivalence (j : ι) : (Glue.inc (gluingData I R B) j).IsEquivalence :=
  Glue.inc_isEquivalence _ j

/-- The equivalence between the quotient groupoid of one chart of the cover and the glued
groupoid of the cover. -/
def chartEquivalence (j : ι) : chart I R B j ≌ intrinsicConeCover I R B :=
  Glue.incEquivalence (gluingData I R B) j

/-- The transition functor between two charts of the cover is an equivalence. -/
def transEquivalence (j k : ι) : chart I R B j ≌ chart I R B k :=
  (gluingData I R B).transEquivalence j k

/-- **The glued groupoid of the cover is the groupoid of `P`-algebra points of the polynomial
model**: covering `Spec P` by flat — in particular open — charts does not change `[C/T](B)`. -/
def algEquivalence (j : ι) : intrinsicConeCover I R B ≌ AlgConeGroupoid I B :=
  (chartEquivalence I R B j).symm.trans (locConeEquivalence (R j) I B)

/-- **An identification of two `P`-algebra points is an arrow translating by `0`.** -/
def algHomOfPointEq {x y : AlgConeGroupoid I B} (h : x.point = y.point) : x ⟶ y :=
  ⟨0, (translatePoint_zero I _).trans (congrArg AlgHom.toRingHom h)⟩

/-- **An identification of two `P`-algebra points is an isomorphism.** -/
def algIsoOfPointEq {x y : AlgConeGroupoid I B} (h : x.point = y.point) : x ≅ y where
  hom := algHomOfPointEq I B h
  inv := algHomOfPointEq I B h.symm
  hom_inv_id := AlgConeGroupoid.Hom.ext (add_zero 0)
  inv_hom_id := AlgConeGroupoid.Hom.ext (add_zero 0)

omit [∀ j, IsScalarTower (Amb A σ) (R j) B] in
/-- Naturality is automatic for identifications of `P`-algebra points, for the same reason as
`naturality_of_val`. -/
theorem naturality_of_val_alg {j : ι} (F G : chart I R B j ⥤ AlgConeGroupoid I B)
    (hF : ∀ {x y : chart I R B j} (f : x ⟶ y), (F.map f).val = f.val)
    (hG : ∀ {x y : chart I R B j} (f : x ⟶ y), (G.map f).val = f.val)
    (e : ∀ x, F.obj x ⟶ G.obj x) (he : ∀ x, (e x).val = 0)
    {x y : chart I R B j} (f : x ⟶ y) :
    F.map f ≫ e y = e x ≫ G.map f :=
  AlgConeGroupoid.Hom.ext (by
    rw [AlgConeGroupoid.comp_val, AlgConeGroupoid.comp_val, he, he, add_zero, zero_add, hF, hG])

/-- **The transition functors are compatible with the comparison of each chart with the
polynomial model**: transporting a point does not change the underlying `P`-algebra point. -/
def transCompareIso (j k : ι) :
    transFunctor I R B j k ⋙ locConeFunctor (R k) I B ≅ locConeFunctor (R j) I B :=
  NatIso.ofComponents
    (fun x ↦ algIsoOfPointEq I B (pointEquiv_transPoint I R B j k x.point))
    (fun {_ _} f ↦ naturality_of_val_alg I R B
      (transFunctor I R B j k ⋙ locConeFunctor (R k) I B) (locConeFunctor (R j) I B)
      (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun x ↦ algHomOfPointEq I B (pointEquiv_transPoint I R B j k x.point)) (fun _ ↦ rfl) f)

end

/-! ### Basic open charts -/

section Away

variable {A : Type u} [CommRing A] {σ : Type u} (R : Type u) [CommRing R]
  [Algebra (Amb A σ) R] (B : Type u) [CommRing B] [Algebra (Amb A σ) B] (f : Amb A σ)

/-- **A basic open chart is a flat chart**: the localisation `P_f` is flat over `P`. -/
theorem flat_awayChart [IsLocalization.Away f R] : Module.Flat (Amb A σ) R :=
  flat_of_isLocalizationAway R f

/-- **A test algebra in which `f` becomes invertible is canonically a `P_f`-algebra**: the
structure map is the localisation lift of the structure map of `B`, and it is a map of
`P`-algebras, so the scalar tower condition holds automatically. -/
noncomputable def awayChartHom [IsLocalization.Away f R]
    (hf : IsUnit (algebraMap (Amb A σ) B f)) : R →ₐ[Amb A σ] B :=
  IsLocalization.Away.liftAlgHom (A := Amb A σ) (f := Algebra.ofId (Amb A σ) B) f hf

/-- The structure map of the basic open chart restricts to the structure map of `B`. -/
theorem awayChartHom_algebraMap [IsLocalization.Away f R]
    (hf : IsUnit (algebraMap (Amb A σ) B f)) (r : Amb A σ) :
    awayChartHom R B f hf (algebraMap (Amb A σ) R r) = algebraMap (Amb A σ) B r :=
  (awayChartHom R B f hf).commutes r

/-- **The hypotheses of the gluing datum are satisfied by a basic open chart on which the test
algebra lives**: if the image of `f` in `B` is a unit then `B` carries an algebra structure over
the localisation `P_f` whose structure map is compatible with the one of `B`, that is, which
makes `P → P_f → B` a scalar tower. -/
theorem exists_algebra_of_isUnit [IsLocalization.Away f R]
    (hf : IsUnit (algebraMap (Amb A σ) B f)) :
    ∃ alg : Algebra R B, ∀ r : Amb A σ,
      @algebraMap R B _ _ alg (algebraMap (Amb A σ) R r) = algebraMap (Amb A σ) B r :=
  ⟨(awayChartHom R B f hf).toAlgebra, awayChartHom_algebraMap R B f hf⟩

end Away

end ConeCover

end GromovWitten.AlgebraicGeometry
