/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.StackCoherence

/-!
# Coherence and the universal property of fibre products of cone stacks

`Cones/StackFibreProducts.lean` builds the fibre product `ConeStack.prod C D hp` of two cone
stacks over a common base on the genuine two-pullback of their projections, and
`Cones/StackCoherence.lean` proves that a pair of coherent cone stacks satisfies the coherence
hypothesis `ProdCoherence`, so that `ConeStack.prodOfCoherent` is unconditional.  What was left
open there is whether the fibre product is itself coherent — without that, iterated fibre
products would again need hypotheses.  This file closes that gap and records the universal
property of the fibre product on fibres.

## Main results

* `ConeStack.isCoherent_prod`: if `C` is coherent then so is `ConeStack.prod C D hp`, for any
  proof `hp` of `ProdCoherence C D` and **any** second factor `D`.  Only the coherence of the
  first factor is needed, because the projection of the fibre product to the base is taken
  through the first factor.  Consequently `ConeStack.isCoherent_prodOfCoherent` shows that
  `ConeStack.prodOfCoherent` of two coherent cone stacks is coherent, so iterated fibre products
  (and mixed iterated fibre products and base changes, via
  `ConeStack.isCoherent_baseChangeOfCoherent`) are unconditional.
* `ConeStack.prodFiberOverEquiv`: for a test scheme `T` and a base object `b`, the fibre
  `(ConeStack.prod C D hp).FiberOver T b` is equivalent to the product of the fibres
  `C.FiberOver T b × D.FiberOver T b`.  This is the universal property of the fibre product at
  the level of fibres; the equivalence is built from the two-pullback description of the points
  of `prodTotal C D` and is compatible with the two projections `prodHomFst` and `prodHomSnd`
  (`ConeStack.prodFiberOverFunctor_obj_fst_object`,
  `ConeStack.prodFiberOverFunctor_obj_snd_object`).
* `ConeStack.prodHomFst_equivariant_eq`, `ConeStack.prodHomSnd_equivariant_eq`: both projections
  of the fibre product are *strictly* equivariant for the contractions, and
  `ConeStack.prodHomFst_overBase_appIso_hom_app`,
  `ConeStack.prodHomSnd_overBase_appIso_hom_app` compute their comparisons with the base.
* `ConeStack.baseChangeIdEquivalence`: base change along the identity of the base does not
  change the total stack, as a `StackEquivalenceData`, and the equivalence is compatible with
  the two projections of the base change (`ConeStack.baseChangeIdProjectionIso`,
  `ConeStack.baseChangeIdFstIso`).  This is the unit half of the pseudofunctoriality of base
  change.

## Infrastructure

The two component computations `ConeStack.prod_vertexProjectionIso_hom_app` and
`ConeStack.prod_projectionNaturality_hom_app` identify the section comparison of the vertex of
the fibre product and the strong-naturality cell of its projection with those of the first
factor; they are what makes the zero law and the reindexing law of `IsCoherent (prod C D hp)`
reduce to the corresponding laws of `C`.  As in `Cones/StackCoherence.lean`, the fibres of a
two-pullback stack are only definitionally the categorical pullbacks, so `simp` and `rw` are
unusable on most of these goals; the small abstract lemmas `ConeStack.mapId_comp`,
`ConeStack.prodFiberOver_snd_comm`, `ConeStack.prodFiberOver_w`,
`ConeStack.prodFiberOver_unit_w`, `ConeStack.prodFiberOver_eqId_comp` and
`ConeStack.prodFiberOver_counit_comm` are stated in an arbitrary category so that they apply
through definitional unfolding.  `ConeStack.FiberOver.isoMk` builds an isomorphism in a fibre
over a base object from an isomorphism of the underlying objects.

## What is not done

No coherence theorem asserting that *all* diagrams of a coherent cone stack commute is
attempted.  The composition half of the pseudofunctoriality of base change — comparing
`baseChange C (Pseudofunctor.StrongTrans.vcomp f g)` with `baseChange (baseChange C g hc) f` —
is *not* constructed: it needs the pasting law identifying an iterated genuine two-pullback
with a genuine two-pullback of the composite cospan, which the repository does not yet have
(`Stacks/StackProducts.lean` proves the pasting law only for representable properties, not as
a bilimit).  Only the identity half, `ConeStack.baseChangeIdEquivalence`, is proved here, and
only at the level of total stacks: the equivalence is not upgraded to a `ConeStack.Iso`, since
`ConeStack.Hom` also requires the vertex and equivariance cells.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

namespace ConeStack

variable {base : FppfStack.{u}} {O : FppfScalarRings.{u}}

/-! ### Component computations for the fibre product -/

/-- Composing with the image of an identity arrow, in any category.  It is stated abstractly so
that it can be used through definitional unfolding, where rewriting is blocked by the category
instances of the fibres. -/
theorem mapId_comp {W V : Type*} [Category W] [Category V] (F : W ⥤ V) {a : W} {c : V}
    (v : F.obj a ⟶ c) : F.map (𝟙 a) ≫ v = v := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The section comparison of the vertex of a fibre product of cone stacks is, on fibres, the
section comparison of the vertex of the first factor: the two intervening cells (an associator
and the first projection cell of the universal property) are identities. -/
theorem prod_vertexProjectionIso_hom_app (C D : ConeStack base O) (T : Scheme.{u})
    (z : StackFiber base T) :
    ((prodVertexProjectionIso C D).appIso T).hom.app z =
      (C.vertexProjectionIso.appIso T).hom.app z := by
  change 𝟙 _ ≫ (StackHom.appFunctor C.projection T).map (𝟙 _) ≫
      (C.vertexProjectionIso.appIso T).hom.app z = _
  exact (Category.id_comp _).trans (mapId_comp _ _)

/-- The strong-naturality cell of the projection of a fibre product of cone stacks is, on
fibres, the strong-naturality cell of the projection of the first factor: the projection of the
fibre product is the first projection of the two-pullback followed by the projection of the
first factor, and the first projection of a two-pullback has identity naturality cell. -/
theorem prod_projectionNaturality_hom_app (C D : ConeStack base O) {S T : Scheme.{u}}
    (h : S ⟶ T) (p : StackFiber (prodTotal C D) T) :
    (StackHom.naturalityIso (prodProjection C D) h).hom.app p =
      (C.projectionNaturality h).hom.app (CategoricalPullback.fst p) := by
  change 𝟙 _ ≫ (StackHom.appFunctor C.projection S).map (𝟙 _) ≫ 𝟙 _ ≫
      (C.projectionNaturality h).hom.app (CategoricalPullback.fst p) ≫ 𝟙 _ = _
  simp

/-! ### The five coherence laws of a fibre product -/

/-- The unit law of a fibre product of cone stacks: it is the unit law of the first factor,
evaluated on the first component of a point of the two-pullback. -/
theorem prodIsCoherent_one {C D : ConeStack base O} (hC : IsCoherent C)
    (hp : ProdCoherence C D) (T : Scheme.{u}) (p : StackFiber (prod C D hp).total T) :
    (StackHom.appFunctor (prod C D hp).projection T).map
        (((prod C D hp).contractionOneIso T).hom.app p) =
      ((prod C D hp).contractionProjectionIso T 1).hom.app p :=
  hC.one T (CategoricalPullback.fst p)

/-- The multiplication law of a fibre product of cone stacks: it is the multiplication law of
the first factor, evaluated on the first component of a point of the two-pullback. -/
theorem prodIsCoherent_mul {C D : ConeStack base O} (hC : IsCoherent C)
    (hp : ProdCoherence C D) (T : Scheme.{u}) (r s : O.ring T)
    (p : StackFiber (prod C D hp).total T) :
    (StackHom.appFunctor (prod C D hp).projection T).map
          (((prod C D hp).contractionMulIso T r s).hom.app p) ≫
        ((prod C D hp).contractionProjectionIso T r).hom.app
            (((prod C D hp).contraction T s).obj p) ≫
          ((prod C D hp).contractionProjectionIso T s).hom.app p =
      ((prod C D hp).contractionProjectionIso T (r * s)).hom.app p :=
  hC.mul T r s (CategoricalPullback.fst p)

/-- The vertex law of a fibre product of cone stacks: it is the vertex law of the first
factor, because the first component of the vertex of the fibre product is the vertex of the
first factor. -/
theorem prodIsCoherent_vertex {C D : ConeStack base O} (hC : IsCoherent C)
    (hp : ProdCoherence C D) (T : Scheme.{u}) (r : O.ring T) (b : StackFiber base T) :
    (StackHom.appFunctor (prod C D hp).projection T).map
        (((prod C D hp).contractionVertexIso T r).hom.app b) =
      ((prod C D hp).contractionProjectionIso T r).hom.app
        ((StackHom.appFunctor (prod C D hp).vertex T).obj b) :=
  hC.vertex T r b

/-- The zero law of a fibre product of cone stacks: it is the zero law of the first factor,
after identifying the section comparison of the vertex of the fibre product with that of the
first factor. -/
theorem prodIsCoherent_zero {C D : ConeStack base O} (hC : IsCoherent C)
    (hp : ProdCoherence C D) (T : Scheme.{u}) (p : StackFiber (prod C D hp).total T) :
    (StackHom.appFunctor (prod C D hp).projection T).map
          (((prod C D hp).contractionZeroIso T).hom.app p) ≫
        ((prod C D hp).vertexProjectionIso.appIso T).hom.app
          ((StackHom.appFunctor (prod C D hp).projection T).obj p) =
      ((prod C D hp).contractionProjectionIso T 0).hom.app p := by
  have h0 := hC.zero T (CategoricalPullback.fst p)
  have key : (StackHom.appFunctor C.projection T).map
          ((C.contractionZeroIso T).hom.app (CategoricalPullback.fst p)) ≫
        ((prodVertexProjectionIso C D).appIso T).hom.app
          ((StackHom.appFunctor C.projection T).obj (CategoricalPullback.fst p)) =
      (C.contractionProjectionIso T 0).hom.app (CategoricalPullback.fst p) := by
    rw [prod_vertexProjectionIso_hom_app]
    exact h0
  exact key

/-- The reindexing law of a fibre product of cone stacks: it is the reindexing law of the first
factor, after identifying the strong-naturality cell of the projection of the fibre product
with that of the first factor. -/
theorem prodIsCoherent_pullback {C D : ConeStack base O} (hC : IsCoherent C)
    (hp : ProdCoherence C D) {S T : Scheme.{u}} (h : S ⟶ T) (r : O.ring T)
    (p : StackFiber (prod C D hp).total T) :
    (StackHom.appFunctor (prod C D hp).projection S).map
          (((prod C D hp).contractionPullbackIso h r).hom.app p) ≫
        ((prod C D hp).contractionProjectionIso S (O.pullback h r)).hom.app
            ((stackPullback (prod C D hp).total h).obj p) ≫
          ((prod C D hp).projectionNaturality h).hom.app p =
      ((prod C D hp).projectionNaturality h).hom.app (((prod C D hp).contraction T r).obj p) ≫
        (stackPullback base h).map
          (((prod C D hp).contractionProjectionIso T r).hom.app p) := by
  have hpb := hC.pullback h r (CategoricalPullback.fst p)
  have key : (StackHom.appFunctor C.projection S).map
          ((C.contractionPullbackIso h r).hom.app (CategoricalPullback.fst p)) ≫
        (C.contractionProjectionIso S (O.pullback h r)).hom.app
            ((stackPullback C.total h).obj (CategoricalPullback.fst p)) ≫
          (StackHom.naturalityIso (prodProjection C D) h).hom.app p =
      (StackHom.naturalityIso (prodProjection C D) h).hom.app
          ((prodContraction C D T r).obj p) ≫
        (stackPullback base h).map
          ((C.contractionProjectionIso T r).hom.app (CategoricalPullback.fst p)) := by
    rw [prod_projectionNaturality_hom_app C D h ((prodContraction C D T r).obj p),
      prod_projectionNaturality_hom_app C D h p]
    exact hpb
  exact key

/-- A fibre product of cone stacks is coherent as soon as its **first** factor is: the
projection of the fibre product to the base is taken through the first factor, and all five
laws reduce to the laws of that factor.  No hypothesis on the second factor is needed beyond
the coherence hypothesis `hp` which is already required to form the fibre product. -/
theorem isCoherent_prod {C D : ConeStack base O} (hC : IsCoherent C)
    (hp : ProdCoherence C D) : IsCoherent (prod C D hp) where
  one := prodIsCoherent_one hC hp
  mul := prodIsCoherent_mul hC hp
  vertex := prodIsCoherent_vertex hC hp
  zero := prodIsCoherent_zero hC hp
  pullback := prodIsCoherent_pullback hC hp

/-- The fibre product of two coherent cone stacks is coherent, so iterated fibre products of
coherent cone stacks are unconditional. -/
theorem isCoherent_prodOfCoherent {C D : ConeStack base O} (hC : IsCoherent C)
    (hD : IsCoherent D) : IsCoherent (prodOfCoherent hC hD) :=
  isCoherent_prod hC (ProdCoherence.of_isCoherent hC hD)

/-! ### The two projections of a fibre product -/

/-- The first projection of a fibre product acts on fibres as the first projection of the
two-pullback. -/
theorem prodHomFst_appFunctor_obj (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (p : StackFiber (prod C D hp).total T) :
    (StackHom.appFunctor (prodHomFst C D hp).toStackHom T).obj p =
      CategoricalPullback.fst p :=
  rfl

/-- The second projection of a fibre product acts on fibres as the second projection of the
two-pullback. -/
theorem prodHomSnd_appFunctor_obj (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (p : StackFiber (prod C D hp).total T) :
    (StackHom.appFunctor (prodHomSnd C D hp).toStackHom T).obj p =
      CategoricalPullback.snd p :=
  rfl

/-- The first projection of a fibre product is *strictly* equivariant: its equivariance cell is
the identity, that is, contracting and then projecting is the same functor as projecting and
then contracting. -/
theorem prodHomFst_equivariant_eq (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (r : O.ring T) :
    (prodHomFst C D hp).equivariant T r = CategoryTheory.Iso.refl _ :=
  rfl

/-- The second projection of a fibre product is *strictly* equivariant. -/
theorem prodHomSnd_equivariant_eq (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (r : O.ring T) :
    (prodHomSnd C D hp).equivariant T r = CategoryTheory.Iso.refl _ :=
  rfl

/-- The first projection of a fibre product lies over the base on the nose. -/
theorem prodHomFst_overBase_appIso_hom_app (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (p : StackFiber (prod C D hp).total T) :
    (((prodHomFst C D hp).overBase).appIso T).hom.app p = 𝟙 _ :=
  rfl

/-- The second projection of a fibre product lies over the base through the comparison
isomorphism carried by a point of the two-pullback. -/
theorem prodHomSnd_overBase_appIso_hom_app (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (p : StackFiber (prod C D hp).total T) :
    (((prodHomSnd C D hp).overBase).appIso T).hom.app p = (CategoricalPullback.iso p).inv :=
  rfl

/-! ### The universal property of a fibre product on fibres -/

/-- An isomorphism of the underlying objects commuting with the chosen comparisons is an
isomorphism in the fibre of a cone stack over a fixed base object. -/
noncomputable def FiberOver.isoMk {C : ConeStack base O} {T : Scheme.{u}}
    {b : StackFiber base T} {x y : C.FiberOver T b} (e : x.object ≅ y.object)
    (w : (StackHom.appFunctor C.projection T).map e.hom ≫ y.comparison.hom =
      x.comparison.hom) : x ≅ y where
  hom := ⟨e.hom, w⟩
  inv := ⟨e.inv, by
    rw [← w, ← Category.assoc, ← CategoryTheory.Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]⟩
  hom_inv_id := FiberOver.Hom.ext _ _ e.hom_inv_id
  inv_hom_id := FiberOver.Hom.ext _ _ e.inv_hom_id

/-- Transporting the compatibility of an arrow with the comparisons from the first to the
second component of a point of a two-pullback.  Stated abstractly for use through definitional
unfolding. -/
theorem prodFiberOver_snd_comm {W : Type*} [Category W] {a a' d d' e : W}
    (m : a ⟶ a') (n : d ⟶ d') (α : a ≅ d) (α' : a' ≅ d') (c : a ⟶ e) (c' : a' ⟶ e)
    (hw : m ≫ α'.hom = α.hom ≫ n) (hc : m ≫ c' = c) :
    n ≫ α'.inv ≫ c' = α.inv ≫ c := by
  have hm : m = α.hom ≫ n ≫ α'.inv := by
    rw [← cancel_mono α'.hom]
    simp [hw]
  rw [← hc, hm]
  simp

/-- The morphism condition of the two-pullback for a pair of arrows over a fixed base object.
Stated abstractly for use through definitional unfolding. -/
theorem prodFiberOver_w {W : Type*} [Category W] {x x' y y' e : W} (m : x ⟶ x') (n : y ⟶ y')
    (cx : x ≅ e) (cx' : x' ≅ e) (cy : y ≅ e) (cy' : y' ≅ e)
    (hx : m ≫ cx'.hom = cx.hom) (hy : n ≫ cy'.hom = cy.hom) :
    m ≫ cx'.hom ≫ cy'.inv = (cx.hom ≫ cy.inv) ≫ n := by
  have h : cy.inv ≫ n = cy'.inv := by
    rw [← cancel_mono cy'.hom]
    simp [hy]
  rw [← Category.assoc, hx, Category.assoc, ← h]

/-- The morphism condition for the unit of the fibre equivalence.  Stated abstractly for use
through definitional unfolding. -/
theorem prodFiberOver_unit_w {W : Type*} [Category W] {a d e : W} (α : a ≅ d) (c : a ≅ e)
    {m : a ⟶ a} (hm : m = 𝟙 a) {n : d ⟶ d} (hn : n = 𝟙 d) :
    m ≫ (c ≪≫ (α.symm ≪≫ c).symm).hom = α.hom ≫ n := by
  subst hm
  subst hn
  simp

/-- Composing with an arrow which is an identity.  Stated abstractly for use through
definitional unfolding. -/
theorem prodFiberOver_eqId_comp {W : Type*} [Category W] {a e : W} {m : a ⟶ a} (hm : m = 𝟙 a)
    (v : a ⟶ e) : m ≫ v = v := by
  subst hm
  simp

/-- The comparison condition for the counit of the fibre equivalence.  Stated abstractly for
use through definitional unfolding. -/
theorem prodFiberOver_counit_comm {W : Type*} [Category W] {x d e : W} (cx : x ≅ e) (cy : d ≅ e)
    {n : d ⟶ d} (hn : n = 𝟙 d) :
    n ≫ cy.hom = ((cx ≪≫ cy.symm).symm ≪≫ cx).hom := by
  subst hn
  simp

/-- From a point of the fibre product over a base object to the pair of its two components:
the first component keeps the comparison with the base, and the second component uses the
comparison isomorphism carried by the point of the two-pullback. -/
noncomputable def prodFiberOverFunctor (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (b : StackFiber base T) :
    (prod C D hp).FiberOver T b ⥤ C.FiberOver T b × D.FiberOver T b where
  obj q :=
    (⟨CategoricalPullback.fst q.object, q.comparison⟩,
      ⟨CategoricalPullback.snd q.object,
        (CategoricalPullback.iso q.object).symm ≪≫ q.comparison⟩)
  map k :=
    (⟨k.hom.fst, k.comm⟩,
      ⟨k.hom.snd, prodFiberOver_snd_comm _ _ _ _ _ _ k.hom.w k.comm⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- From a pair of points of the two factors over a base object to a point of the fibre
product: the comparison isomorphism of the two-pullback is the composite of the two
comparisons with the base. -/
noncomputable def prodFiberOverInverse (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (b : StackFiber base T) :
    C.FiberOver T b × D.FiberOver T b ⥤ (prod C D hp).FiberOver T b where
  obj xy :=
    { object :=
        { fst := xy.1.object
          snd := xy.2.object
          iso := xy.1.comparison ≪≫ xy.2.comparison.symm }
      comparison := xy.1.comparison }
  map k :=
    { hom :=
        { fst := k.1.hom
          snd := k.2.hom
          w := prodFiberOver_w _ _ _ _ _ _ k.1.comm k.2.comm }
      comm := k.1.comm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Splitting a point of the fibre product and recombining it returns the same point: only the
comparison isomorphism has to be rebuilt, and it is recovered on the nose. -/
noncomputable def prodFiberOverUnitIso (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (b : StackFiber base T) :
    𝟭 ((prod C D hp).FiberOver T b) ≅
      prodFiberOverFunctor C D hp T b ⋙ prodFiberOverInverse C D hp T b :=
  NatIso.ofComponents
    (fun q => FiberOver.isoMk
      (CategoricalPullback.mkIso (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
        (prodFiberOver_unit_w _ _ (CategoryTheory.Functor.map_id _ _)
          (CategoryTheory.Functor.map_id _ _)))
      (prodFiberOver_eqId_comp (CategoryTheory.Functor.map_id _ _) _))
    (fun k => by
      apply FiberOver.Hom.ext
      apply CategoricalPullback.hom_ext
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Recombining a pair of points over a base object and splitting it again returns the same
pair. -/
noncomputable def prodFiberOverCounitIso (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (b : StackFiber base T) :
    prodFiberOverInverse C D hp T b ⋙ prodFiberOverFunctor C D hp T b ≅
      𝟭 (C.FiberOver T b × D.FiberOver T b) :=
  NatIso.ofComponents
    (fun xy => CategoryTheory.Iso.prod (CategoryTheory.Iso.refl xy.1)
      (FiberOver.isoMk (CategoryTheory.Iso.refl xy.2.object)
        (prodFiberOver_counit_comm xy.1.comparison xy.2.comparison
          (CategoryTheory.Functor.map_id _ _))))
    (fun k => by
      apply Prod.ext
      · exact FiberOver.Hom.ext _ _
          ((Category.comp_id _).trans (Category.id_comp _).symm)
      · exact FiberOver.Hom.ext _ _
          ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The universal property of the fibre product of two cone stacks on fibres: over a fixed
object `b` of the base fibre, the groupoid of points of `ConeStack.prod C D hp` is equivalent
to the product of the groupoids of points of the two factors. -/
noncomputable def prodFiberOverEquiv (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (b : StackFiber base T) :
    (prod C D hp).FiberOver T b ≌ C.FiberOver T b × D.FiberOver T b :=
  CategoryTheory.Equivalence.mk (prodFiberOverFunctor C D hp T b)
    (prodFiberOverInverse C D hp T b) (prodFiberOverUnitIso C D hp T b)
    (prodFiberOverCounitIso C D hp T b)

/-- The equivalence of fibres is compatible with the first projection of the fibre product. -/
theorem prodFiberOverFunctor_obj_fst_object (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (b : StackFiber base T) (q : (prod C D hp).FiberOver T b) :
    ((prodFiberOverFunctor C D hp T b).obj q).1.object =
      (StackHom.appFunctor (prodHomFst C D hp).toStackHom T).obj q.object :=
  rfl

/-- The equivalence of fibres is compatible with the second projection of the fibre
product. -/
theorem prodFiberOverFunctor_obj_snd_object (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (b : StackFiber base T) (q : (prod C D hp).FiberOver T b) :
    ((prodFiberOverFunctor C D hp T b).obj q).2.object =
      (StackHom.appFunctor (prodHomSnd C D hp).toStackHom T).obj q.object :=
  rfl

/-- The inverse of the equivalence of fibres recombines a pair of points into the point of the
two-pullback whose comparison isomorphism is the composite of the two comparisons. -/
theorem prodFiberOverInverse_obj_object_iso (C D : ConeStack base O) (hp : ProdCoherence C D)
    (T : Scheme.{u}) (b : StackFiber base T) (xy : C.FiberOver T b × D.FiberOver T b) :
    CategoricalPullback.iso ((prodFiberOverInverse C D hp T b).obj xy).object =
      xy.1.comparison ≪≫ xy.2.comparison.symm :=
  rfl

/-! ### Base change along the identity -/

/-- The total stack of the base change of a cone stack along the identity of the base is
equivalent to its own total stack.  Both are genuine two-pullbacks of the same cospan — the
right-identity presentation `StackTwoPullback.rightIdentity` and the canonical fibrewise one —
so the comparison maps and the two inverse laws come from their bilimit universal
properties. -/
noncomputable def baseChangeIdEquivalence (C : ConeStack base O) :
    StackEquivalenceData C.total
      (baseChangeTotal C (Pseudofunctor.StrongTrans.id base.toPseudofunctor)) :=
  StackTwoPullback.presentationEquivalence (StackTwoPullback.rightIdentity C.projection)
    (StackTwoPullback.canonicalGenuine C.projection
      (Pseudofunctor.StrongTrans.id base.toPseudofunctor))

/-- The equivalence identifying a cone stack with its base change along the identity is
compatible with the projections to the base. -/
noncomputable def baseChangeIdProjectionIso (C : ConeStack base O) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (baseChangeIdEquivalence C).hom
        (baseChangeProjection C (Pseudofunctor.StrongTrans.id base.toPseudofunctor)))
      C.projection :=
  (StackTwoPullback.canonicalGenuine C.projection
      (Pseudofunctor.StrongTrans.id base.toPseudofunctor)).bilimit.lift_snd
    (StackTwoPullback.selfCone (StackTwoPullback.rightIdentity C.projection).toStackTwoPullback)

/-- The equivalence identifying a cone stack with its base change along the identity is
compatible with the projection of the base change to the original total stack. -/
noncomputable def baseChangeIdFstIso (C : ConeStack base O) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (baseChangeIdEquivalence C).hom
        (baseChangeFst C (Pseudofunctor.StrongTrans.id base.toPseudofunctor)))
      (Pseudofunctor.StrongTrans.id C.total.toPseudofunctor) :=
  (StackTwoPullback.canonicalGenuine C.projection
      (Pseudofunctor.StrongTrans.id base.toPseudofunctor)).bilimit.lift_fst
    (StackTwoPullback.selfCone (StackTwoPullback.rightIdentity C.projection).toStackTwoPullback)

end ConeStack

end GromovWitten.AlgebraicGeometry
