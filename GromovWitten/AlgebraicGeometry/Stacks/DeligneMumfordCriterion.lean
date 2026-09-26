/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.Scheme
import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent

/-!
# Charts obtained by precomposing with a morphism of schemes

The converse half of the Deligne–Mumford criterion (Stacks 06N3) produces an étale atlas of a
stack with unramified diagonal by *slicing* a smooth chart `u : U → X`: for every point of `U`
one cuts `U` down to a locally closed subscheme `W ⊆ U`, and the disjoint union of the resulting
family of morphisms `W → U → X` is the desired étale atlas.  Every member of that family, and
also the disjoint union of the family, is a chart of the form

  `A.precomp g`,  `g : W ⟶ A.scheme`,

where `A` is the given chart.  This file constructs such charts and computes all of their
comparison data:

* `StackChart.precomp A g` is the chart with scheme `W` and structure morphism the composite of
  the promoted scheme morphism `g` with the structure morphism of `A`;
* `StackChart.precomp_obj`, `precomp_objIsoOfEq`, `precomp_objPullbackIso`,
  `precomp_inducedComparison` identify its objects and its pseudonaturality isomorphisms with
  those of `A` at the composed scheme maps (the promoted scheme morphism contributes nothing,
  because the fibres of a represented stack are discrete);
* `StackChart.precomp_classifies_iff` identifies the classification property of the precomposed
  chart with that of `A`, with both chart legs composed with `g`;
* `StackChart.inducedComparison_comp` is the chart-level transitivity of induced comparisons:
  the comparison induced in two steps is the comparison induced by the composite.  It is the
  chart-level counterpart of `stackMorphismInducedComparison_comp` and is the key step for
  building the base-change presentations of a precomposed chart out of those of `A` by an
  ordinary pullback of schemes.

## What is still missing

The intended continuation is the presentation

  `precompPresentation (p : A.PullbackPresentation T x) : (A.precomp g).PullbackPresentation T x`

with `space := pullback p.snd g`, `fst := pullback.fst ≫ p.fst`, `snd := pullback.snd` and
`comparison := (A.objIsoOfEq pullback.condition.symm).trans
  (A.inducedComparison p.fst p.snd p.comparison pullback.fst)`.  Its `lift`, `lift_fst` and
`lift_snd` fields are immediate from `p.lift` and `pullback.lift`; its `lift_compatible` and
`lift_unique` fields need, besides `precomp_classifies_iff` and `inducedComparison_comp`, two
further transport lemmas, both proved here: `inducedComparison_objIsoOfEq` (which absorbs
`pullback.condition`) and `inducedComparison_changeMap` (which absorbs `pullback.lift_fst`).
What remains for the presentation is therefore only the bookkeeping chaining these four
equations inside the `Classifies` predicate, in both the `lift_compatible` and the
`lift_unique` direction.

Beyond that, the converse Deligne–Mumford criterion
(`∃ A : StackChart X, A.IsEtaleSurjective` from `(stackDiagonal X).Unramified`) needs, for a
smooth chart `A` with `hA : A.IsSmoothSurjective`:

1. the geometric slicing input: for every point `u₀ : A.scheme` a scheme `W`, a morphism
   `g : W ⟶ A.scheme` whose image contains `u₀`, such that the second projection
   `W ×_X A.scheme ⟶ A.scheme` of a presentation
   `A.PullbackPresentation W ((A.precomp g).obj W (𝟙 W))` is étale.  This is what the ring-level
   slicing lemma of `Stacks.EtaleSlice` (`etale_of_span_eq_top_of_isStandardSmooth`) is for,
   together with
   `Ω_{R/A.scheme × A.scheme} = 0`, which is where `(stackDiagonal X).Unramified` enters.
2. the descent step: `Etale` of the first projection of `precompPresentation p` for arbitrary
   `T`, `x`, obtained from (1) by base change along the fppf cover `p.fst` and descent of
   `Etale` along fppf covers (`Stacks.PropertiesDescent`).
3. the gluing step: the disjoint union of the slices of (1) is again of the form `A.precomp` of
   the morphism `Sigma.desc`, whose étaleness is `IsLocalAtSource.sigmaDesc` and whose
   surjectivity follows because each slice meets its own point.
-/

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackChart

variable {X : FppfStack.{u}} (A : StackChart X)

/-- The chart obtained from `A` by precomposing with a morphism of schemes `g : W ⟶ A.scheme`.
Its scheme is `W` and its structure morphism is the composite of the promoted scheme morphism
with the structure morphism of `A`. -/
noncomputable def precomp {W : Scheme.{u}} (g : W ⟶ A.scheme) : StackChart X where
  scheme := W
  map := Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom g) A.map

@[simp]
theorem precomp_scheme {W : Scheme.{u}} (g : W ⟶ A.scheme) : (A.precomp g).scheme = W := rfl

/-- The objects of a precomposed chart are the objects of the original chart attached to the
composed scheme maps. -/
theorem precomp_obj {W T : Scheme.{u}} (g : W ⟶ A.scheme) (f : T ⟶ W) :
    (A.precomp g).obj T f = A.obj T (f ≫ g) := rfl

/-- The equality-induced isomorphisms of a precomposed chart are those of the original chart. -/
theorem precomp_objIsoOfEq {W T : Scheme.{u}} (g : W ⟶ A.scheme) {f f' : T ⟶ W} (h : f = f') :
    (A.precomp g).objIsoOfEq h = A.objIsoOfEq (congrArg (· ≫ g) h) := by
  subst h; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The pseudonaturality isomorphism of a precomposed chart is the one of the original chart at
the composed scheme map: the promoted scheme morphism contributes the identity, because the
fibres of a represented stack are discrete. -/
theorem precomp_objPullbackIso {W T S : Scheme.{u}} (g : W ⟶ A.scheme) (f : T ⟶ W) (m : S ⟶ T) :
    (A.precomp g).objPullbackIso m f = A.objPullbackIso m (f ≫ g) := by
  apply Iso.ext
  have hcomp := congrArg (fun k ↦ k.toNatTrans.app (Discrete.mk f))
    (Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom
      (FppfStack.mapOfSchemeHom g) A.map ⟨m.op⟩)
  change ((Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom g) A.map).naturality
    ⟨m.op⟩).hom.toNatTrans.app (Discrete.mk f) = _ at hcomp
  simp only [Cat.Hom.comp_toFunctor, GrothendieckTopology.yoneda_obj_obj, yoneda_obj_obj,
    Functor.comp_obj, Cat.Hom.toNatTrans_comp, Cat.associator_inv_toNatTrans,
    Cat.whiskerRight_toNatTrans, Cat.associator_hom_toNatTrans, Cat.whiskerLeft_toNatTrans,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Discrete.functor_map_id, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.comp_id, Category.id_comp] at hcomp
  change ((Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom g) A.map).naturality
    (⟨m.op⟩ : LocallyDiscrete.mk (Opposite.op T) ⟶
      LocallyDiscrete.mk (Opposite.op S))).hom.toNatTrans.app (Discrete.mk f) =
    (A.map.naturality (⟨m.op⟩ : LocallyDiscrete.mk (Opposite.op T) ⟶
      LocallyDiscrete.mk (Opposite.op S))).hom.toNatTrans.app (Discrete.mk (f ≫ g))
  rw [hcomp]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- The induced comparison of a precomposed chart is the induced comparison of the original
chart at the composed chart leg. -/
theorem precomp_inducedComparison {W U T S : Scheme.{u}} (g : W ⟶ A.scheme) (fst : U ⟶ T)
    (snd : U ⟶ W) {x : StackFiber X T}
    (universal : (A.precomp g).obj U snd ≅ (stackPullback X fst).obj x) (m : S ⟶ U) :
    (A.precomp g).inducedComparison fst snd universal m =
      A.inducedComparison fst (snd ≫ g) universal m := by
  apply Iso.ext
  simp only [inducedComparison, Iso.trans_hom]
  rw [show ((Cat.Hom.toNatIso ((A.precomp g).map.naturality ⟨m.op⟩)).app
        (Discrete.mk snd)).hom =
      ((Cat.Hom.toNatIso (A.map.naturality ⟨m.op⟩)).app (Discrete.mk (snd ≫ g))).hom from
    congrArg Iso.hom (A.precomp_objPullbackIso g snd m)]

set_option backward.isDefEq.respectTransparency false in
/-- Classification for a precomposed chart is classification for the original chart, with both
chart legs composed with `g`. -/
theorem precomp_classifies_iff {W U T S : Scheme.{u}} (g : W ⟶ A.scheme) (fst : U ⟶ T)
    (snd : U ⟶ W) {x : StackFiber X T}
    (universal : (A.precomp g).obj U snd ≅ (stackPullback X fst).obj x)
    (toBase : S ⟶ T) (toChart : S ⟶ W)
    (c : (A.precomp g).obj S toChart ≅ (stackPullback X toBase).obj x) (m : S ⟶ U)
    (snd_eq : m ≫ snd = toChart) :
    (A.precomp g).Classifies fst snd universal toBase toChart c m ↔
      A.Classifies fst (snd ≫ g) universal toBase (toChart ≫ g) c m := by
  constructor
  · rintro ⟨fst_eq, snd_eq', heq⟩
    rw [precomp_objIsoOfEq, precomp_inducedComparison] at heq
    exact ⟨fst_eq, congrArg (· ≫ g) snd_eq', heq⟩
  · rintro ⟨fst_eq, _, heq⟩
    refine ⟨fst_eq, snd_eq, ?_⟩
    rw [precomp_objIsoOfEq, precomp_inducedComparison]
    exact heq

set_option backward.isDefEq.respectTransparency false in
/-- The comparison induced in two steps, first along `k` and then along `m`, is the comparison
induced along the composite `m ≫ k`, up to the transport forced by associativity of
composition of scheme maps.  This is the chart-level form of
`stackMorphismInducedComparison_comp`. -/
theorem inducedComparison_comp {V U T S : Scheme.{u}} (fst : U ⟶ T) (snd : U ⟶ A.scheme)
    {x : StackFiber X T} (universal : A.obj U snd ≅ (stackPullback X fst).obj x)
    (k : V ⟶ U) (m : S ⟶ V) :
    A.inducedComparison (k ≫ fst) (k ≫ snd) (A.inducedComparison fst snd universal k) m =
      (A.objIsoOfEq (Category.assoc m k snd).symm).trans
        ((A.inducedComparison fst snd universal (m ≫ k)).trans
          (stackPullbackObjIsoOfEq X (Category.assoc m k fst) x)) := by
  apply Iso.ext
  simp only [inducedComparison, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.app_hom, Cat.Hom.toNatIso_hom]
  have hp := (Cat.Hom.toNatIso
    (X.toPseudofunctor.mapComp ⟨k.op⟩ ⟨m.op⟩)).inv.naturality universal.hom
  change (stackPullback X m).map ((stackPullback X k).map universal.hom) ≫
      (stackPullbackCompIso X m k ((stackPullback X fst).obj x)).hom =
    (stackPullbackCompIso X m k (A.obj U snd)).hom ≫
      (stackPullback X (m ≫ k)).map universal.hom at hp
  rw [stackPullbackCompIso_assoc X m k fst x]
  rw [reassoc_of% hp]
  have hn : (A.map.naturality (⟨m.op⟩ : LocallyDiscrete.mk (Opposite.op V) ⟶
          LocallyDiscrete.mk (Opposite.op S))).hom.toNatTrans.app (Discrete.mk (k ≫ snd)) ≫
        (stackPullback X m).map
          ((A.map.naturality (⟨k.op⟩ : LocallyDiscrete.mk (Opposite.op U) ⟶
            LocallyDiscrete.mk (Opposite.op V))).hom.toNatTrans.app (Discrete.mk snd)) ≫
        (stackPullbackCompIso X m k (A.obj U snd)).hom =
      (A.map.appFunctor S).map
          (stackPullbackCompIso (representedStack A.scheme) m k (Discrete.mk snd)).hom ≫
        (A.map.naturality (⟨(m ≫ k).op⟩ : LocallyDiscrete.mk (Opposite.op U) ⟶
          LocallyDiscrete.mk (Opposite.op S))).hom.toNatTrans.app (Discrete.mk snd) :=
    (stackHomNaturalityCompPullback A.map m k (Discrete.mk snd)).symm
  rw [reassoc_of% hn]
  have hobj : (A.map.appFunctor S).map
        (stackPullbackCompIso (representedStack A.scheme) m k (Discrete.mk snd)).hom =
      (A.objIsoOfEq (Category.assoc m k snd).symm).hom := by
    rw [objIsoOfEq_hom]
    refine congrArg (A.map.appFunctor S).map ?_
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  rw [hobj]

set_option backward.isDefEq.respectTransparency false in
/-- Changing the classifying map by an equality changes the induced comparison only by the
transports forced by that equality. -/
theorem inducedComparison_changeMap {U T S : Scheme.{u}} (fst : U ⟶ T) (snd : U ⟶ A.scheme)
    {x : StackFiber X T} (universal : A.obj U snd ≅ (stackPullback X fst).obj x)
    {m m' : S ⟶ U} (h : m = m') :
    A.inducedComparison fst snd universal m =
      (A.objIsoOfEq (congrArg (· ≫ snd) h)).trans
        ((A.inducedComparison fst snd universal m').trans
          (stackPullbackObjIsoOfEq X (congrArg (· ≫ fst) h).symm x)) := by
  subst h
  apply Iso.ext
  simp only [inducedComparison, Cat.Hom.comp_toFunctor, GrothendieckTopology.yoneda_obj_obj,
    yoneda_obj_obj, Functor.comp_obj, Iso.trans_assoc, Iso.trans_hom, Iso.app_hom,
    Cat.Hom.toNatIso_hom, Functor.mapIso_hom, stackPullbackObjIsoOfEq, Iso.trans_refl,
    objIsoOfEq_hom, eqToHom_refl, Discrete.functor_map_id]
  exact (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing the universal comparison with an equality transport of the chart leg only
transports the induced comparison. -/
theorem inducedComparison_objIsoOfEq {U T S : Scheme.{u}} (fst : U ⟶ T)
    {snd snd' : U ⟶ A.scheme} (h : snd' = snd)
    {x : StackFiber X T} (universal : A.obj U snd ≅ (stackPullback X fst).obj x)
    (m : S ⟶ U) :
    A.inducedComparison fst snd' ((A.objIsoOfEq h).trans universal) m =
      (A.objIsoOfEq (congrArg (m ≫ ·) h)).trans (A.inducedComparison fst snd universal m) := by
  subst h
  apply Iso.ext
  simp only [inducedComparison, Cat.Hom.comp_toFunctor, GrothendieckTopology.yoneda_obj_obj,
    yoneda_obj_obj, Functor.comp_obj, Functor.mapIso_trans, Iso.trans_assoc, Iso.trans_hom,
    Iso.app_hom, Cat.Hom.toNatIso_hom, Functor.mapIso_hom, objIsoOfEq_hom, eqToHom_refl,
    Discrete.functor_map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.id_comp _).symm

end StackChart

end GromovWitten.AlgebraicGeometry
