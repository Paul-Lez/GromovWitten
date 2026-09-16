/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.Algebraic

/-!
# Calculus of representable stack morphisms

This file constructs the composition part of the geometric calculus for representable
morphisms of groupoid-valued stacks.  The former provisional API stored composition and
base-change theorems as fields.  Here the composite presentation, including its comparison,
pseudofunctorial pasting, and both uniqueness laws, is derived from two actual scheme-valued
universal properties.  Explicit transport across invertible 2-cells and the canonical
two-pullback base-change calculus are developed in `PresentationTransport` and `BaseChange`.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

/-- Equality transport of pulled-back stack objects respects transitivity of the underlying
scheme-map equalities. -/
theorem stackPullbackObjIsoOfEq_trans
    (W : FppfStack.{u}) {S T : Scheme.{u}} {a b c : S ⟶ T}
    (hab : a = b) (hbc : b = c) (z : StackFiber W T) :
    (stackPullbackObjIsoOfEq W hab z).trans
        (stackPullbackObjIsoOfEq W hbc z) =
      stackPullbackObjIsoOfEq W (hab.trans hbc) z := by
  subst b
  subst c
  simp [stackPullbackObjIsoOfEq]

set_option backward.isDefEq.respectTransparency false in
/-- Changing a classifying scheme map by equality changes its induced comparison only by the
canonical equality transport.  The hypothesis also requires the source-object isomorphism to
be transported, so no automorphism of the source object is discarded. -/
theorem stackMorphismInducedComparison_changeMap
    {X Y : FppfStack.{u}} (f : StackHom X Y)
    {U T : Scheme.{u}} (map : U ⟶ T) (object : StackFiber X U)
    (y : StackFiber Y T)
    (universal : (f.appFunctor U).obj object ≅
      (stackPullback Y map).obj y)
    {S : Scheme.{u}} {a b : S ⟶ U} (hab : a = b) (x : StackFiber X S)
    (ea : x ≅ (stackPullback X a).obj object)
    (eb : x ≅ (stackPullback X b).obj object)
    (he : ea.trans (stackPullbackObjIsoOfEq X hab object) = eb) :
    (stackMorphismInducedComparison f map object y universal a x ea).trans
        (stackPullbackObjIsoOfEq Y (congrArg (fun k => k ≫ map) hab) y) =
      stackMorphismInducedComparison f map object y universal b x eb := by
  subst b
  simp only [stackPullbackObjIsoOfEq, Iso.trans_refl] at he ⊢
  subst eb
  rfl

/-- A complete classification remains valid after changing the classifying scheme map by
equality and transporting the source-object isomorphism along that equality. -/
theorem stackMorphismClassifies_changeMap
    {X Y : FppfStack.{u}} {f : StackHom X Y}
    {U T : Scheme.{u}} {map : U ⟶ T} {object : StackFiber X U}
    {y : StackFiber Y T}
    {universal : (f.appFunctor U).obj object ≅ (stackPullback Y map).obj y}
    {S : Scheme.{u}} {toBase : S ⟶ T} {x : StackFiber X S}
    {comparison : (f.appFunctor S).obj x ≅ (stackPullback Y toBase).obj y}
    {a b : S ⟶ U}
    (ea : x ≅ (stackPullback X a).obj object)
    (eb : x ≅ (stackPullback X b).obj object)
    (h : StackMorphismClassifies f map object y universal
      toBase x comparison a ea)
    (hab : a = b)
    (he : ea.trans (stackPullbackObjIsoOfEq X hab object) = eb) :
    StackMorphismClassifies f map object y universal
      toBase x comparison b eb := by
  subst b
  simp only [stackPullbackObjIsoOfEq, Iso.trans_refl] at he
  subst eb
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Pulling the compositor of the source stack through a stack morphism is the same as
composing the two strong-naturality cells and the compositor of the target stack. -/
theorem stackHomNaturalityCompPullback
    {Y Z : FppfStack.{u}} (g : StackHom Y Z)
    {S U V : Scheme.{u}} (h : S ⟶ U) (qMap : U ⟶ V)
    (pObj : StackFiber Y V) :
    (g.appFunctor S).map (stackPullbackCompIso Y h qMap pObj).hom ≫
        (g.naturality ⟨(h ≫ qMap).op⟩).hom.toNatTrans.app pObj =
      (g.naturality ⟨h.op⟩).hom.toNatTrans.app
          ((stackPullback Y qMap).obj pObj) ≫
        (stackPullback Z h).map
          ((g.naturality ⟨qMap.op⟩).hom.toNatTrans.app pObj) ≫
        (stackPullbackCompIso Z h qMap ((g.appFunctor V).obj pObj)).hom := by
  let qop : LocallyDiscrete.mk (Opposite.op V) ⟶
      LocallyDiscrete.mk (Opposite.op U) := ⟨qMap.op⟩
  let hop : LocallyDiscrete.mk (Opposite.op U) ⟶
      LocallyDiscrete.mk (Opposite.op S) := ⟨h.op⟩
  have hc := Pseudofunctor.StrongTrans.naturality_comp_hom_app
    g qop hop pObj
  change (g.naturality ⟨(h ≫ qMap).op⟩).hom.toNatTrans.app pObj = _ at hc
  rw [hc]
  simp only [stackPullbackCompIso, qop, hop, Iso.symm_hom,
    Cat.Hom.toNatIso_inv, Iso.app_hom]
  rw [← Functor.map_comp_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The image of the inverse associator in the locally discrete base bicategory is exactly
transport of a stack object along associativity of scheme-map composition. -/
theorem stackPullbackMap₂AssociatorInv
    (W : FppfStack.{u}) {R S U V : Scheme.{u}}
    (h : R ⟶ S) (qMap : S ⟶ U) (pMap : U ⟶ V)
    (z : StackFiber W V) :
    (W.toPseudofunctor.map₂ (Bicategory.associator
      (⟨pMap.op⟩ : LocallyDiscrete.mk (Opposite.op V) ⟶
        LocallyDiscrete.mk (Opposite.op U))
      (⟨qMap.op⟩ : LocallyDiscrete.mk (Opposite.op U) ⟶
        LocallyDiscrete.mk (Opposite.op S))
      (⟨h.op⟩ : LocallyDiscrete.mk (Opposite.op S) ⟶
        LocallyDiscrete.mk (Opposite.op R))).inv).toNatTrans.app z =
        (stackPullbackObjIsoOfEq W (Category.assoc h qMap pMap) z).hom := by
  simp only [Bicategory.Strict.associator_eqToIso, eqToIso.inv,
    PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans,
    eqToHom_app, stackPullbackObjIsoOfEq, Iso.refl_hom]
  apply eqToHom_refl

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of the canonical pullback compositors, including the equality transport
between the two parenthesizations of a triple composite of scheme maps. -/
theorem stackPullbackCompIso_assoc
    (W : FppfStack.{u}) {R S U V : Scheme.{u}}
    (h : R ⟶ S) (qMap : S ⟶ U) (pMap : U ⟶ V)
    (z : StackFiber W V) :
    (stackPullback W h).map (stackPullbackCompIso W qMap pMap z).hom ≫
        (stackPullbackCompIso W h (qMap ≫ pMap) z).hom =
      (stackPullbackCompIso W h qMap ((stackPullback W pMap).obj z)).hom ≫
        (stackPullbackCompIso W (h ≫ qMap) pMap z).hom ≫
          (stackPullbackObjIsoOfEq W (Category.assoc h qMap pMap) z).hom := by
  let pop : LocallyDiscrete.mk (Opposite.op V) ⟶
      LocallyDiscrete.mk (Opposite.op U) := ⟨pMap.op⟩
  let qop : LocallyDiscrete.mk (Opposite.op U) ⟶
      LocallyDiscrete.mk (Opposite.op S) := ⟨qMap.op⟩
  let hop : LocallyDiscrete.mk (Opposite.op S) ⟶
      LocallyDiscrete.mk (Opposite.op R) := ⟨h.op⟩
  have ha := Pseudofunctor.mapComp_assoc_left_inv_app
    W.toPseudofunctor pop qop hop z
  change
    (W.toPseudofunctor.map ⟨h.op⟩).toFunctor.map
        ((W.toPseudofunctor.mapComp ⟨pMap.op⟩ ⟨qMap.op⟩).inv.toNatTrans.app z) ≫
      (W.toPseudofunctor.mapComp ⟨(qMap ≫ pMap).op⟩
        ⟨h.op⟩).inv.toNatTrans.app z =
    (W.toPseudofunctor.mapComp ⟨qMap.op⟩ ⟨h.op⟩).inv.toNatTrans.app
          ((W.toPseudofunctor.map ⟨pMap.op⟩).toFunctor.obj z) ≫
      (W.toPseudofunctor.mapComp ⟨pMap.op⟩
        ⟨(h ≫ qMap).op⟩).inv.toNatTrans.app z ≫
        (W.toPseudofunctor.map₂ (Bicategory.associator pop qop hop).inv).toNatTrans.app z
      at ha
  rw [stackPullbackMap₂AssociatorInv W h qMap pMap z] at ha
  simpa only [stackPullbackCompIso, pop, qop, hop, Iso.symm_hom,
    Cat.Hom.toNatIso_inv, Iso.app_hom] using ha

set_option backward.isDefEq.respectTransparency false in
/-- Pulling the universal comparison of a vertical composite agrees with first pulling the
inner comparison and then the outer comparison.  The final transport is forced by
associativity of scheme-map composition. -/
theorem stackMorphismInducedComparison_vcomp
    {X Y Z : FppfStack.{u}} (f : StackHom X Y) (g : StackHom Y Z)
    {U V T : Scheme.{u}} (qMap : U ⟶ V) (pMap : V ⟶ T)
    (qObj : StackFiber X U) (pObj : StackFiber Y V) (z : StackFiber Z T)
    (qUniversal : (StackHom.appFunctor f U).obj qObj ≅
      (stackPullback Y qMap).obj pObj)
    (pUniversal : (StackHom.appFunctor g V).obj pObj ≅
      (stackPullback Z pMap).obj z)
    {S : Scheme.{u}} (h : S ⟶ U) (x : StackFiber X S)
    (objectIso : x ≅ (stackPullback X h).obj qObj) :
    stackMorphismInducedComparison (Pseudofunctor.StrongTrans.vcomp f g)
        (qMap ≫ pMap) qObj z
        (stackMorphismInducedComparison g pMap pObj z pUniversal qMap
          ((StackHom.appFunctor f U).obj qObj) qUniversal)
        h x objectIso =
      (stackMorphismInducedComparison g pMap pObj z pUniversal (h ≫ qMap)
        ((StackHom.appFunctor f S).obj x)
        (stackMorphismInducedComparison f qMap qObj pObj qUniversal h x objectIso)).trans
      (stackPullbackObjIsoOfEq Z (Category.assoc h qMap pMap) z) := by
  apply Iso.ext
  simp only [stackMorphismInducedComparison, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  change (g.appFunctor S).map ((f.appFunctor S).map objectIso.hom) ≫ _ = _
  have hcomp := congrArg (fun k => k.toNatTrans.app qObj)
    (Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom
      f g ⟨h.op⟩)
  change ((Pseudofunctor.StrongTrans.vcomp f g).naturality
    ⟨h.op⟩).hom.toNatTrans.app qObj = _ at hcomp
  simp at hcomp
  have hcompClean :
      ((Pseudofunctor.StrongTrans.vcomp f g).naturality
        ⟨h.op⟩).hom.toNatTrans.app qObj =
        (g.appFunctor S).map
            ((f.naturality ⟨h.op⟩).hom.toNatTrans.app qObj) ≫
          (g.naturality ⟨h.op⟩).hom.toNatTrans.app
            ((f.appFunctor U).obj qObj) :=
    hcomp.trans (Category.id_comp _)
  simp only [Iso.app_hom, Cat.Hom.toNatIso_hom]
  rw [hcompClean]
  simp only [Category.assoc]
  have hq := (g.naturality ⟨h.op⟩).hom.toNatTrans.naturality qUniversal.hom
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hq
  rw [← reassoc_of% hq]
  rw [reassoc_of% stackHomNaturalityCompPullback g h qMap pObj]
  have hp := (Cat.Hom.toNatIso
    (Z.toPseudofunctor.mapComp ⟨qMap.op⟩ ⟨h.op⟩)).inv.naturality pUniversal.hom
  change
    (stackPullback Z h).map ((stackPullback Z qMap).map pUniversal.hom) ≫
        (stackPullbackCompIso Z h qMap ((stackPullback Z pMap).obj z)).hom =
      (stackPullbackCompIso Z h qMap ((g.appFunctor V).obj pObj)).hom ≫
        (stackPullback Z (h ≫ qMap)).map pUniversal.hom at hp
  rw [← reassoc_of% hp]
  rw [stackPullbackCompIso_assoc Z h qMap pMap z]

namespace StackMorphismPresentation

variable {X Y Z : FppfStack.{u}}
  {f : StackHom X Y} {g : StackHom Y Z}

/-- The universal comparison for the composite presentation.  It is obtained by feeding the
universal comparison for the `f`-presentation into the actual classifying comparison of the
`g`-presentation, so all pseudofunctor and strong-naturality coherence is retained. -/
noncomputable def compComparison {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object) :
    (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) q.space).obj q.object ≅
      (stackPullback Z (q.map ≫ p.map)).obj z :=
  stackMorphismInducedComparison g p.map p.object z p.comparison q.map
    ((StackHom.appFunctor f q.space).obj q.object) q.comparison

/-- The intermediate classifying map to the scheme presenting the base change of `g`. -/
noncomputable def compIntermediateMap {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z) : S ⟶ p.space :=
  p.lift toBase ((StackHom.appFunctor f S).obj x) c

/-- The image of the source object under `f` is the pullback of the intermediate universal
object along `compIntermediateMap`. -/
noncomputable def compIntermediateObjectIso {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z) :
    (StackHom.appFunctor f S).obj x ≅
      (stackPullback Y (p.compIntermediateMap toBase x c)).obj p.object :=
  p.liftObjectIso toBase ((StackHom.appFunctor f S).obj x) c

/-- The intermediate map and object isomorphism satisfy the complete universal comparison for
the presentation of `g`. -/
theorem compIntermediate_classifies {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z) :
    StackMorphismClassifies g p.map p.object z p.comparison toBase
      ((StackHom.appFunctor f S).obj x) c
      (p.compIntermediateMap toBase x c) (p.compIntermediateObjectIso toBase x c) :=
  p.lift_compatible toBase ((StackHom.appFunctor f S).obj x) c

/-- The classifying map to the composite representing scheme is the nested lift: first through
the presentation of `g`, then through the presentation of `f` over its universal object. -/
noncomputable def compLift {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z) : S ⟶ q.space :=
  q.lift (p.compIntermediateMap toBase x c) x
    (p.compIntermediateObjectIso toBase x c)

/-- The nested classifying map lies over the original test-scheme map. -/
theorem compLift_map {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z) :
    p.compLift q toBase x c ≫ (q.map ≫ p.map) = toBase := by
  rw [← Category.assoc]
  change (q.lift (p.compIntermediateMap toBase x c) x
    (p.compIntermediateObjectIso toBase x c) ≫ q.map) ≫ p.map = toBase
  rw [q.lift_map]
  change p.lift toBase ((StackHom.appFunctor f S).obj x) c ≫ p.map = toBase
  exact p.lift_map toBase ((StackHom.appFunctor f S).obj x) c

/-- The source object is the pullback of the universal object on the composite representing
scheme along the nested classifying map. -/
noncomputable def compLiftObjectIso {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z) :
    x ≅ (stackPullback X (p.compLift q toBase x c)).obj q.object :=
  q.liftObjectIso (p.compIntermediateMap toBase x c) x
    (p.compIntermediateObjectIso toBase x c)

/-- The nested lift satisfies the complete universal comparison for the presentation of `f`
over the intermediate scheme. -/
theorem compLift_classifiesIntermediate {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z) :
    StackMorphismClassifies f q.map q.object p.object q.comparison
      (p.compIntermediateMap toBase x c) x (p.compIntermediateObjectIso toBase x c)
      (p.compLift q toBase x c) (p.compLiftObjectIso q toBase x c) :=
  q.lift_compatible (p.compIntermediateMap toBase x c) x
    (p.compIntermediateObjectIso toBase x c)

set_option backward.isDefEq.respectTransparency false in
/-- The nested lift satisfies the complete universal comparison for the composite morphism.
This is the pasting step: both constituent classification equations are used, and the two
parenthesizations of the resulting scheme map are compared by the proved pullback
associativity theorem. -/
theorem compLift_compatible {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z) :
    StackMorphismClassifies (Pseudofunctor.StrongTrans.vcomp f g)
      (q.map ≫ p.map) q.object z (p.compComparison q) toBase x c
      (p.compLift q toBase x c) (p.compLiftObjectIso q toBase x c) := by
  refine ⟨p.compLift_map q toBase x c, ?_⟩
  obtain ⟨hqMap, hqComp⟩ := p.compLift_classifiesIntermediate q toBase x c
  obtain ⟨hpMap, hpComp⟩ := p.compIntermediate_classifies toBase x c
  simp only [compComparison]
  rw [stackMorphismInducedComparison_vcomp]
  let b : S ⟶ q.space := p.compLift q toBase x c
  let a : S ⟶ p.space := p.compIntermediateMap toBase x c
  let inner :
      (f.appFunctor S).obj x ≅ (stackPullback Y (b ≫ q.map)).obj p.object :=
    stackMorphismInducedComparison f q.map q.object p.object q.comparison
      b x (p.compLiftObjectIso q toBase x c)
  let outer :
      (g.appFunctor S).obj ((f.appFunctor S).obj x) ≅
        (stackPullback Z ((b ≫ q.map) ≫ p.map)).obj z :=
    stackMorphismInducedComparison g p.map p.object z p.comparison
      (b ≫ q.map) ((f.appFunctor S).obj x) inner
  let outer' :
      (g.appFunctor S).obj ((f.appFunctor S).obj x) ≅
        (stackPullback Z (a ≫ p.map)).obj z :=
    stackMorphismInducedComparison g p.map p.object z p.comparison
      a ((f.appFunctor S).obj x) (p.compIntermediateObjectIso toBase x c)
  let hAssoc : (b ≫ q.map) ≫ p.map = b ≫ (q.map ≫ p.map) :=
    Category.assoc b q.map p.map
  let hTotal : b ≫ (q.map ≫ p.map) = toBase := p.compLift_map q toBase x c
  let hIntermediate : (b ≫ q.map) ≫ p.map = a ≫ p.map :=
    congrArg (fun k => k ≫ p.map) hqMap
  have hProofs : hAssoc.trans hTotal = hIntermediate.trans hpMap :=
    Subsingleton.elim _ _
  have hchange :
      outer.trans (stackPullbackObjIsoOfEq Z hIntermediate z) = outer' :=
    stackMorphismInducedComparison_changeMap g p.map p.object z p.comparison
      hqMap ((f.appFunctor S).obj x) inner
      (p.compIntermediateObjectIso toBase x c) hqComp
  change (outer.trans (stackPullbackObjIsoOfEq Z hAssoc z)).trans
    (stackPullbackObjIsoOfEq Z hTotal z) = c
  calc
    _ = outer.trans
        ((stackPullbackObjIsoOfEq Z hAssoc z).trans
          (stackPullbackObjIsoOfEq Z hTotal z)) := Iso.trans_assoc _ _ _
    _ = outer.trans
        (stackPullbackObjIsoOfEq Z (hAssoc.trans hTotal) z) := by
      rw [stackPullbackObjIsoOfEq_trans]
    _ = outer.trans
        (stackPullbackObjIsoOfEq Z (hIntermediate.trans hpMap) z) := by
      rw [hProofs]
    _ = outer.trans
        ((stackPullbackObjIsoOfEq Z hIntermediate z).trans
          (stackPullbackObjIsoOfEq Z hpMap z)) := by
      rw [stackPullbackObjIsoOfEq_trans]
    _ = (outer.trans (stackPullbackObjIsoOfEq Z hIntermediate z)).trans
        (stackPullbackObjIsoOfEq Z hpMap z) := by
      rw [Iso.trans_assoc]
    _ = outer'.trans (stackPullbackObjIsoOfEq Z hpMap z) := by rw [hchange]
    _ = c := hpComp

set_option backward.isDefEq.respectTransparency false in
/-- Any classification for the composite morphism determines an actual classification for the
outer presentation.  The intermediate object is not chosen separately: it is the comparison
induced from the supplied source-object isomorphism for the inner presentation. -/
theorem compClassifiesOuter {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z)
    (b : S ⟶ q.space)
    (e : x ≅ (stackPullback X b).obj q.object)
    (hc : StackMorphismClassifies (Pseudofunctor.StrongTrans.vcomp f g)
      (q.map ≫ p.map) q.object z (p.compComparison q) toBase x c b e) :
    StackMorphismClassifies g p.map p.object z p.comparison toBase
      ((f.appFunctor S).obj x) c (b ≫ q.map)
      (stackMorphismInducedComparison f q.map q.object p.object q.comparison b x e) := by
  obtain ⟨hMap, hComp⟩ := hc
  refine ⟨(Category.assoc b q.map p.map).trans hMap, ?_⟩
  simp only [compComparison] at hComp
  rw [stackMorphismInducedComparison_vcomp] at hComp
  simpa only [Iso.trans_assoc, stackPullbackObjIsoOfEq_trans] using hComp

set_option backward.isDefEq.respectTransparency false in
/-- Every compatible map into the proposed composite presenting scheme is the nested lift.
The proof first uses uniqueness for the outer presentation, then uses uniqueness of its
source-object isomorphism before invoking uniqueness for the inner presentation. -/
theorem compLift_unique {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z)
    (b : S ⟶ q.space)
    (e : x ≅ (stackPullback X b).obj q.object)
    (hc : StackMorphismClassifies (Pseudofunctor.StrongTrans.vcomp f g)
      (q.map ≫ p.map) q.object z (p.compComparison q) toBase x c b e) :
    b = p.compLift q toBase x c := by
  let inner :
      (f.appFunctor S).obj x ≅ (stackPullback Y (b ≫ q.map)).obj p.object :=
    stackMorphismInducedComparison f q.map q.object p.object q.comparison b x e
  have hOuter := p.compClassifiesOuter q toBase x c b e hc
  have hIntermediate : b ≫ q.map = p.compIntermediateMap toBase x c :=
    p.lift_unique toBase ((f.appFunctor S).obj x) c (b ≫ q.map) inner hOuter
  let inner' :
      (f.appFunctor S).obj x ≅
        (stackPullback Y (p.compIntermediateMap toBase x c)).obj p.object :=
    inner.trans (stackPullbackObjIsoOfEq Y hIntermediate p.object)
  have hOuter' :
      StackMorphismClassifies g p.map p.object z p.comparison toBase
        ((f.appFunctor S).obj x) c (p.compIntermediateMap toBase x c) inner' :=
    stackMorphismClassifies_changeMap inner inner' hOuter hIntermediate rfl
  have hInner : inner' = p.compIntermediateObjectIso toBase x c :=
    p.liftObjectIso_unique toBase ((f.appFunctor S).obj x) c inner' hOuter'
  have hQ :
      StackMorphismClassifies f q.map q.object p.object q.comparison
        (p.compIntermediateMap toBase x c) x
        (p.compIntermediateObjectIso toBase x c) b e := by
    refine ⟨hIntermediate, ?_⟩
    change inner' = p.compIntermediateObjectIso toBase x c
    exact hInner
  exact q.lift_unique (p.compIntermediateMap toBase x c) x
    (p.compIntermediateObjectIso toBase x c) b e hQ

set_option backward.isDefEq.respectTransparency false in
/-- For the nested lift, the source-object isomorphism is uniquely forced by the composite
comparison.  Both constituent `liftObjectIso_unique` laws are used, so relative stabilizer
arrows are retained rather than collapsed. -/
theorem compLiftObjectIso_unique {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z)
    (e : x ≅ (stackPullback X (p.compLift q toBase x c)).obj q.object)
    (hc : StackMorphismClassifies (Pseudofunctor.StrongTrans.vcomp f g)
      (q.map ≫ p.map) q.object z (p.compComparison q) toBase x c
      (p.compLift q toBase x c) e) :
    e = p.compLiftObjectIso q toBase x c := by
  let b : S ⟶ q.space := p.compLift q toBase x c
  let inner :
      (f.appFunctor S).obj x ≅ (stackPullback Y (b ≫ q.map)).obj p.object :=
    stackMorphismInducedComparison f q.map q.object p.object q.comparison b x e
  have hOuter := p.compClassifiesOuter q toBase x c b e hc
  have hIntermediate : b ≫ q.map = p.compIntermediateMap toBase x c :=
    p.lift_unique toBase ((f.appFunctor S).obj x) c (b ≫ q.map) inner hOuter
  let inner' :
      (f.appFunctor S).obj x ≅
        (stackPullback Y (p.compIntermediateMap toBase x c)).obj p.object :=
    inner.trans (stackPullbackObjIsoOfEq Y hIntermediate p.object)
  have hOuter' :
      StackMorphismClassifies g p.map p.object z p.comparison toBase
        ((f.appFunctor S).obj x) c (p.compIntermediateMap toBase x c) inner' :=
    stackMorphismClassifies_changeMap inner inner' hOuter hIntermediate rfl
  have hInner : inner' = p.compIntermediateObjectIso toBase x c :=
    p.liftObjectIso_unique toBase ((f.appFunctor S).obj x) c inner' hOuter'
  have hQ :
      StackMorphismClassifies f q.map q.object p.object q.comparison
        (p.compIntermediateMap toBase x c) x
        (p.compIntermediateObjectIso toBase x c) b e := by
    refine ⟨hIntermediate, ?_⟩
    change inner' = p.compIntermediateObjectIso toBase x c
    exact hInner
  exact q.liftObjectIso_unique (p.compIntermediateMap toBase x c) x
    (p.compIntermediateObjectIso toBase x c) e hQ

/-- The scheme presentation of a composite stack morphism, constructed from two actual
scheme-valued universal presentations.  No composition theorem is stored in either input:
the comparison, lift, compatibility, and both uniqueness laws are the constructions and
theorems above. -/
noncomputable def comp {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object) :
    StackMorphismPresentation (Pseudofunctor.StrongTrans.vcomp f g) T z where
  space := q.space
  map := q.map ≫ p.map
  object := q.object
  comparison := p.compComparison q
  lift := p.compLift q
  lift_map := p.compLift_map q
  liftObjectIso := p.compLiftObjectIso q
  lift_compatible := p.compLift_compatible q
  liftObjectIso_unique := p.compLiftObjectIso_unique q
  lift_unique := p.compLift_unique q

/-- Any other intermediate map equipped with a compatible pullback isomorphism equals the
constructed intermediate lift. -/
theorem compIntermediateMap_unique {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z)
    (a : S ⟶ p.space)
    (e : (StackHom.appFunctor f S).obj x ≅ (stackPullback Y a).obj p.object)
    (h : StackMorphismClassifies g p.map p.object z p.comparison toBase
      ((StackHom.appFunctor f S).obj x) c a e) :
    a = p.compIntermediateMap toBase x c :=
  p.lift_unique toBase ((StackHom.appFunctor f S).obj x) c a e h

/-- Once the intermediate map and comparison are fixed, any compatible map into the second
presenting scheme equals the nested lift. -/
theorem compLift_uniqueOverIntermediate {T : Scheme.{u}} {z : StackFiber Z T}
    (p : StackMorphismPresentation g T z)
    (q : StackMorphismPresentation f p.space p.object)
    {S : Scheme.{u}} (toBase : S ⟶ T) (x : StackFiber X S)
    (c : (StackHom.appFunctor (Pseudofunctor.StrongTrans.vcomp f g) S).obj x ≅
      (stackPullback Z toBase).obj z)
    (b : S ⟶ q.space)
    (e : x ≅ (stackPullback X b).obj q.object)
    (h : StackMorphismClassifies f q.map q.object p.object q.comparison
      (p.compIntermediateMap toBase x c) x (p.compIntermediateObjectIso toBase x c) b e) :
    b = p.compLift q toBase x c :=
  q.lift_unique (p.compIntermediateMap toBase x c) x
    (p.compIntermediateObjectIso toBase x c) b e h

end StackMorphismPresentation

namespace StackHom

variable {X Y Z : FppfStack.{u}}
  {f : StackHom X Y} {g : StackHom Y Z}

/-- Raw representable scheme-morphism properties stable under scheme composition are stable
under composition of the actual presenting stack morphisms. -/
theorem comp_hasRepresentablePropertyRaw
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition]
    (hf : f.HasRepresentablePropertyRaw P)
    (hg : g.HasRepresentablePropertyRaw P) :
    HasRepresentablePropertyRaw (Pseudofunctor.StrongTrans.vcomp f g) P := by
  intro T z
  obtain ⟨⟨p, hp⟩⟩ := hg T z
  obtain ⟨⟨q, hq⟩⟩ := hf p.space p.object
  exact ⟨⟨p.comp q, P.comp_mem q.map p.map hq hp⟩⟩

/-- Representable scheme-morphism properties stable under scheme composition are stable under
composition of stack morphisms.  For the 2-isomorphism-invariant closure, the two displayed
2-cells are whiskered and composed explicitly before applying the raw theorem. -/
theorem comp_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition]
    (hf : f.HasRepresentableProperty P)
    (hg : g.HasRepresentableProperty P) :
    HasRepresentableProperty (Pseudofunctor.StrongTrans.vcomp f g) P := by
  obtain ⟨f', ⟨ef⟩, hf'⟩ := hf
  obtain ⟨g', ⟨eg⟩, hg'⟩ := hg
  refine ⟨Pseudofunctor.StrongTrans.vcomp f' g',
    ⟨(ef.whiskerRight g).trans (StackIso2.whiskerLeft f' eg)⟩, ?_⟩
  exact comp_hasRepresentablePropertyRaw P hf' hg'

end StackHom

end GromovWitten.AlgebraicGeometry
