/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.PresentationTransport

/-!
# Scheme presentations of stack equivalences

Every base change of a stack equivalence by a scheme object is represented by that same scheme.
This file constructs the complete `StackMorphismPresentation`, including the comparison
coherences and stabilizer-sensitive uniqueness law.  It follows that equivalences have every
multiplicative representable scheme-morphism property.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackEquivalenceData

variable {A B : FppfStack.{u}} (E : StackEquivalenceData A B)

set_option backward.isDefEq.respectTransparency false in
noncomputable def appEquivalence (T : Scheme.{u}) :
    StackFiber A T ≌ StackFiber B T :=
  CategoryTheory.Equivalence.mk
    (E.hom.appFunctor T) (E.inv.appFunctor T)
    (E.homInv.appIso T).symm (E.invHom.appIso T)

noncomputable def homAppFullyFaithful (T : Scheme.{u}) :
    (E.hom.appFunctor T).FullyFaithful :=
  (E.appEquivalence T).fullyFaithfulFunctor

private theorem homPresentation_map_eq
    {S T : Scheme.{u}} (toBase : S ⟶ T) :
    toBase ≫ 𝟙 T = toBase :=
  Category.comp_id _

/-- Universal comparison for the scheme `T` presenting the base change of an
equivalence by `y : B(T)`. -/
noncomputable def homPresentationUniversal
    (T : Scheme.{u}) (y : StackFiber B T) :
    (E.hom.appFunctor T).obj ((E.inv.appFunctor T).obj y) ≅
      (stackPullback B (𝟙 T)).obj y :=
  ((E.invHom.appIso T).app y).trans
    ((Cat.Hom.toNatIso
      (B.toPseudofunctor.mapId
        (LocallyDiscrete.mk (Opposite.op T)))).symm.app y)

/-- Fixed coherence tail from the image of the pulled-back inverse object to
the pulled-back target object. -/
noncomputable def homClassificationTail
    {S T : Scheme.{u}} (toBase : S ⟶ T) (y : StackFiber B T) :
    (E.hom.appFunctor S).obj
        ((stackPullback A toBase).obj ((E.inv.appFunctor T).obj y)) ≅
      (stackPullback B toBase).obj y :=
  ((Cat.Hom.toNatIso (E.hom.naturality ⟨toBase.op⟩)).app
      ((E.inv.appFunctor T).obj y)).trans
    (((stackPullback B toBase).mapIso
      (E.homPresentationUniversal T y)).trans
      ((stackPullbackCompIso B toBase (𝟙 T) y).trans
        (stackPullbackObjIsoOfEq B
          (homPresentation_map_eq toBase) y)))

/-- The unique source-object isomorphism whose image under the equivalence is
the supplied comparison with the fixed coherence tail removed. -/
noncomputable def homClassificationObjectIso
    {S T : Scheme.{u}} (toBase : S ⟶ T) (y : StackFiber B T)
    (x : StackFiber A S)
    (c : (E.hom.appFunctor S).obj x ≅ (stackPullback B toBase).obj y) :
    x ≅ (stackPullback A toBase).obj ((E.inv.appFunctor T).obj y) :=
  (E.homAppFullyFaithful S).preimageIso
    (c.trans (E.homClassificationTail toBase y).symm)

@[simp]
theorem homClassificationObjectIso_map
    {S T : Scheme.{u}} (toBase : S ⟶ T) (y : StackFiber B T)
    (x : StackFiber A S)
    (c : (E.hom.appFunctor S).obj x ≅ (stackPullback B toBase).obj y) :
    (E.hom.appFunctor S).map
        (E.homClassificationObjectIso toBase y x c).hom =
      (c.trans (E.homClassificationTail toBase y).symm).hom := by
  unfold homClassificationObjectIso
  exact (E.homAppFullyFaithful S).map_preimage _

theorem homInducedComparison_eq
    {S T : Scheme.{u}} (toBase : S ⟶ T) (y : StackFiber B T)
    (x : StackFiber A S)
    (objectIso : x ≅
      (stackPullback A toBase).obj ((E.inv.appFunctor T).obj y)) :
    (stackMorphismInducedComparison E.hom (𝟙 T)
        ((E.inv.appFunctor T).obj y) y
        (E.homPresentationUniversal T y) toBase x objectIso).trans
      (stackPullbackObjIsoOfEq B
        (homPresentation_map_eq toBase) y) =
    ((E.hom.appFunctor S).mapIso objectIso).trans
      (E.homClassificationTail toBase y) := by
  unfold stackMorphismInducedComparison homClassificationTail
  simp only [Iso.trans_assoc]

/-- The inverse image of `y` presents the base change of an equivalence by the
scheme object `y`.  The representing scheme is `T` itself. -/
noncomputable def homPresentation
    (T : Scheme.{u}) (y : StackFiber B T) :
    StackMorphismPresentation E.hom T y where
  space := T
  map := 𝟙 T
  object := (E.inv.appFunctor T).obj y
  comparison := E.homPresentationUniversal T y
  lift toBase _ _ := toBase
  lift_map toBase _ _ := homPresentation_map_eq toBase
  liftObjectIso toBase x c := E.homClassificationObjectIso toBase y x c
  lift_compatible toBase x c := by
    refine ⟨homPresentation_map_eq toBase, ?_⟩
    have hcanonical :
        (stackMorphismInducedComparison E.hom (𝟙 T)
          ((E.inv.appFunctor T).obj y) y
          (E.homPresentationUniversal T y) toBase x
          (E.homClassificationObjectIso toBase y x c)).trans
            (stackPullbackObjIsoOfEq B
              (homPresentation_map_eq toBase) y) = c := by
      rw [E.homInducedComparison_eq]
      apply Iso.ext
      simp only [Iso.trans_hom, Functor.mapIso_hom]
      rw [E.homClassificationObjectIso_map]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    convert hcanonical using 1
  liftObjectIso_unique toBase x c objectIso compatible := by
    obtain ⟨mapEq, hcomparison⟩ := compatible
    have hcomparison' :
        (stackMorphismInducedComparison E.hom (𝟙 T)
          ((E.inv.appFunctor T).obj y) y
          (E.homPresentationUniversal T y) toBase x objectIso).trans
            (stackPullbackObjIsoOfEq B
              (homPresentation_map_eq toBase) y) = c := by
      convert hcomparison using 1
    rw [E.homInducedComparison_eq] at hcomparison'
    apply Iso.ext
    apply (E.homAppFullyFaithful _).map_injective
    apply (cancel_mono (E.homClassificationTail toBase y).hom).1
    have hchosen := E.homClassificationObjectIso_map toBase y x c
    rw [hchosen]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    simpa only [Iso.trans_hom, Functor.mapIso_hom] using
      congrArg Iso.hom hcomparison'
  lift_unique _ _ _ l _ compatible := by
    obtain ⟨hl, -⟩ := compatible
    simpa using hl

/-- Reverse a displayed stack equivalence. -/
def symm : StackEquivalenceData B A where
  hom := E.inv
  inv := E.hom
  homInv := E.invHom
  invHom := E.homInv

/-- A stack equivalence is representable by identity scheme maps for every
multiplicative scheme-morphism property. -/
theorem hom_hasRepresentablePropertyRaw
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] :
    E.hom.HasRepresentablePropertyRaw P := by
  intro T y
  exact ⟨⟨E.homPresentation T y, MorphismProperty.id_mem P T⟩⟩

theorem hom_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] :
    E.hom.HasRepresentableProperty P :=
  (StackHom.hasRepresentableProperty_iff_raw P).mpr
    (E.hom_hasRepresentablePropertyRaw P)

theorem inv_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] :
    E.inv.HasRepresentableProperty P :=
  (E.symm).hom_hasRepresentableProperty P

end StackEquivalenceData

end GromovWitten.AlgebraicGeometry
