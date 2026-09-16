/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.TwoPullbackBilimit
import GromovWitten.AlgebraicGeometry.Stacks.EquivalencePresentation

/-!
# Comparison of genuine stack two-pullbacks

Any two genuine bicategorical pullbacks of the same cospan are equivalent.  This file constructs
the two comparison morphisms from the respective bilimit lifts, proves their round trips classify
the identity cones, and derives both inverse 2-cells from bilimit uniqueness.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackIso2

@[simp]
theorem associator_appIso_hom_app
    {A B C D : FppfStack.{u}}
    (f : StackHom A B) (g : StackHom B C) (h : StackHom C D)
    (U : Scheme.{u}) (x : StackFiber A U) :
    ((associator f g h).appIso U).hom.app x = 𝟙 _ := rfl

@[simp]
theorem whiskerLeft_appIso_hom_app
    {A B C : FppfStack.{u}} (q : StackHom A B)
    {f g : StackHom B C} (e : StackIso2 f g)
    (U : Scheme.{u}) (x : StackFiber A U) :
    ((StackIso2.whiskerLeft q e).appIso U).hom.app x =
      (e.appIso U).hom.app ((q.appFunctor U).obj x) := rfl

end StackIso2

namespace StackTwoPullback

variable {X Y Z : FppfStack.{u}} {f : StackHom X Z} {g : StackHom Y Z}

/-- A pullback presentation regarded as a cone over its defining cospan. -/
def selfCone (P : StackTwoPullback f g) : Cone (f := f) (g := g) P.pullback where
  fst := P.fst
  snd := P.snd
  comparison := P.comparison

/-- The identity morphism classifies the self-cone of a pullback presentation. -/
theorem identitySelfConeClassifies (P : StackTwoPullback f g) :
    ConeLiftClassifies P P.selfCone
      (Pseudofunctor.StrongTrans.id P.pullback.toPseudofunctor)
      (StackIso2.leftUnitor P.fst)
      (StackIso2.leftUnitor P.snd) := by
  intro U x
  apply Iso.ext
  change
    (f.appFunctor U).map
          (((StackIso2.leftUnitor P.fst).appIso U).hom.app x) ≫
        (P.comparison.appIso U).hom.app x =
      (P.comparison.appIso U).hom.app
          ((StackHom.appFunctor
            (Pseudofunctor.StrongTrans.id P.pullback.toPseudofunctor) U).obj x) ≫
        (g.appFunctor U).map
          (((StackIso2.leftUnitor P.snd).appIso U).hom.app x)
  rw [leftUnitor_appIso_hom_app, leftUnitor_appIso_hom_app]
  change
    (f.appFunctor U).map (𝟙 ((P.fst.appFunctor U).obj x)) ≫
        (P.comparison.appIso U).hom.app x =
      (P.comparison.appIso U).hom.app x ≫
        (g.appFunctor U).map (𝟙 ((P.snd.appFunctor U).obj x))
  rw [(f.appFunctor U).map_id]
  change
    𝟙 ((StackHom.appFunctor
      (Pseudofunctor.StrongTrans.vcomp P.fst f) U).obj x) ≫
        (P.comparison.appIso U).hom.app x =
      (P.comparison.appIso U).hom.app x ≫
        (g.appFunctor U).map (𝟙 ((P.snd.appFunctor U).obj x))
  erw [(g.appFunctor U).map_id]
  change
    𝟙 ((StackHom.appFunctor
      (Pseudofunctor.StrongTrans.vcomp P.fst f) U).obj x) ≫
        (P.comparison.appIso U).hom.app x =
      (P.comparison.appIso U).hom.app x ≫
        𝟙 ((StackHom.appFunctor
          (Pseudofunctor.StrongTrans.vcomp P.snd g) U).obj x)
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The universal map from one genuine pullback presentation to another. -/
noncomputable def comparisonHom (P Q : Genuine f g) :
    StackHom P.pullback Q.pullback :=
  Q.bilimit.lift P.toStackTwoPullback.selfCone

/-- Projection comparison for the round trip `P → Q → P`. -/
noncomputable def roundTripFstIso (P Q : Genuine f g) : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp (comparisonHom P Q)
        (comparisonHom Q P)) P.fst)
    P.fst :=
  ((StackIso2.associator (comparisonHom P Q) (comparisonHom Q P) P.fst).trans
    (StackIso2.whiskerLeft (comparisonHom P Q)
      (P.bilimit.lift_fst Q.toStackTwoPullback.selfCone))).trans
    (Q.bilimit.lift_fst P.toStackTwoPullback.selfCone)

/-- Second-projection comparison for the round trip `P → Q → P`. -/
noncomputable def roundTripSndIso (P Q : Genuine f g) : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp (comparisonHom P Q)
        (comparisonHom Q P)) P.snd)
    P.snd :=
  ((StackIso2.associator (comparisonHom P Q) (comparisonHom Q P) P.snd).trans
    (StackIso2.whiskerLeft (comparisonHom P Q)
      (P.bilimit.lift_snd Q.toStackTwoPullback.selfCone))).trans
    (Q.bilimit.lift_snd P.toStackTwoPullback.selfCone)

set_option backward.isDefEq.respectTransparency false in
/-- The round trip between two genuine pullbacks classifies the original self-cone. -/
theorem roundTripClassifies (P Q : Genuine f g) :
    ConeLiftClassifies P.toStackTwoPullback P.toStackTwoPullback.selfCone
      (Pseudofunctor.StrongTrans.vcomp (comparisonHom P Q)
        (comparisonHom Q P))
      (roundTripFstIso P Q) (roundTripSndIso P Q) := by
  intro U x
  apply Iso.ext
  have hQ := congrArg Iso.hom
    (Q.bilimit.lift_compatible P.toStackTwoPullback.selfCone U x)
  have hP := congrArg Iso.hom
    (P.bilimit.lift_compatible Q.toStackTwoPullback.selfCone U
      ((comparisonHom P Q).appFunctor U |>.obj x))
  change
    (f.appFunctor U).map
          (((roundTripFstIso P Q).appIso U).hom.app x) ≫
        (P.comparison.appIso U).hom.app x =
      (P.comparison.appIso U).hom.app
          ((StackHom.appFunctor
            (Pseudofunctor.StrongTrans.vcomp (comparisonHom P Q)
              (comparisonHom Q P)) U).obj x) ≫
        (g.appFunctor U).map
          (((roundTripSndIso P Q).appIso U).hom.app x)
  dsimp only [roundTripFstIso, roundTripSndIso, comparisonHom]
  simp only [trans_appIso_hom_app,
    StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app,
    Functor.map_comp, Category.id_comp,
    Category.assoc]
  change
    (f.appFunctor U).map
          (((P.bilimit.lift_fst Q.toStackTwoPullback.selfCone).appIso U).hom.app
            ((comparisonHom P Q).appFunctor U |>.obj x)) ≫
        (f.appFunctor U).map
          (((Q.bilimit.lift_fst P.toStackTwoPullback.selfCone).appIso U).hom.app x) ≫
        (P.comparison.appIso U).hom.app x =
      (P.comparison.appIso U).hom.app
          ((comparisonHom Q P).appFunctor U |>.obj
            ((comparisonHom P Q).appFunctor U |>.obj x)) ≫
        (g.appFunctor U).map
          (((P.bilimit.lift_snd Q.toStackTwoPullback.selfCone).appIso U).hom.app
            ((comparisonHom P Q).appFunctor U |>.obj x)) ≫
        (g.appFunctor U).map
          (((Q.bilimit.lift_snd P.toStackTwoPullback.selfCone).appIso U).hom.app x)
  change
    (f.appFunctor U).map
          (((Q.bilimit.lift_fst P.toStackTwoPullback.selfCone).appIso U).hom.app x) ≫
        (P.comparison.appIso U).hom.app x =
      (Q.comparison.appIso U).hom.app
          ((comparisonHom P Q).appFunctor U |>.obj x) ≫
        (g.appFunctor U).map
          (((Q.bilimit.lift_snd P.toStackTwoPullback.selfCone).appIso U).hom.app x) at hQ
  change
    (f.appFunctor U).map
          (((P.bilimit.lift_fst Q.toStackTwoPullback.selfCone).appIso U).hom.app
            ((comparisonHom P Q).appFunctor U |>.obj x)) ≫
        (Q.comparison.appIso U).hom.app
          ((comparisonHom P Q).appFunctor U |>.obj x) =
      (P.comparison.appIso U).hom.app
          ((comparisonHom Q P).appFunctor U |>.obj
            ((comparisonHom P Q).appFunctor U |>.obj x)) ≫
        (g.appFunctor U).map
          (((P.bilimit.lift_snd Q.toStackTwoPullback.selfCone).appIso U).hom.app
            ((comparisonHom P Q).appFunctor U |>.obj x)) at hP
  erw [hQ]
  rw [reassoc_of% hP]

/-- The universal round trip is 2-isomorphic to the identity. Both legs are compared with the
same universal lift of the self-cone. -/
noncomputable def roundTripIso (P Q : Genuine f g) : StackIso2
    (Pseudofunctor.StrongTrans.vcomp (comparisonHom P Q)
      (comparisonHom Q P))
    (Pseudofunctor.StrongTrans.id P.pullback.toPseudofunctor) :=
  (P.bilimit.lift_unique P.toStackTwoPullback.selfCone
    (Pseudofunctor.StrongTrans.vcomp (comparisonHom P Q)
      (comparisonHom Q P))
    (roundTripFstIso P Q) (roundTripSndIso P Q)
    (roundTripClassifies P Q)).trans
  (P.bilimit.lift_unique P.toStackTwoPullback.selfCone
    (Pseudofunctor.StrongTrans.id P.pullback.toPseudofunctor)
    (StackIso2.leftUnitor P.fst) (StackIso2.leftUnitor P.snd)
    (identitySelfConeClassifies P.toStackTwoPullback)).symm

/-- Any two genuine two-pullback presentations of the same cospan are equivalent, with the
comparison maps and inverse laws constructed from their bilimit universal properties. -/
noncomputable def presentationEquivalence (P Q : Genuine f g) :
    StackEquivalenceData P.pullback Q.pullback where
  hom := comparisonHom P Q
  inv := comparisonHom Q P
  homInv := roundTripIso P Q
  invHom := roundTripIso Q P

end StackTwoPullback

end GromovWitten.AlgebraicGeometry
