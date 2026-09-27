/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.PresentationGroupoidObject

/-!
# The groupoid-object laws of a presentation groupoid

Let `f : StackHom U X` be an atlas and `R : Genuine f f` a genuine self two-pullback, so that
`R.pullback` presents `U ×_X U` and `Stacks.AtlasRefinement` equips `R.pullback ⇉ U` with source,
target, unit, composition and inversion maps.  This file proves the five remaining
two-dimensional groupoid-object laws, each as a `StackIso2` between stack morphisms:

* `Genuine.unit_compose_right` : `rightUnitPair ≫ compose ≅ 𝟙`, i.e. `g ∘ id_{target g} ≅ g`;
* `Genuine.unit_compose_left` : `leftUnitPair ≫ compose ≅ 𝟙`, i.e. `id_{source g} ∘ g ≅ g`;
* `Genuine.inverse_compose_right` : `invPairRight ≫ compose ≅ source ≫ unit`, i.e.
  `g⁻¹ ∘ g ≅ id_{source g}` in the convention where `compose` composes `(g, g⁻¹)`;
* `Genuine.inverse_compose_left` : `invPairLeft ≫ compose ≅ target ≫ unit`;
* `Genuine.compose_assoc` : `assocLeftPair ≫ compose ≅ assocRightPair ≫ compose`, associativity
  on the stack `composable3.pullback` of triples of composable arrows.

Together with `Genuine.inverse_inverse` of `Stacks.PresentationGroupoidObject` these are all the
groupoid-object identities of the presentation groupoid at the level of stack 2-cells.

A final section ties the stack-level structure maps of the *canonical* self two-pullback to the
fibrewise groupoid `PresentationGroupoid f T` of `Stacks.AtlasRefinement`: `unit`, `compose` and
`inverse` act on the fibre over a test scheme `T` as the identity, the composition and the
inverse of that groupoid (`PresentationGroupoid.unit_agrees`,
`PresentationGroupoid.compose_agrees`, `PresentationGroupoid.inverse_agrees`).

## Construction

Every law is proved by the same three-step pattern.

1. The composable pair entering the law (`(g, id)`, `(id, g)`, `(g, g⁻¹)`, `(g⁻¹, g)`,
   `(g₁g₂, g₃)`, `(g₁, g₂g₃)`) is produced as a lift through the universal property of
   `R.composable` (the stack of composable pairs) of an explicitly built cone, whose comparison
   face encodes the composability of the pair.
2. Both sides of the law are shown to classify one and the same cone over the cospan `f, f`
   — `R.selfCone` for the unit laws, the constant cone `unitConeOf` for the inverse laws, and
   `assocCone` for associativity — projections *and* comparison face.  The comparison face is
   the only real content; it is isolated as a diagram chase in an arbitrary category
   (`rightUnitSquare`, `leftUnitSquare`, `invRightSquare`, `invLeftSquare`, `assocLeftSquare`,
   `assocRightSquare`), so that the fibrewise computation is a purely formal rewrite and the
   only definitional unfolding happens when the abstract lemma is applied.
3. `R.bilimit.lift_unique` is applied twice, comparing both sides with the universal lift of
   that cone, exactly as `Stacks.BilimitComparison` compares two genuine presentations.

The fibre components of all the composite 2-cells involved are computed by dedicated
`…_appIso_hom_app` lemmas: the bicategorical operations on `StackIso2`s compute on fibre
components by definitional unfolding, and only the resulting identity arrows need the generic
cancellation lemmas of the first section.

The triple-composable stack used for associativity, `Genuine.composable3`, is the genuine two
pullback of the outer target `R.composable.pullback ⟶ U` of a composable pair against the source
`R.pullback ⟶ U`; it is obtained by iterating the very construction that produces
`R.composable` from `R`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackTwoPullback

namespace Genuine

variable {U X : FppfStack.{u}} {f : StackHom U X}

/-! ### Fibre components of composite 2-cells

All the bicategorical operations on `StackIso2`s compute on fibre components by definitional
unfolding.  The facts below are the ones missing from `Stacks.TwoPullback` and
`Stacks.BilimitComparison`; they are deliberately not `simp` lemmas, and are instead listed
explicitly in the `simp only` calls of this file. -/

/-- The fibre components of the identity 2-cell are identities. -/
theorem refl_appIso_hom_app {A B : FppfStack.{u}} (p : StackHom A B) (V : Scheme.{u})
    (x : StackFiber A V) :
    ((StackIso2.refl p).appIso V).hom.app x = 𝟙 _ := rfl

/-- The `hom` components of a reversed 2-cell are the `inv` components of the original. -/
theorem symm_appIso_hom_app {A B : FppfStack.{u}} {p q : StackHom A B} (e : StackIso2 p q)
    (V : Scheme.{u}) (x : StackFiber A V) :
    ((e.symm).appIso V).hom.app x = (e.appIso V).inv.app x := rfl

/-- The `inv` components of a transitivity composite. -/
theorem trans_appIso_inv_app {A B : FppfStack.{u}} {p q r : StackHom A B} (e : StackIso2 p q)
    (e' : StackIso2 q r) (V : Scheme.{u}) (x : StackFiber A V) :
    ((e.trans e').appIso V).inv.app x =
      (e'.appIso V).inv.app x ≫ (e.appIso V).inv.app x := rfl

/-- The `inv` components of an associator are identities. -/
theorem associator_appIso_inv_app {A B C D : FppfStack.{u}} (p : StackHom A B)
    (q : StackHom B C) (r : StackHom C D) (V : Scheme.{u}) (x : StackFiber A V) :
    ((StackIso2.associator p q r).appIso V).inv.app x = 𝟙 _ := rfl

/-- The `inv` components of a left whiskering. -/
theorem whiskerLeft_appIso_inv_app {A B C : FppfStack.{u}} (q : StackHom A B)
    {p p' : StackHom B C} (e : StackIso2 p p') (V : Scheme.{u}) (x : StackFiber A V) :
    ((StackIso2.whiskerLeft q e).appIso V).inv.app x =
      (e.appIso V).inv.app ((q.appFunctor V).obj x) := rfl

/-! The intermediate objects of the composites below agree only definitionally, so `simp` cannot
apply `Category.id_comp`/`Category.comp_id` to them.  The following statements in an arbitrary
category are applied through definitional unfolding instead, exactly as in
`Stacks/InertiaCoherence.lean`. -/

/-- Cancelling a trailing identity, in an arbitrary category. -/
theorem eq_of_comp_id {W : Type*} [Category W] {a b : W} (u v : a ⟶ b)
    (h : u ≫ 𝟙 b = v) : u = v := by simpa using h

/-- Cancelling an interior identity after two factors, in an arbitrary category. -/
theorem comp_comp_idComp {W : Type*} [Category W] {a b c d : W} (u : a ⟶ b) (w : b ⟶ c)
    (v : c ⟶ d) : u ≫ w ≫ 𝟙 c ≫ v = u ≫ w ≫ v := by simp

/-- Cancelling an interior identity after one factor, in an arbitrary category. -/
theorem comp_idComp {W : Type*} [Category W] {a b c : W} (u : a ⟶ b) (v : b ⟶ c) :
    u ≫ 𝟙 b ≫ v = u ≫ v := by simp

/-- Cancelling two interior identities, in an arbitrary category. -/
theorem comp_idComp_comp_comp_idComp {W : Type*} [Category W] {a b c d e : W} (u : a ⟶ b)
    (v : b ⟶ c) (w : c ⟶ d) (z : d ⟶ e) : u ≫ 𝟙 b ≫ v ≫ w ≫ 𝟙 d ≫ z = u ≫ v ≫ w ≫ z := by
  simp

/-- Cancelling an interior identity and a trailing one, in an arbitrary category. -/
theorem comp_idComp_comp_id {W : Type*} [Category W] {a b c : W} (u : a ⟶ b) (v : b ⟶ c) :
    u ≫ 𝟙 b ≫ v ≫ 𝟙 c = u ≫ v := by simp

/-- Cancelling an interior and a trailing identity, in an arbitrary category. -/
theorem comp_idComp_comp_comp_id {W : Type*} [Category W] {a b c d : W} (u : a ⟶ b)
    (v : b ⟶ c) (w : c ⟶ d) : u ≫ 𝟙 b ≫ v ≫ w ≫ 𝟙 d = u ≫ v ≫ w := by simp

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the tautological 2-cell of a presentation groupoid.**  The comparison
2-cell of a self two-pullback is a modification, hence natural in the fibre variable. -/
theorem comparison_naturality (R : Genuine f f) (V : Scheme.{u})
    {a b : StackFiber R.pullback V} (h : a ⟶ b) :
    (f.appFunctor V).map ((R.fst.appFunctor V).map h) ≫
        (R.comparison.appIso V).hom.app b =
      (R.comparison.appIso V).hom.app a ≫
        (f.appFunctor V).map ((R.snd.appFunctor V).map h) :=
  (R.comparison.appIso V).hom.naturality h

set_option backward.isDefEq.respectTransparency false in
/-- **The unit arrow is an actual identity.**  The comparison face of the cone classified by
the unit section says that the image under the atlas of the source triviality of the unit is
the tautological 2-cell at the unit arrow followed by the image of its target triviality. -/
theorem unit_comparison (R : Genuine f f) (V : Scheme.{u}) (z : StackFiber U V) :
    (f.appFunctor V).map ((R.unit_source.appIso V).hom.app z) =
      (R.comparison.appIso V).hom.app ((R.unit.appFunctor V).obj z) ≫
        (f.appFunctor V).map ((R.unit_target.appIso V).hom.app z) := by
  have h := congrArg Iso.hom (R.relativeDiagonalClassifies V z)
  change
    (f.appFunctor V).map ((R.unit_source.appIso V).hom.app z) ≫
        ((StackIso2.refl (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.id U.toPseudofunctor) f)).appIso V).hom.app z =
      (R.comparison.appIso V).hom.app ((R.unit.appFunctor V).obj z) ≫
        (f.appFunctor V).map ((R.unit_target.appIso V).hom.app z) at h
  rw [refl_appIso_hom_app] at h
  exact eq_of_comp_id _ _ h

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face of the composition cone, on fibre components.**  It is the
tautological 2-cell at the first arrow, followed by the image under the atlas of the
composability 2-cell, followed by the tautological 2-cell at the second arrow. -/
theorem composeConeComparison_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (y : StackFiber R.composable.pullback V) :
    (R.composeConeComparison.appIso V).hom.app y =
      (R.comparison.appIso V).hom.app ((R.firstArrow.appFunctor V).obj y) ≫
        (f.appFunctor V).map ((R.composableComparison.appIso V).hom.app y) ≫
          (R.comparison.appIso V).hom.app ((R.secondArrow.appFunctor V).obj y) := by
  dsimp only [composeConeComparison]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app,
    symm_appIso_hom_app, associator_appIso_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc]
  exact comp_comp_idComp _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face of the right-unit pairing cone, on fibre components.**  It is the
inverse of the source triviality of the unit, at the target of the given arrow. -/
theorem rightUnitPairComparison_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.rightUnitPairComparison.appIso V).hom.app x =
      (R.unit_source.appIso V).inv.app ((R.target.appFunctor V).obj x) := by
  dsimp only [rightUnitPairComparison]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackTwoPullback.leftUnitor_appIso_hom_app,
    symm_appIso_hom_app, trans_appIso_inv_app, StackTwoPullback.rightUnitor_appIso_inv_app,
    whiskerLeft_appIso_inv_app, associator_appIso_inv_app, Category.id_comp, Category.comp_id]

/-! ### The right unit law -/

/-- The source comparison of the right-unit composite: composing an arrow with the identity
arrow at its target does not change its source. -/
noncomputable def rightUnitFstIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.rightUnitPair R.compose) R.fst) R.fst :=
  (((StackIso2.associator R.rightUnitPair R.compose R.fst).trans
    (StackIso2.whiskerLeft R.rightUnitPair R.compose_source)).trans
      (StackIso2.associator R.rightUnitPair R.firstArrow R.fst).symm).trans
        ((StackIso2.whiskerRight R.rightUnitPair_firstArrow R.fst).trans
          (StackIso2.leftUnitor R.fst))

/-- The target comparison of the right-unit composite: composing an arrow with the identity
arrow at its target does not change its target. -/
noncomputable def rightUnitSndIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.rightUnitPair R.compose) R.snd) R.snd :=
  (((StackIso2.associator R.rightUnitPair R.compose R.snd).trans
    (StackIso2.whiskerLeft R.rightUnitPair R.compose_target)).trans
      (StackIso2.associator R.rightUnitPair R.secondArrow R.snd).symm).trans
        ((StackIso2.whiskerRight R.rightUnitPair_secondArrow R.snd).trans
          ((StackIso2.associator R.target R.unit R.snd).trans
            ((StackIso2.whiskerLeft R.target R.unit_target).trans
              (StackIso2.rightUnitor R.target))))

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `rightUnitFstIso`. -/
theorem rightUnitFstIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.rightUnitFstIso.appIso V).hom.app x =
      (R.compose_source.appIso V).hom.app ((R.rightUnitPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.rightUnitPair_firstArrow.appIso V).hom.app x) := by
  dsimp only [rightUnitFstIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, StackTwoPullback.leftUnitor_appIso_hom_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  exact comp_idComp _ _

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `rightUnitSndIso`. -/
theorem rightUnitSndIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.rightUnitSndIso.appIso V).hom.app x =
      (R.compose_target.appIso V).hom.app ((R.rightUnitPair.appFunctor V).obj x) ≫
        (R.snd.appFunctor V).map ((R.rightUnitPair_secondArrow.appIso V).hom.app x) ≫
          (R.unit_target.appIso V).hom.app ((R.target.appFunctor V).obj x) := by
  dsimp only [rightUnitSndIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, Category.id_comp, Category.assoc]
  exact comp_idComp_comp_comp_id _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face classified by the composition map, on fibre components.** -/
theorem compose_comparison (R : Genuine f f) (V : Scheme.{u})
    (y : StackFiber R.composable.pullback V) :
    (f.appFunctor V).map ((R.compose_source.appIso V).hom.app y) ≫
        (R.comparison.appIso V).hom.app ((R.firstArrow.appFunctor V).obj y) ≫
          (f.appFunctor V).map ((R.composableComparison.appIso V).hom.app y) ≫
            (R.comparison.appIso V).hom.app ((R.secondArrow.appFunctor V).obj y) =
      (R.comparison.appIso V).hom.app ((R.compose.appFunctor V).obj y) ≫
        (f.appFunctor V).map ((R.compose_target.appIso V).hom.app y) := by
  have h := congrArg Iso.hom (R.compose_classifies V y)
  change
    (f.appFunctor V).map ((R.compose_source.appIso V).hom.app y) ≫
        (R.composeConeComparison.appIso V).hom.app y =
      (R.comparison.appIso V).hom.app ((R.compose.appFunctor V).obj y) ≫
        (f.appFunctor V).map ((R.compose_target.appIso V).hom.app y) at h
  rw [composeConeComparison_appIso_hom_app] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face classified by the right-unit pairing map, on fibre components.** -/
theorem rightUnitPair_comparison (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.snd.appFunctor V).map ((R.rightUnitPair_firstArrow.appIso V).hom.app x) ≫
        (R.unit_source.appIso V).inv.app ((R.target.appFunctor V).obj x) =
      (R.composableComparison.appIso V).hom.app ((R.rightUnitPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.rightUnitPair_secondArrow.appIso V).hom.app x) := by
  have h := congrArg Iso.hom (R.rightUnitPair_classifies V x)
  change
    (R.snd.appFunctor V).map ((R.rightUnitPair_firstArrow.appIso V).hom.app x) ≫
        (R.rightUnitPairComparison.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.rightUnitPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.rightUnitPair_secondArrow.appIso V).hom.app x) at h
  rw [rightUnitPairComparison_appIso_hom_app] at h
  exact h

/-- Cancelling a pair of mutually inverse arrows after a two-factor composite, in an arbitrary
category. -/
theorem eq_comp_comp_of_comp_inv {W : Type*} [Category W] {a b c d : W} (u : a ⟶ c) (i : c ⟶ d)
    (j : d ⟶ c) (v : a ⟶ b) (w : b ⟶ d) (hij : i ≫ j = 𝟙 c) (h : u ≫ i = v ≫ w) :
    u = v ≫ w ≫ j := by
  rw [← Category.assoc, ← h, Category.assoc, hij, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The target-side identification supplied by the right-unit pairing map: the image of its
first projection cell under the target map factors through the composability 2-cell. -/
theorem rightUnitPair_snd_eq (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.snd.appFunctor V).map ((R.rightUnitPair_firstArrow.appIso V).hom.app x) =
      (R.composableComparison.appIso V).hom.app ((R.rightUnitPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.rightUnitPair_secondArrow.appIso V).hom.app x) ≫
          (R.unit_source.appIso V).hom.app ((R.target.appFunctor V).obj x) :=
  eq_comp_comp_of_comp_inv _ _ _ _ _ ((R.unit_source.appIso V).inv_hom_id_app _)
    (R.rightUnitPair_comparison V x)

/-- **The diagram chase behind the right unit law**, stated in an arbitrary category so that the
only definitional unfolding needed is in the application of this lemma.  `F` plays the role of
the atlas on a test fibre, the `cmp` arrows the role of the tautological 2-cell of the
presentation groupoid at the various arrows involved. -/
theorem rightUnitSquare {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {s₁ s₂ s₃ u₁ v₁ v₂ t₁ t₂ t₃ zz : C}
    {cs : s₁ ⟶ s₂} {fa : s₂ ⟶ s₃} {ct : t₁ ⟶ t₂} {fb : t₂ ⟶ t₃} {ut : t₃ ⟶ zz}
    {ta : u₁ ⟶ zz} {cc : u₁ ⟶ v₁} {sb : v₁ ⟶ v₂} {us : v₂ ⟶ zz}
    {cmpx : F.obj s₃ ⟶ F.obj zz} {cmp1 : F.obj s₂ ⟶ F.obj u₁}
    {cmp2 : F.obj v₁ ⟶ F.obj t₂} {cmpu : F.obj v₂ ⟶ F.obj t₃}
    {cmpc : F.obj s₁ ⟶ F.obj t₁}
    (hA : F.map cs ≫ cmp1 ≫ F.map cc ≫ cmp2 = cmpc ≫ F.map ct)
    (hB : ta = cc ≫ sb ≫ us)
    (hU : F.map us = cmpu ≫ F.map ut)
    (ha : F.map fa ≫ cmpx = cmp1 ≫ F.map ta)
    (hb : F.map sb ≫ cmpu = cmp2 ≫ F.map fb) :
    F.map (cs ≫ fa) ≫ cmpx = cmpc ≫ F.map (ct ≫ fb ≫ ut) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [ha, hB]
  simp only [Functor.map_comp]
  rw [hU, reassoc_of% hb, reassoc_of% hA]

set_option backward.isDefEq.respectTransparency false in
/-- **The right-unit composite classifies the self-cone of `R`.**  Composing an arrow with the
identity arrow at its target reproduces the arrow, projections *and* comparison face. -/
theorem rightUnitClassifies (R : Genuine f f) :
    ConeLiftClassifies R.toStackTwoPullback R.toStackTwoPullback.selfCone
      (Pseudofunctor.StrongTrans.vcomp R.rightUnitPair R.compose)
      R.rightUnitFstIso R.rightUnitSndIso := by
  intro V x
  apply Iso.ext
  change
    (f.appFunctor V).map ((R.rightUnitFstIso.appIso V).hom.app x) ≫
        (R.comparison.appIso V).hom.app x =
      (R.comparison.appIso V).hom.app
          ((R.compose.appFunctor V).obj ((R.rightUnitPair.appFunctor V).obj x)) ≫
        (f.appFunctor V).map ((R.rightUnitSndIso.appIso V).hom.app x)
  rw [rightUnitFstIso_appIso_hom_app, rightUnitSndIso_appIso_hom_app]
  exact rightUnitSquare (R.compose_comparison V ((R.rightUnitPair.appFunctor V).obj x))
    (R.rightUnitPair_snd_eq V x) (R.unit_comparison V ((R.target.appFunctor V).obj x))
    (R.comparison_naturality V
      (a := (R.firstArrow.appFunctor V).obj ((R.rightUnitPair.appFunctor V).obj x)) (b := x)
      ((R.rightUnitPair_firstArrow.appIso V).hom.app x))
    (R.comparison_naturality V
      (a := (R.secondArrow.appFunctor V).obj ((R.rightUnitPair.appFunctor V).obj x))
      (b := (R.unit.appFunctor V).obj ((R.target.appFunctor V).obj x))
      ((R.rightUnitPair_secondArrow.appIso V).hom.app x))

/-- **The right unit law of the presentation groupoid.**  Composing an arrow with the identity
arrow at its target is 2-isomorphic to the identity of the arrow stack: the pairing map
`rightUnitPair` followed by `compose` is 2-isomorphic to the identity of `R.pullback`. -/
noncomputable def unit_compose_right (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.rightUnitPair R.compose)
      (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) :=
  (R.bilimit.lift_unique R.toStackTwoPullback.selfCone
      (Pseudofunctor.StrongTrans.vcomp R.rightUnitPair R.compose)
      R.rightUnitFstIso R.rightUnitSndIso R.rightUnitClassifies).trans
    (R.bilimit.lift_unique R.toStackTwoPullback.selfCone
      (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor)
      (StackIso2.leftUnitor R.fst) (StackIso2.leftUnitor R.snd)
      (identitySelfConeClassifies R.toStackTwoPullback)).symm

/-! ### The left unit law -/

/-- The comparison 2-cell of the cone pairing the identity arrow at the source of an arrow with
the arrow itself. -/
noncomputable def leftUnitPairComparison (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.source R.unit) R.target)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) R.source) :=
  (StackIso2.associator R.source R.unit R.target).trans
    ((StackIso2.whiskerLeft R.source R.unit_target).trans
      ((StackIso2.rightUnitor R.source).trans (StackIso2.leftUnitor R.source).symm))

/-- The cone, over `R.pullback`, of the composable pair `(unit (source g), g)`. -/
noncomputable def leftUnitPairCone (R : Genuine f f) :
    Cone (f := R.target) (g := R.source) R.pullback where
  fst := Pseudofunctor.StrongTrans.vcomp R.source R.unit
  snd := Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor
  comparison := R.leftUnitPairComparison

/-- The map `R.pullback ⟶ R.composable.pullback` pairing the identity arrow at the source of an
arrow with the arrow itself. -/
noncomputable def leftUnitPair (R : Genuine f f) :
    StackHom R.pullback R.composable.pullback :=
  R.composable.bilimit.lift R.leftUnitPairCone

/-- The first projection of the left-unit pairing map is the identity arrow at the source. -/
noncomputable def leftUnitPair_firstArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.leftUnitPair R.firstArrow)
      (Pseudofunctor.StrongTrans.vcomp R.source R.unit) :=
  R.composable.bilimit.lift_fst R.leftUnitPairCone

/-- The second projection of the left-unit pairing map is the identity. -/
noncomputable def leftUnitPair_secondArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.leftUnitPair R.secondArrow)
      (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) :=
  R.composable.bilimit.lift_snd R.leftUnitPairCone

/-- The left-unit pairing map classifies its defining cone completely. -/
theorem leftUnitPair_classifies (R : Genuine f f) :
    ConeLiftClassifies R.composable.toStackTwoPullback R.leftUnitPairCone R.leftUnitPair
      R.leftUnitPair_firstArrow R.leftUnitPair_secondArrow :=
  R.composable.bilimit.lift_compatible R.leftUnitPairCone

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face of the left-unit pairing cone, on fibre components.** -/
theorem leftUnitPairComparison_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.leftUnitPairComparison.appIso V).hom.app x =
      (R.unit_target.appIso V).hom.app ((R.source.appFunctor V).obj x) := by
  dsimp only [leftUnitPairComparison]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, symm_appIso_hom_app,
    StackTwoPullback.leftUnitor_appIso_inv_app, Category.id_comp, Category.comp_id]
  exact Category.comp_id _

/-- The source comparison of the left-unit composite. -/
noncomputable def leftUnitFstIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.leftUnitPair R.compose) R.fst) R.fst :=
  (((StackIso2.associator R.leftUnitPair R.compose R.fst).trans
    (StackIso2.whiskerLeft R.leftUnitPair R.compose_source)).trans
      (StackIso2.associator R.leftUnitPair R.firstArrow R.fst).symm).trans
        ((StackIso2.whiskerRight R.leftUnitPair_firstArrow R.fst).trans
          ((StackIso2.associator R.source R.unit R.fst).trans
            ((StackIso2.whiskerLeft R.source R.unit_source).trans
              (StackIso2.rightUnitor R.source))))

/-- The target comparison of the left-unit composite. -/
noncomputable def leftUnitSndIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.leftUnitPair R.compose) R.snd) R.snd :=
  (((StackIso2.associator R.leftUnitPair R.compose R.snd).trans
    (StackIso2.whiskerLeft R.leftUnitPair R.compose_target)).trans
      (StackIso2.associator R.leftUnitPair R.secondArrow R.snd).symm).trans
        ((StackIso2.whiskerRight R.leftUnitPair_secondArrow R.snd).trans
          (StackIso2.leftUnitor R.snd))

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `leftUnitFstIso`. -/
theorem leftUnitFstIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.leftUnitFstIso.appIso V).hom.app x =
      (R.compose_source.appIso V).hom.app ((R.leftUnitPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.leftUnitPair_firstArrow.appIso V).hom.app x) ≫
          (R.unit_source.appIso V).hom.app ((R.source.appFunctor V).obj x) := by
  dsimp only [leftUnitFstIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, Category.id_comp, Category.assoc]
  exact comp_idComp_comp_comp_id _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `leftUnitSndIso`. -/
theorem leftUnitSndIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.leftUnitSndIso.appIso V).hom.app x =
      (R.compose_target.appIso V).hom.app ((R.leftUnitPair.appFunctor V).obj x) ≫
        (R.snd.appFunctor V).map ((R.leftUnitPair_secondArrow.appIso V).hom.app x) := by
  dsimp only [leftUnitSndIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, StackTwoPullback.leftUnitor_appIso_hom_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  exact comp_idComp _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face classified by the left-unit pairing map, on fibre components.** -/
theorem leftUnitPair_comparison (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.snd.appFunctor V).map ((R.leftUnitPair_firstArrow.appIso V).hom.app x) ≫
        (R.unit_target.appIso V).hom.app ((R.source.appFunctor V).obj x) =
      (R.composableComparison.appIso V).hom.app ((R.leftUnitPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.leftUnitPair_secondArrow.appIso V).hom.app x) := by
  have h := congrArg Iso.hom (R.leftUnitPair_classifies V x)
  change
    (R.snd.appFunctor V).map ((R.leftUnitPair_firstArrow.appIso V).hom.app x) ≫
        (R.leftUnitPairComparison.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.leftUnitPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.leftUnitPair_secondArrow.appIso V).hom.app x) at h
  rw [leftUnitPairComparison_appIso_hom_app] at h
  exact h

/-- **The diagram chase behind the left unit law**, stated in an arbitrary category. -/
theorem leftUnitSquare {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {s₁ s₂ s₃ u₁ u₂ v₁ t₁ t₂ t₃ zz : C}
    {cs : s₁ ⟶ s₂} {sa : s₂ ⟶ s₃} {us : s₃ ⟶ zz} {ct : t₁ ⟶ t₂} {tb : t₂ ⟶ t₃}
    {ta : u₁ ⟶ u₂} {ut : u₂ ⟶ zz} {cc : u₁ ⟶ v₁} {sb : v₁ ⟶ zz}
    {cmpx : F.obj zz ⟶ F.obj t₃} {cmp1 : F.obj s₂ ⟶ F.obj u₁}
    {cmp2 : F.obj v₁ ⟶ F.obj t₂} {cmpu : F.obj s₃ ⟶ F.obj u₂}
    {cmpc : F.obj s₁ ⟶ F.obj t₁}
    (hA : F.map cs ≫ cmp1 ≫ F.map cc ≫ cmp2 = cmpc ≫ F.map ct)
    (hB : ta ≫ ut = cc ≫ sb)
    (hU : F.map us = cmpu ≫ F.map ut)
    (ha : F.map sa ≫ cmpu = cmp1 ≫ F.map ta)
    (hb : F.map sb ≫ cmpx = cmp2 ≫ F.map tb) :
    F.map (cs ≫ sa ≫ us) ≫ cmpx = cmpc ≫ F.map (ct ≫ tb) := by
  have hB' : F.map ta ≫ F.map ut = F.map cc ≫ F.map sb := by
    rw [← Functor.map_comp, ← Functor.map_comp, hB]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hU, reassoc_of% ha, reassoc_of% hB', hb, reassoc_of% hA]

set_option backward.isDefEq.respectTransparency false in
/-- **The left-unit composite classifies the self-cone of `R`.** -/
theorem leftUnitClassifies (R : Genuine f f) :
    ConeLiftClassifies R.toStackTwoPullback R.toStackTwoPullback.selfCone
      (Pseudofunctor.StrongTrans.vcomp R.leftUnitPair R.compose)
      R.leftUnitFstIso R.leftUnitSndIso := by
  intro V x
  apply Iso.ext
  change
    (f.appFunctor V).map ((R.leftUnitFstIso.appIso V).hom.app x) ≫
        (R.comparison.appIso V).hom.app x =
      (R.comparison.appIso V).hom.app
          ((R.compose.appFunctor V).obj ((R.leftUnitPair.appFunctor V).obj x)) ≫
        (f.appFunctor V).map ((R.leftUnitSndIso.appIso V).hom.app x)
  rw [leftUnitFstIso_appIso_hom_app, leftUnitSndIso_appIso_hom_app]
  exact leftUnitSquare (R.compose_comparison V ((R.leftUnitPair.appFunctor V).obj x))
    (R.leftUnitPair_comparison V x) (R.unit_comparison V ((R.source.appFunctor V).obj x))
    (R.comparison_naturality V
      (a := (R.firstArrow.appFunctor V).obj ((R.leftUnitPair.appFunctor V).obj x))
      (b := (R.unit.appFunctor V).obj ((R.source.appFunctor V).obj x))
      ((R.leftUnitPair_firstArrow.appIso V).hom.app x))
    (R.comparison_naturality V
      (a := (R.secondArrow.appFunctor V).obj ((R.leftUnitPair.appFunctor V).obj x)) (b := x)
      ((R.leftUnitPair_secondArrow.appIso V).hom.app x))

/-- **The left unit law of the presentation groupoid.**  Composing the identity arrow at the
source of an arrow with the arrow is 2-isomorphic to the identity of the arrow stack. -/
noncomputable def unit_compose_left (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.leftUnitPair R.compose)
      (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) :=
  (R.bilimit.lift_unique R.toStackTwoPullback.selfCone
      (Pseudofunctor.StrongTrans.vcomp R.leftUnitPair R.compose)
      R.leftUnitFstIso R.leftUnitSndIso R.leftUnitClassifies).trans
    (R.bilimit.lift_unique R.toStackTwoPullback.selfCone
      (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor)
      (StackIso2.leftUnitor R.fst) (StackIso2.leftUnitor R.snd)
      (identitySelfConeClassifies R.toStackTwoPullback)).symm

/-! ### The constant cone classified by a unit arrow -/

/-- Cancelling a trailing identity presented as an abstract arrow, in an arbitrary category. -/
theorem comp_eq_of_eq_id {W : Type*} [Category W] {a b : W} (u v : a ⟶ b) (e : b ⟶ b)
    (he : e = 𝟙 b) (h : u = v) : u ≫ e = v := by rw [he, Category.comp_id, h]

/-- The constant cone at a morphism `q : T ⟶ U`, with identity comparison face: it is the cone
classified by the unit arrow of `q`, since the unit arrow has trivial source and target. -/
noncomputable def unitConeOf (_R : Genuine f f) {T : FppfStack.{u}} (q : StackHom T U) :
    Cone (f := f) (g := f) T where
  fst := q
  snd := q
  comparison := StackIso2.refl (Pseudofunctor.StrongTrans.vcomp q f)

/-- The source comparison of a unit arrow: `(q ≫ unit) ≫ source ≅ q`. -/
noncomputable def unitPostcompFstIso (R : Genuine f f) {T : FppfStack.{u}} (q : StackHom T U) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp q R.unit) R.fst) q :=
  (StackIso2.associator q R.unit R.fst).trans
    ((StackIso2.whiskerLeft q R.unit_source).trans (StackIso2.rightUnitor q))

/-- The target comparison of a unit arrow: `(q ≫ unit) ≫ target ≅ q`. -/
noncomputable def unitPostcompSndIso (R : Genuine f f) {T : FppfStack.{u}} (q : StackHom T U) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp q R.unit) R.snd) q :=
  (StackIso2.associator q R.unit R.snd).trans
    ((StackIso2.whiskerLeft q R.unit_target).trans (StackIso2.rightUnitor q))

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `unitPostcompFstIso`. -/
theorem unitPostcompFstIso_appIso_hom_app (R : Genuine f f) {T : FppfStack.{u}}
    (q : StackHom T U) (V : Scheme.{u}) (x : StackFiber T V) :
    ((R.unitPostcompFstIso q).appIso V).hom.app x =
      (R.unit_source.appIso V).hom.app ((q.appFunctor V).obj x) := by
  dsimp only [unitPostcompFstIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, Category.id_comp]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `unitPostcompSndIso`. -/
theorem unitPostcompSndIso_appIso_hom_app (R : Genuine f f) {T : FppfStack.{u}}
    (q : StackHom T U) (V : Scheme.{u}) (x : StackFiber T V) :
    ((R.unitPostcompSndIso q).appIso V).hom.app x =
      (R.unit_target.appIso V).hom.app ((q.appFunctor V).obj x) := by
  dsimp only [unitPostcompSndIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, Category.id_comp]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- **A unit arrow classifies the constant cone.**  For every `q : T ⟶ U` the composite
`q ≫ unit` classifies `unitConeOf q`, comparison face included. -/
theorem unitPostcompClassifies (R : Genuine f f) {T : FppfStack.{u}} (q : StackHom T U) :
    ConeLiftClassifies R.toStackTwoPullback (R.unitConeOf q)
      (Pseudofunctor.StrongTrans.vcomp q R.unit)
      (R.unitPostcompFstIso q) (R.unitPostcompSndIso q) := by
  intro V x
  apply Iso.ext
  change
    (f.appFunctor V).map (((R.unitPostcompFstIso q).appIso V).hom.app x) ≫
        ((StackIso2.refl (Pseudofunctor.StrongTrans.vcomp q f)).appIso V).hom.app x =
      (R.comparison.appIso V).hom.app ((R.unit.appFunctor V).obj ((q.appFunctor V).obj x)) ≫
        (f.appFunctor V).map (((R.unitPostcompSndIso q).appIso V).hom.app x)
  rw [unitPostcompFstIso_appIso_hom_app, unitPostcompSndIso_appIso_hom_app]
  exact comp_eq_of_eq_id _ _ _ (refl_appIso_hom_app _ _ _)
    (R.unit_comparison V ((q.appFunctor V).obj x))

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face classified by the inversion map, on fibre components.** -/
theorem inverse_comparison (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (f.appFunctor V).map ((R.inverse_source.appIso V).hom.app x) ≫
        (R.comparison.appIso V).inv.app x =
      (R.comparison.appIso V).hom.app ((R.inverse.appFunctor V).obj x) ≫
        (f.appFunctor V).map ((R.inverse_target.appIso V).hom.app x) := by
  have h := congrArg Iso.hom (R.inverse_classifies V x)
  change
    (f.appFunctor V).map ((R.inverse_source.appIso V).hom.app x) ≫
        (R.comparison.symm.appIso V).hom.app x =
      (R.comparison.appIso V).hom.app ((R.inverse.appFunctor V).obj x) ≫
        (f.appFunctor V).map ((R.inverse_target.appIso V).hom.app x) at h
  rw [symm_appIso_hom_app] at h
  exact h

/-! ### The right inverse law: `compose (g, g⁻¹) ≅ unit (source g)` -/

/-- The comparison 2-cell of the cone pairing an arrow with its inverse. -/
noncomputable def invPairRightComparison (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) R.target)
      (Pseudofunctor.StrongTrans.vcomp R.inverse R.source) :=
  (StackIso2.leftUnitor R.target).trans R.inverse_source.symm

/-- The cone, over `R.pullback`, of the composable pair `(g, g⁻¹)`. -/
noncomputable def invPairRightCone (R : Genuine f f) :
    Cone (f := R.target) (g := R.source) R.pullback where
  fst := Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor
  snd := R.inverse
  comparison := R.invPairRightComparison

/-- The map pairing an arrow with its inverse. -/
noncomputable def invPairRight (R : Genuine f f) :
    StackHom R.pullback R.composable.pullback :=
  R.composable.bilimit.lift R.invPairRightCone

/-- The first projection of the `(g, g⁻¹)` pairing map is the identity. -/
noncomputable def invPairRight_firstArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.invPairRight R.firstArrow)
      (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) :=
  R.composable.bilimit.lift_fst R.invPairRightCone

/-- The second projection of the `(g, g⁻¹)` pairing map is inversion. -/
noncomputable def invPairRight_secondArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.invPairRight R.secondArrow) R.inverse :=
  R.composable.bilimit.lift_snd R.invPairRightCone

/-- The `(g, g⁻¹)` pairing map classifies its defining cone completely. -/
theorem invPairRight_classifies (R : Genuine f f) :
    ConeLiftClassifies R.composable.toStackTwoPullback R.invPairRightCone R.invPairRight
      R.invPairRight_firstArrow R.invPairRight_secondArrow :=
  R.composable.bilimit.lift_compatible R.invPairRightCone

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face of the `(g, g⁻¹)` pairing cone, on fibre components.** -/
theorem invPairRightComparison_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.invPairRightComparison.appIso V).hom.app x =
      (R.inverse_source.appIso V).inv.app x := by
  dsimp only [invPairRightComparison]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackTwoPullback.leftUnitor_appIso_hom_app,
    symm_appIso_hom_app, Category.id_comp]

/-- The source comparison of the right inverse composite. -/
noncomputable def invRightFstIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.invPairRight R.compose) R.fst) R.source :=
  (((StackIso2.associator R.invPairRight R.compose R.fst).trans
    (StackIso2.whiskerLeft R.invPairRight R.compose_source)).trans
      (StackIso2.associator R.invPairRight R.firstArrow R.fst).symm).trans
        ((StackIso2.whiskerRight R.invPairRight_firstArrow R.fst).trans
          (StackIso2.leftUnitor R.fst))

/-- The target comparison of the right inverse composite. -/
noncomputable def invRightSndIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.invPairRight R.compose) R.snd) R.source :=
  (((StackIso2.associator R.invPairRight R.compose R.snd).trans
    (StackIso2.whiskerLeft R.invPairRight R.compose_target)).trans
      (StackIso2.associator R.invPairRight R.secondArrow R.snd).symm).trans
        ((StackIso2.whiskerRight R.invPairRight_secondArrow R.snd).trans R.inverse_target)

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `invRightFstIso`. -/
theorem invRightFstIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.invRightFstIso.appIso V).hom.app x =
      (R.compose_source.appIso V).hom.app ((R.invPairRight.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.invPairRight_firstArrow.appIso V).hom.app x) := by
  dsimp only [invRightFstIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, Category.id_comp, Category.assoc]
  exact comp_idComp_comp_id _ _

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `invRightSndIso`. -/
theorem invRightSndIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.invRightSndIso.appIso V).hom.app x =
      (R.compose_target.appIso V).hom.app ((R.invPairRight.appFunctor V).obj x) ≫
        (R.snd.appFunctor V).map ((R.invPairRight_secondArrow.appIso V).hom.app x) ≫
          (R.inverse_target.appIso V).hom.app x := by
  dsimp only [invRightSndIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, Category.id_comp, Category.assoc]
  exact comp_idComp _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face classified by the `(g, g⁻¹)` pairing map, on fibre components.** -/
theorem invPairRight_comparison (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.snd.appFunctor V).map ((R.invPairRight_firstArrow.appIso V).hom.app x) ≫
        (R.inverse_source.appIso V).inv.app x =
      (R.composableComparison.appIso V).hom.app ((R.invPairRight.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.invPairRight_secondArrow.appIso V).hom.app x) := by
  have h := congrArg Iso.hom (R.invPairRight_classifies V x)
  change
    (R.snd.appFunctor V).map ((R.invPairRight_firstArrow.appIso V).hom.app x) ≫
        (R.invPairRightComparison.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.invPairRight.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.invPairRight_secondArrow.appIso V).hom.app x) at h
  rw [invPairRightComparison_appIso_hom_app] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The target-side identification supplied by the `(g, g⁻¹)` pairing map. -/
theorem invPairRight_snd_eq (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.snd.appFunctor V).map ((R.invPairRight_firstArrow.appIso V).hom.app x) =
      (R.composableComparison.appIso V).hom.app ((R.invPairRight.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.invPairRight_secondArrow.appIso V).hom.app x) ≫
          (R.inverse_source.appIso V).hom.app x :=
  eq_comp_comp_of_comp_inv _ _ _ _ _ ((R.inverse_source.appIso V).inv_hom_id_app _)
    (R.invPairRight_comparison V x)

/-- **The diagram chase behind the right inverse law**, in an arbitrary category. -/
theorem invRightSquare {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {s₁ s₂ zz u₁ w v₁ v₂ t₁ t₂ t₃ : C}
    {cs : s₁ ⟶ s₂} {sa : s₂ ⟶ zz} {ct : t₁ ⟶ t₂} {tb : t₂ ⟶ t₃} {it : t₃ ⟶ zz}
    {ta : u₁ ⟶ w} {cc : u₁ ⟶ v₁} {sb : v₁ ⟶ v₂} {si : v₂ ⟶ w}
    {e : F.obj zz ⟶ F.obj zz}
    {cmpc : F.obj s₁ ⟶ F.obj t₁} {cmp1 : F.obj s₂ ⟶ F.obj u₁}
    {cmp2 : F.obj v₁ ⟶ F.obj t₂} {cmpi : F.obj v₂ ⟶ F.obj t₃}
    {cmpx : F.obj zz ⟶ F.obj w} {cmpy : F.obj w ⟶ F.obj zz}
    (he : e = 𝟙 (F.obj zz))
    (hA : F.map cs ≫ cmp1 ≫ F.map cc ≫ cmp2 = cmpc ≫ F.map ct)
    (hB : ta = cc ≫ sb ≫ si)
    (hI : F.map si ≫ cmpy = cmpi ≫ F.map it)
    (ha : F.map sa ≫ cmpx = cmp1 ≫ F.map ta)
    (hb : F.map sb ≫ cmpi = cmp2 ≫ F.map tb)
    (hx : cmpx ≫ cmpy = 𝟙 (F.obj zz)) :
    F.map (cs ≫ sa) ≫ e = cmpc ≫ F.map (ct ≫ tb ≫ it) := by
  have hB' : F.map cc ≫ F.map sb ≫ F.map si = F.map ta := by
    rw [hB]; simp
  rw [he, Category.comp_id]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hA, ← reassoc_of% hb, ← hI, reassoc_of% hB', ← reassoc_of% ha, hx,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- **The right inverse composite classifies the constant cone at the source.** -/
theorem invRightClassifies (R : Genuine f f) :
    ConeLiftClassifies R.toStackTwoPullback (R.unitConeOf R.source)
      (Pseudofunctor.StrongTrans.vcomp R.invPairRight R.compose)
      R.invRightFstIso R.invRightSndIso := by
  intro V x
  apply Iso.ext
  change
    (f.appFunctor V).map ((R.invRightFstIso.appIso V).hom.app x) ≫
        ((StackIso2.refl (Pseudofunctor.StrongTrans.vcomp R.source f)).appIso V).hom.app x =
      (R.comparison.appIso V).hom.app
          ((R.compose.appFunctor V).obj ((R.invPairRight.appFunctor V).obj x)) ≫
        (f.appFunctor V).map ((R.invRightSndIso.appIso V).hom.app x)
  rw [invRightFstIso_appIso_hom_app, invRightSndIso_appIso_hom_app]
  exact invRightSquare (refl_appIso_hom_app _ _ _)
    (R.compose_comparison V ((R.invPairRight.appFunctor V).obj x))
    (R.invPairRight_snd_eq V x) (R.inverse_comparison V x)
    (R.comparison_naturality V
      (a := (R.firstArrow.appFunctor V).obj ((R.invPairRight.appFunctor V).obj x)) (b := x)
      ((R.invPairRight_firstArrow.appIso V).hom.app x))
    (R.comparison_naturality V
      (a := (R.secondArrow.appFunctor V).obj ((R.invPairRight.appFunctor V).obj x))
      (b := (R.inverse.appFunctor V).obj x)
      ((R.invPairRight_secondArrow.appIso V).hom.app x))
    ((R.comparison.appIso V).hom_inv_id_app x)

/-- **The right inverse law of the presentation groupoid.**  Composing an arrow with its inverse
is 2-isomorphic to the identity arrow at its source. -/
noncomputable def inverse_compose_right (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.invPairRight R.compose)
      (Pseudofunctor.StrongTrans.vcomp R.source R.unit) :=
  (R.bilimit.lift_unique (R.unitConeOf R.source)
      (Pseudofunctor.StrongTrans.vcomp R.invPairRight R.compose)
      R.invRightFstIso R.invRightSndIso R.invRightClassifies).trans
    (R.bilimit.lift_unique (R.unitConeOf R.source)
      (Pseudofunctor.StrongTrans.vcomp R.source R.unit)
      (R.unitPostcompFstIso R.source) (R.unitPostcompSndIso R.source)
      (R.unitPostcompClassifies R.source)).symm

/-! ### The left inverse law: `compose (g⁻¹, g) ≅ unit (target g)` -/

/-- The comparison 2-cell of the cone pairing the inverse of an arrow with the arrow. -/
noncomputable def invPairLeftComparison (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.inverse R.target)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) R.source) :=
  R.inverse_target.trans (StackIso2.leftUnitor R.source).symm

/-- The cone, over `R.pullback`, of the composable pair `(g⁻¹, g)`. -/
noncomputable def invPairLeftCone (R : Genuine f f) :
    Cone (f := R.target) (g := R.source) R.pullback where
  fst := R.inverse
  snd := Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor
  comparison := R.invPairLeftComparison

/-- The map pairing the inverse of an arrow with the arrow. -/
noncomputable def invPairLeft (R : Genuine f f) :
    StackHom R.pullback R.composable.pullback :=
  R.composable.bilimit.lift R.invPairLeftCone

/-- The first projection of the `(g⁻¹, g)` pairing map is inversion. -/
noncomputable def invPairLeft_firstArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.invPairLeft R.firstArrow) R.inverse :=
  R.composable.bilimit.lift_fst R.invPairLeftCone

/-- The second projection of the `(g⁻¹, g)` pairing map is the identity. -/
noncomputable def invPairLeft_secondArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.invPairLeft R.secondArrow)
      (Pseudofunctor.StrongTrans.id R.pullback.toPseudofunctor) :=
  R.composable.bilimit.lift_snd R.invPairLeftCone

/-- The `(g⁻¹, g)` pairing map classifies its defining cone completely. -/
theorem invPairLeft_classifies (R : Genuine f f) :
    ConeLiftClassifies R.composable.toStackTwoPullback R.invPairLeftCone R.invPairLeft
      R.invPairLeft_firstArrow R.invPairLeft_secondArrow :=
  R.composable.bilimit.lift_compatible R.invPairLeftCone

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face of the `(g⁻¹, g)` pairing cone, on fibre components.** -/
theorem invPairLeftComparison_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.invPairLeftComparison.appIso V).hom.app x =
      (R.inverse_target.appIso V).hom.app x := by
  dsimp only [invPairLeftComparison]
  simp only [StackTwoPullback.trans_appIso_hom_app, symm_appIso_hom_app,
    StackTwoPullback.leftUnitor_appIso_inv_app, Category.comp_id]

/-- The source comparison of the left inverse composite. -/
noncomputable def invLeftFstIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.invPairLeft R.compose) R.fst) R.target :=
  (((StackIso2.associator R.invPairLeft R.compose R.fst).trans
    (StackIso2.whiskerLeft R.invPairLeft R.compose_source)).trans
      (StackIso2.associator R.invPairLeft R.firstArrow R.fst).symm).trans
        ((StackIso2.whiskerRight R.invPairLeft_firstArrow R.fst).trans R.inverse_source)

/-- The target comparison of the left inverse composite. -/
noncomputable def invLeftSndIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.invPairLeft R.compose) R.snd) R.target :=
  (((StackIso2.associator R.invPairLeft R.compose R.snd).trans
    (StackIso2.whiskerLeft R.invPairLeft R.compose_target)).trans
      (StackIso2.associator R.invPairLeft R.secondArrow R.snd).symm).trans
        ((StackIso2.whiskerRight R.invPairLeft_secondArrow R.snd).trans
          (StackIso2.leftUnitor R.snd))

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `invLeftFstIso`. -/
theorem invLeftFstIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.invLeftFstIso.appIso V).hom.app x =
      (R.compose_source.appIso V).hom.app ((R.invPairLeft.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.invPairLeft_firstArrow.appIso V).hom.app x) ≫
          (R.inverse_source.appIso V).hom.app x := by
  dsimp only [invLeftFstIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, Category.id_comp, Category.assoc]
  exact comp_idComp _ _

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `invLeftSndIso`. -/
theorem invLeftSndIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.invLeftSndIso.appIso V).hom.app x =
      (R.compose_target.appIso V).hom.app ((R.invPairLeft.appFunctor V).obj x) ≫
        (R.snd.appFunctor V).map ((R.invPairLeft_secondArrow.appIso V).hom.app x) := by
  dsimp only [invLeftSndIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, Category.id_comp, Category.assoc]
  exact comp_idComp_comp_id _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face classified by the `(g⁻¹, g)` pairing map, on fibre components.** -/
theorem invPairLeft_comparison (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.pullback V) :
    (R.snd.appFunctor V).map ((R.invPairLeft_firstArrow.appIso V).hom.app x) ≫
        (R.inverse_target.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.invPairLeft.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.invPairLeft_secondArrow.appIso V).hom.app x) := by
  have h := congrArg Iso.hom (R.invPairLeft_classifies V x)
  change
    (R.snd.appFunctor V).map ((R.invPairLeft_firstArrow.appIso V).hom.app x) ≫
        (R.invPairLeftComparison.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.invPairLeft.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.invPairLeft_secondArrow.appIso V).hom.app x) at h
  rw [invPairLeftComparison_appIso_hom_app] at h
  exact h

/-- **The diagram chase behind the left inverse law**, in an arbitrary category. -/
theorem invLeftSquare {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {s₁ s₂ v₂ w u₁ vv zz v₁ t₁ t₂ : C}
    {cs : s₁ ⟶ s₂} {sa : s₂ ⟶ v₂} {si : v₂ ⟶ w} {ct : t₁ ⟶ t₂} {tb : t₂ ⟶ w}
    {ta : u₁ ⟶ vv} {it : vv ⟶ zz} {cc : u₁ ⟶ v₁} {sb : v₁ ⟶ zz}
    {e : F.obj w ⟶ F.obj w}
    {cmpc : F.obj s₁ ⟶ F.obj t₁} {cmp1 : F.obj s₂ ⟶ F.obj u₁}
    {cmp2 : F.obj v₁ ⟶ F.obj t₂} {cmpi : F.obj v₂ ⟶ F.obj vv}
    {cmpx : F.obj zz ⟶ F.obj w} {cmpy : F.obj w ⟶ F.obj zz}
    (he : e = 𝟙 (F.obj w))
    (hA : F.map cs ≫ cmp1 ≫ F.map cc ≫ cmp2 = cmpc ≫ F.map ct)
    (hB : ta ≫ it = cc ≫ sb)
    (hI : F.map si ≫ cmpy = cmpi ≫ F.map it)
    (ha : F.map sa ≫ cmpi = cmp1 ≫ F.map ta)
    (hb : F.map sb ≫ cmpx = cmp2 ≫ F.map tb)
    (hx : cmpy ≫ cmpx = 𝟙 (F.obj w)) :
    F.map (cs ≫ sa ≫ si) ≫ e = cmpc ≫ F.map (ct ≫ tb) := by
  have hB' : F.map cc ≫ F.map sb = F.map ta ≫ F.map it := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← hB]
  rw [he, Category.comp_id]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hA, ← hb, reassoc_of% hB', ← reassoc_of% ha, ← reassoc_of% hI, hx,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- **The left inverse composite classifies the constant cone at the target.** -/
theorem invLeftClassifies (R : Genuine f f) :
    ConeLiftClassifies R.toStackTwoPullback (R.unitConeOf R.target)
      (Pseudofunctor.StrongTrans.vcomp R.invPairLeft R.compose)
      R.invLeftFstIso R.invLeftSndIso := by
  intro V x
  apply Iso.ext
  change
    (f.appFunctor V).map ((R.invLeftFstIso.appIso V).hom.app x) ≫
        ((StackIso2.refl (Pseudofunctor.StrongTrans.vcomp R.target f)).appIso V).hom.app x =
      (R.comparison.appIso V).hom.app
          ((R.compose.appFunctor V).obj ((R.invPairLeft.appFunctor V).obj x)) ≫
        (f.appFunctor V).map ((R.invLeftSndIso.appIso V).hom.app x)
  rw [invLeftFstIso_appIso_hom_app, invLeftSndIso_appIso_hom_app]
  exact invLeftSquare (refl_appIso_hom_app _ _ _)
    (R.compose_comparison V ((R.invPairLeft.appFunctor V).obj x))
    (R.invPairLeft_comparison V x) (R.inverse_comparison V x)
    (R.comparison_naturality V
      (a := (R.firstArrow.appFunctor V).obj ((R.invPairLeft.appFunctor V).obj x))
      (b := (R.inverse.appFunctor V).obj x)
      ((R.invPairLeft_firstArrow.appIso V).hom.app x))
    (R.comparison_naturality V
      (a := (R.secondArrow.appFunctor V).obj ((R.invPairLeft.appFunctor V).obj x)) (b := x)
      ((R.invPairLeft_secondArrow.appIso V).hom.app x))
    ((R.comparison.appIso V).inv_hom_id_app x)

/-- **The left inverse law of the presentation groupoid.**  Composing the inverse of an arrow
with the arrow is 2-isomorphic to the identity arrow at its target. -/
noncomputable def inverse_compose_left (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.invPairLeft R.compose)
      (Pseudofunctor.StrongTrans.vcomp R.target R.unit) :=
  (R.bilimit.lift_unique (R.unitConeOf R.target)
      (Pseudofunctor.StrongTrans.vcomp R.invPairLeft R.compose)
      R.invLeftFstIso R.invLeftSndIso R.invLeftClassifies).trans
    (R.bilimit.lift_unique (R.unitConeOf R.target)
      (Pseudofunctor.StrongTrans.vcomp R.target R.unit)
      (R.unitPostcompFstIso R.target) (R.unitPostcompSndIso R.target)
      (R.unitPostcompClassifies R.target)).symm

/-! ### Associativity of composition

The triple-composable stack `composable3` is the genuine two-pullback of the outer target of a
composable pair against the source of a further arrow; its points are triples `(g₁, g₂, g₃)` with
`target g₁ = source g₂` and `target g₂ = source g₃`.  Both bracketings of the triple composite are
maps `composable3.pullback ⟶ R.pullback`, and both classify the same cone `assocCone`, whose
comparison face is the full four-step chain of tautological 2-cells across the triple. -/

/-- The `inv` components of a right whiskering. -/
theorem whiskerRight_appIso_inv_app {A B C : FppfStack.{u}} {p q : StackHom A B}
    (e : StackIso2 p q) (r : StackHom B C) (V : Scheme.{u}) (x : StackFiber A V) :
    ((StackIso2.whiskerRight e r).appIso V).inv.app x =
      (r.appFunctor V).map ((e.appIso V).inv.app x) := rfl

/-- Cancelling a pair of mutually inverse arrows sitting after a two-factor composite. -/
theorem comp_eq_comp_comp_of_comp_inv {W : Type*} [Category W] {a b c d e : W} (u : a ⟶ b)
    (m : b ⟶ c) (i : c ⟶ d) (j : d ⟶ c) (v : a ⟶ e) (w : e ⟶ d)
    (hij : i ≫ j = 𝟙 c) (h : u ≫ m ≫ i = v ≫ w) : u ≫ m = v ≫ w ≫ j := by
  rw [← Category.assoc, ← h]; simp [hij]

/-- A two-step composite of mutually inverse pairs is the identity. -/
theorem comp_comp_comp_comp_eq_id {W : Type*} [Category W] {a b c : W} (i : a ⟶ b) (j : b ⟶ c)
    (j' : c ⟶ b) (i' : b ⟶ a) (h1 : j ≫ j' = 𝟙 b) (h2 : i ≫ i' = 𝟙 a) :
    (i ≫ j) ≫ j' ≫ i' = 𝟙 a := by
  rw [Category.assoc, ← Category.assoc j, h1, Category.id_comp, h2]

/-- **The stack of triples of composable arrows.**  It is the genuine two-pullback of the outer
target of a composable pair against the source map of the arrow stack. -/
noncomputable def composable3 (R : Genuine f f) :
    Genuine (Pseudofunctor.StrongTrans.vcomp R.secondArrow R.snd) R.fst :=
  canonicalGenuine (Pseudofunctor.StrongTrans.vcomp R.secondArrow R.snd) R.fst

/-! #### The pair of the last two arrows of a triple -/

/-- The composability 2-cell of the pair `(g₂, g₃)` of the last two arrows of a triple. -/
noncomputable def tailPairComparison (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.composable3.fst R.secondArrow) R.snd)
      (Pseudofunctor.StrongTrans.vcomp R.composable3.snd R.fst) :=
  (StackIso2.associator R.composable3.fst R.secondArrow R.snd).trans R.composable3.comparison

/-- The cone of the pair `(g₂, g₃)` of the last two arrows of a triple. -/
noncomputable def tailPairCone (R : Genuine f f) :
    Cone (f := R.snd) (g := R.fst) R.composable3.pullback where
  fst := Pseudofunctor.StrongTrans.vcomp R.composable3.fst R.secondArrow
  snd := R.composable3.snd
  comparison := R.tailPairComparison

/-- The map sending a triple to the composable pair of its last two arrows. -/
noncomputable def tailPair (R : Genuine f f) :
    StackHom R.composable3.pullback R.composable.pullback :=
  R.composable.bilimit.lift R.tailPairCone

/-- The first arrow of the tail pair of a triple is its second arrow. -/
noncomputable def tailPair_firstArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.tailPair R.firstArrow)
      (Pseudofunctor.StrongTrans.vcomp R.composable3.fst R.secondArrow) :=
  R.composable.bilimit.lift_fst R.tailPairCone

/-- The second arrow of the tail pair of a triple is its third arrow. -/
noncomputable def tailPair_secondArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.tailPair R.secondArrow) R.composable3.snd :=
  R.composable.bilimit.lift_snd R.tailPairCone

/-- The tail-pair map classifies its defining cone completely. -/
theorem tailPair_classifies (R : Genuine f f) :
    ConeLiftClassifies R.composable.toStackTwoPullback R.tailPairCone R.tailPair
      R.tailPair_firstArrow R.tailPair_secondArrow :=
  R.composable.bilimit.lift_compatible R.tailPairCone

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face of the tail-pair cone, on fibre components.** -/
theorem tailPairComparison_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.tailPairComparison.appIso V).hom.app x =
      (R.composable3.comparison.appIso V).hom.app x := by
  dsimp only [tailPairComparison]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face classified by the tail-pair map, on fibre components.** -/
theorem tailPair_comparison (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.snd.appFunctor V).map ((R.tailPair_firstArrow.appIso V).hom.app x) ≫
        (R.composable3.comparison.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.tailPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.tailPair_secondArrow.appIso V).hom.app x) := by
  have h := congrArg Iso.hom (R.tailPair_classifies V x)
  change
    (R.snd.appFunctor V).map ((R.tailPair_firstArrow.appIso V).hom.app x) ≫
        (R.tailPairComparison.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.tailPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.tailPair_secondArrow.appIso V).hom.app x) at h
  rw [tailPairComparison_appIso_hom_app] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The image under the source map of the two mutually inverse components of the tail-pair
first-arrow 2-cell cancel. -/
theorem tailPair_firstArrow_map_inv_hom (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.fst.appFunctor V).map ((R.tailPair_firstArrow.appIso V).inv.app x) ≫
        (R.fst.appFunctor V).map ((R.tailPair_firstArrow.appIso V).hom.app x) = 𝟙 _ := by
  rw [← Functor.map_comp, (R.tailPair_firstArrow.appIso V).inv_hom_id_app,
    CategoryTheory.Functor.map_id]

/-! #### The cone classified by both bracketings -/

/-- The comparison face of the cone classified by a triple composite: the four-step chain of
tautological 2-cells running from the source of the first arrow to the target of the third. -/
noncomputable def assocConeComparison (R : Genuine f f) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.composable3.fst
          (Pseudofunctor.StrongTrans.vcomp R.firstArrow R.fst)) f)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.composable3.snd R.snd) f) :=
  ((((StackIso2.associator R.composable3.fst
      (Pseudofunctor.StrongTrans.vcomp R.firstArrow R.fst) f).trans
    (StackIso2.whiskerLeft R.composable3.fst R.composeConeComparison)).trans
      (StackIso2.associator R.composable3.fst
        (Pseudofunctor.StrongTrans.vcomp R.secondArrow R.snd) f).symm).trans
        (StackIso2.whiskerRight R.composable3.comparison f)).trans
          (((StackIso2.associator R.composable3.snd R.fst f).trans
            (StackIso2.whiskerLeft R.composable3.snd R.comparison)).trans
              (StackIso2.associator R.composable3.snd R.snd f).symm)

/-- The cone, over the stack of triples, classified by either bracketing of the triple
composite: its first leg is the source of the first arrow, its second the target of the
third. -/
noncomputable def assocCone (R : Genuine f f) :
    Cone (f := f) (g := f) R.composable3.pullback where
  fst := Pseudofunctor.StrongTrans.vcomp R.composable3.fst
    (Pseudofunctor.StrongTrans.vcomp R.firstArrow R.fst)
  snd := Pseudofunctor.StrongTrans.vcomp R.composable3.snd R.snd
  comparison := R.assocConeComparison

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face of `assocCone`, on fibre components.** -/
theorem assocConeComparison_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.assocConeComparison.appIso V).hom.app x =
      (R.comparison.appIso V).hom.app ((R.firstArrow.appFunctor V).obj
          ((R.composable3.fst.appFunctor V).obj x)) ≫
        (f.appFunctor V).map ((R.composableComparison.appIso V).hom.app
          ((R.composable3.fst.appFunctor V).obj x)) ≫
          (R.comparison.appIso V).hom.app ((R.secondArrow.appFunctor V).obj
            ((R.composable3.fst.appFunctor V).obj x)) ≫
            (f.appFunctor V).map ((R.composable3.comparison.appIso V).hom.app x) ≫
              (R.comparison.appIso V).hom.app ((R.composable3.snd.appFunctor V).obj x) := by
  dsimp only [assocConeComparison]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, composeConeComparison_appIso_hom_app, Category.id_comp,
    Category.comp_id, Category.assoc]

/-! #### The left bracketing `(g₁g₂)g₃` -/

/-- The composability 2-cell of the pair `(g₁g₂, g₃)`. -/
noncomputable def assocLeftPairComparison (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.composable3.fst R.compose) R.snd)
      (Pseudofunctor.StrongTrans.vcomp R.composable3.snd R.fst) :=
  ((StackIso2.associator R.composable3.fst R.compose R.snd).trans
    (StackIso2.whiskerLeft R.composable3.fst R.compose_target)).trans R.composable3.comparison

/-- The cone of the pair `(g₁g₂, g₃)`. -/
noncomputable def assocLeftPairCone (R : Genuine f f) :
    Cone (f := R.snd) (g := R.fst) R.composable3.pullback where
  fst := Pseudofunctor.StrongTrans.vcomp R.composable3.fst R.compose
  snd := R.composable3.snd
  comparison := R.assocLeftPairComparison

/-- The map sending a triple to the composable pair `(g₁g₂, g₃)`. -/
noncomputable def assocLeftPair (R : Genuine f f) :
    StackHom R.composable3.pullback R.composable.pullback :=
  R.composable.bilimit.lift R.assocLeftPairCone

/-- The first arrow of the left-bracketing pair is the composite of the first two arrows. -/
noncomputable def assocLeftPair_firstArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.assocLeftPair R.firstArrow)
      (Pseudofunctor.StrongTrans.vcomp R.composable3.fst R.compose) :=
  R.composable.bilimit.lift_fst R.assocLeftPairCone

/-- The second arrow of the left-bracketing pair is the third arrow of the triple. -/
noncomputable def assocLeftPair_secondArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.assocLeftPair R.secondArrow)
      R.composable3.snd :=
  R.composable.bilimit.lift_snd R.assocLeftPairCone

/-- The left-bracketing pairing map classifies its defining cone completely. -/
theorem assocLeftPair_classifies (R : Genuine f f) :
    ConeLiftClassifies R.composable.toStackTwoPullback R.assocLeftPairCone R.assocLeftPair
      R.assocLeftPair_firstArrow R.assocLeftPair_secondArrow :=
  R.composable.bilimit.lift_compatible R.assocLeftPairCone

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face of the left-bracketing pairing cone, on fibre components.** -/
theorem assocLeftPairComparison_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.assocLeftPairComparison.appIso V).hom.app x =
      (R.compose_target.appIso V).hom.app ((R.composable3.fst.appFunctor V).obj x) ≫
        (R.composable3.comparison.appIso V).hom.app x := by
  dsimp only [assocLeftPairComparison]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face classified by the left-bracketing pairing map, on components.** -/
theorem assocLeftPair_comparison (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.snd.appFunctor V).map ((R.assocLeftPair_firstArrow.appIso V).hom.app x) ≫
        (R.compose_target.appIso V).hom.app ((R.composable3.fst.appFunctor V).obj x) ≫
          (R.composable3.comparison.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.assocLeftPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.assocLeftPair_secondArrow.appIso V).hom.app x) := by
  have h := congrArg Iso.hom (R.assocLeftPair_classifies V x)
  change
    (R.snd.appFunctor V).map ((R.assocLeftPair_firstArrow.appIso V).hom.app x) ≫
        (R.assocLeftPairComparison.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.assocLeftPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.assocLeftPair_secondArrow.appIso V).hom.app x) at h
  rw [assocLeftPairComparison_appIso_hom_app] at h
  exact h

/-- The source comparison of the left bracketing of a triple composite. -/
noncomputable def assocLeftFstIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.assocLeftPair R.compose) R.fst)
      (Pseudofunctor.StrongTrans.vcomp R.composable3.fst
        (Pseudofunctor.StrongTrans.vcomp R.firstArrow R.fst)) :=
  (((StackIso2.associator R.assocLeftPair R.compose R.fst).trans
    (StackIso2.whiskerLeft R.assocLeftPair R.compose_source)).trans
      (StackIso2.associator R.assocLeftPair R.firstArrow R.fst).symm).trans
        ((StackIso2.whiskerRight R.assocLeftPair_firstArrow R.fst).trans
          ((StackIso2.associator R.composable3.fst R.compose R.fst).trans
            (StackIso2.whiskerLeft R.composable3.fst R.compose_source)))

/-- The target comparison of the left bracketing of a triple composite. -/
noncomputable def assocLeftSndIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.assocLeftPair R.compose) R.snd)
      (Pseudofunctor.StrongTrans.vcomp R.composable3.snd R.snd) :=
  (((StackIso2.associator R.assocLeftPair R.compose R.snd).trans
    (StackIso2.whiskerLeft R.assocLeftPair R.compose_target)).trans
      (StackIso2.associator R.assocLeftPair R.secondArrow R.snd).symm).trans
        (StackIso2.whiskerRight R.assocLeftPair_secondArrow R.snd)

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `assocLeftFstIso`. -/
theorem assocLeftFstIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.assocLeftFstIso.appIso V).hom.app x =
      (R.compose_source.appIso V).hom.app ((R.assocLeftPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.assocLeftPair_firstArrow.appIso V).hom.app x) ≫
          (R.compose_source.appIso V).hom.app ((R.composable3.fst.appFunctor V).obj x) := by
  dsimp only [assocLeftFstIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, Category.id_comp, Category.assoc]
  exact comp_idComp _ _

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `assocLeftSndIso`. -/
theorem assocLeftSndIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.assocLeftSndIso.appIso V).hom.app x =
      (R.compose_target.appIso V).hom.app ((R.assocLeftPair.appFunctor V).obj x) ≫
        (R.snd.appFunctor V).map ((R.assocLeftPair_secondArrow.appIso V).hom.app x) := by
  dsimp only [assocLeftSndIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, Category.id_comp, Category.assoc]
  exact comp_idComp _ _

/-- **The diagram chase behind the left bracketing of a triple composite**, in an arbitrary
category. -/
theorem assocLeftSquare {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {a1 a2 a3 a4 b1 b2 b3 c1 c2 c3o c4 d1 d2 e1 : C}
    {csq : a1 ⟶ a2} {sa1 : a2 ⟶ a3} {csp : a3 ⟶ a4}
    {ctq : b1 ⟶ b2} {ta2 : b2 ⟶ b3}
    {ta1 : c1 ⟶ c2} {ctp : c2 ⟶ c3o} {c3 : c3o ⟶ c4}
    {ccq : c1 ⟶ d1} {sa2 : d1 ⟶ c4} {ccp : e1 ⟶ d2}
    {e : F.obj a4 ⟶ F.obj b3}
    {cmpg1 : F.obj a4 ⟶ F.obj e1} {cmpg2 : F.obj d2 ⟶ F.obj c3o}
    {cmpg3 : F.obj c4 ⟶ F.obj b3} {cmpfaq : F.obj a2 ⟶ F.obj c1}
    {cmpsaq : F.obj d1 ⟶ F.obj b2} {cmpcp : F.obj a3 ⟶ F.obj c2}
    {cmpcq : F.obj a1 ⟶ F.obj b1}
    (he : e = cmpg1 ≫ F.map ccp ≫ cmpg2 ≫ F.map c3 ≫ cmpg3)
    (hA1 : F.map csq ≫ cmpfaq ≫ F.map ccq ≫ cmpsaq = cmpcq ≫ F.map ctq)
    (hA2 : F.map csp ≫ cmpg1 ≫ F.map ccp ≫ cmpg2 = cmpcp ≫ F.map ctp)
    (hB : ta1 ≫ ctp ≫ c3 = ccq ≫ sa2)
    (hN1 : F.map sa1 ≫ cmpcp = cmpfaq ≫ F.map ta1)
    (hN2 : F.map sa2 ≫ cmpg3 = cmpsaq ≫ F.map ta2) :
    F.map (csq ≫ sa1 ≫ csp) ≫ e = cmpcq ≫ F.map (ctq ≫ ta2) := by
  have hB3 : F.map ta1 ≫ F.map ctp ≫ F.map c3 = F.map ccq ≫ F.map sa2 := by
    simp only [← Functor.map_comp]; rw [hB]
  rw [he]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hA2, reassoc_of% hN1, reassoc_of% hB3, hN2, reassoc_of% hA1]

set_option backward.isDefEq.respectTransparency false in
/-- **The left bracketing of a triple composite classifies `assocCone`.** -/
theorem assocLeftClassifies (R : Genuine f f) :
    ConeLiftClassifies R.toStackTwoPullback R.assocCone
      (Pseudofunctor.StrongTrans.vcomp R.assocLeftPair R.compose)
      R.assocLeftFstIso R.assocLeftSndIso := by
  intro V x
  apply Iso.ext
  change
    (f.appFunctor V).map ((R.assocLeftFstIso.appIso V).hom.app x) ≫
        (R.assocConeComparison.appIso V).hom.app x =
      (R.comparison.appIso V).hom.app
          ((R.compose.appFunctor V).obj ((R.assocLeftPair.appFunctor V).obj x)) ≫
        (f.appFunctor V).map ((R.assocLeftSndIso.appIso V).hom.app x)
  rw [assocLeftFstIso_appIso_hom_app, assocLeftSndIso_appIso_hom_app]
  exact assocLeftSquare (R.assocConeComparison_appIso_hom_app V x)
    (R.compose_comparison V ((R.assocLeftPair.appFunctor V).obj x))
    (R.compose_comparison V ((R.composable3.fst.appFunctor V).obj x))
    (R.assocLeftPair_comparison V x)
    (R.comparison_naturality V
      (a := (R.firstArrow.appFunctor V).obj ((R.assocLeftPair.appFunctor V).obj x))
      (b := (R.compose.appFunctor V).obj ((R.composable3.fst.appFunctor V).obj x))
      ((R.assocLeftPair_firstArrow.appIso V).hom.app x))
    (R.comparison_naturality V
      (a := (R.secondArrow.appFunctor V).obj ((R.assocLeftPair.appFunctor V).obj x))
      (b := (R.composable3.snd.appFunctor V).obj x)
      ((R.assocLeftPair_secondArrow.appIso V).hom.app x))

/-! #### The right bracketing `g₁(g₂g₃)` -/

/-- The composability 2-cell of the pair `(g₁, g₂g₃)`. -/
noncomputable def assocRightPairComparison (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.composable3.fst R.firstArrow) R.snd)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.tailPair R.compose) R.fst) :=
  ((((((StackIso2.associator R.composable3.fst R.firstArrow R.snd).trans
    (StackIso2.whiskerLeft R.composable3.fst R.composableComparison)).trans
      (StackIso2.associator R.composable3.fst R.secondArrow R.fst).symm).trans
        (StackIso2.whiskerRight R.tailPair_firstArrow R.fst).symm).trans
          (StackIso2.associator R.tailPair R.firstArrow R.fst)).trans
            (StackIso2.whiskerLeft R.tailPair R.compose_source).symm).trans
              (StackIso2.associator R.tailPair R.compose R.fst).symm

/-- The cone of the pair `(g₁, g₂g₃)`. -/
noncomputable def assocRightPairCone (R : Genuine f f) :
    Cone (f := R.snd) (g := R.fst) R.composable3.pullback where
  fst := Pseudofunctor.StrongTrans.vcomp R.composable3.fst R.firstArrow
  snd := Pseudofunctor.StrongTrans.vcomp R.tailPair R.compose
  comparison := R.assocRightPairComparison

/-- The map sending a triple to the composable pair `(g₁, g₂g₃)`. -/
noncomputable def assocRightPair (R : Genuine f f) :
    StackHom R.composable3.pullback R.composable.pullback :=
  R.composable.bilimit.lift R.assocRightPairCone

/-- The first arrow of the right-bracketing pair is the first arrow of the triple. -/
noncomputable def assocRightPair_firstArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.assocRightPair R.firstArrow)
      (Pseudofunctor.StrongTrans.vcomp R.composable3.fst R.firstArrow) :=
  R.composable.bilimit.lift_fst R.assocRightPairCone

/-- The second arrow of the right-bracketing pair is the composite of the last two. -/
noncomputable def assocRightPair_secondArrow (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.assocRightPair R.secondArrow)
      (Pseudofunctor.StrongTrans.vcomp R.tailPair R.compose) :=
  R.composable.bilimit.lift_snd R.assocRightPairCone

/-- The right-bracketing pairing map classifies its defining cone completely. -/
theorem assocRightPair_classifies (R : Genuine f f) :
    ConeLiftClassifies R.composable.toStackTwoPullback R.assocRightPairCone R.assocRightPair
      R.assocRightPair_firstArrow R.assocRightPair_secondArrow :=
  R.composable.bilimit.lift_compatible R.assocRightPairCone

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face of the right-bracketing pairing cone, on fibre components.** -/
theorem assocRightPairComparison_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.assocRightPairComparison.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.composable3.fst.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.tailPair_firstArrow.appIso V).inv.app x) ≫
          (R.compose_source.appIso V).inv.app ((R.tailPair.appFunctor V).obj x) := by
  dsimp only [assocRightPairComparison]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, symm_appIso_hom_app, associator_appIso_inv_app,
    whiskerRight_appIso_inv_app, whiskerLeft_appIso_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  exact comp_idComp_comp_comp_id _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison face classified by the right-bracketing pairing map, on components.** -/
theorem assocRightPair_comparison (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.snd.appFunctor V).map ((R.assocRightPair_firstArrow.appIso V).hom.app x) ≫
        (R.composableComparison.appIso V).hom.app ((R.composable3.fst.appFunctor V).obj x) ≫
          ((R.fst.appFunctor V).map ((R.tailPair_firstArrow.appIso V).inv.app x) ≫
            (R.compose_source.appIso V).inv.app ((R.tailPair.appFunctor V).obj x)) =
      (R.composableComparison.appIso V).hom.app ((R.assocRightPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.assocRightPair_secondArrow.appIso V).hom.app x) := by
  have h := congrArg Iso.hom (R.assocRightPair_classifies V x)
  change
    (R.snd.appFunctor V).map ((R.assocRightPair_firstArrow.appIso V).hom.app x) ≫
        (R.assocRightPairComparison.appIso V).hom.app x =
      (R.composableComparison.appIso V).hom.app ((R.assocRightPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.assocRightPair_secondArrow.appIso V).hom.app x) at h
  rw [assocRightPairComparison_appIso_hom_app] at h
  simpa only [Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- The composability identity of the right-bracketing pairing map, with the two inverse
comparison components cancelled. -/
theorem assocRightPair_snd_eq (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.snd.appFunctor V).map ((R.assocRightPair_firstArrow.appIso V).hom.app x) ≫
        (R.composableComparison.appIso V).hom.app ((R.composable3.fst.appFunctor V).obj x) =
      (R.composableComparison.appIso V).hom.app ((R.assocRightPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.assocRightPair_secondArrow.appIso V).hom.app x) ≫
          ((R.compose_source.appIso V).hom.app ((R.tailPair.appFunctor V).obj x) ≫
            (R.fst.appFunctor V).map ((R.tailPair_firstArrow.appIso V).hom.app x)) :=
  comp_eq_comp_comp_of_comp_inv _ _ _ _ _ _
    (comp_comp_comp_comp_eq_id _ _ _ _
      ((R.compose_source.appIso V).inv_hom_id_app ((R.tailPair.appFunctor V).obj x))
      (R.tailPair_firstArrow_map_inv_hom V x))
    (R.assocRightPair_comparison V x)

/-- The source comparison of the right bracketing of a triple composite. -/
noncomputable def assocRightFstIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.assocRightPair R.compose) R.fst)
      (Pseudofunctor.StrongTrans.vcomp R.composable3.fst
        (Pseudofunctor.StrongTrans.vcomp R.firstArrow R.fst)) :=
  (((StackIso2.associator R.assocRightPair R.compose R.fst).trans
    (StackIso2.whiskerLeft R.assocRightPair R.compose_source)).trans
      (StackIso2.associator R.assocRightPair R.firstArrow R.fst).symm).trans
        ((StackIso2.whiskerRight R.assocRightPair_firstArrow R.fst).trans
          (StackIso2.associator R.composable3.fst R.firstArrow R.fst))

/-- The target comparison of the right bracketing of a triple composite. -/
noncomputable def assocRightSndIso (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp R.assocRightPair R.compose) R.snd)
      (Pseudofunctor.StrongTrans.vcomp R.composable3.snd R.snd) :=
  (((StackIso2.associator R.assocRightPair R.compose R.snd).trans
    (StackIso2.whiskerLeft R.assocRightPair R.compose_target)).trans
      (StackIso2.associator R.assocRightPair R.secondArrow R.snd).symm).trans
        ((StackIso2.whiskerRight R.assocRightPair_secondArrow R.snd).trans
          ((StackIso2.associator R.tailPair R.compose R.snd).trans
            ((StackIso2.whiskerLeft R.tailPair R.compose_target).trans
              ((StackIso2.associator R.tailPair R.secondArrow R.snd).symm.trans
                (StackIso2.whiskerRight R.tailPair_secondArrow R.snd)))))

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `assocRightFstIso`. -/
theorem assocRightFstIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.assocRightFstIso.appIso V).hom.app x =
      (R.compose_source.appIso V).hom.app ((R.assocRightPair.appFunctor V).obj x) ≫
        (R.fst.appFunctor V).map ((R.assocRightPair_firstArrow.appIso V).hom.app x) := by
  dsimp only [assocRightFstIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
  exact comp_idComp _ _

set_option backward.isDefEq.respectTransparency false in
/-- The fibre components of `assocRightSndIso`. -/
theorem assocRightSndIso_appIso_hom_app (R : Genuine f f) (V : Scheme.{u})
    (x : StackFiber R.composable3.pullback V) :
    (R.assocRightSndIso.appIso V).hom.app x =
      (R.compose_target.appIso V).hom.app ((R.assocRightPair.appFunctor V).obj x) ≫
        (R.snd.appFunctor V).map ((R.assocRightPair_secondArrow.appIso V).hom.app x) ≫
          (R.compose_target.appIso V).hom.app ((R.tailPair.appFunctor V).obj x) ≫
            (R.snd.appFunctor V).map ((R.tailPair_secondArrow.appIso V).hom.app x) := by
  dsimp only [assocRightSndIso]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, whiskerRight_appIso_hom_app, symm_appIso_hom_app,
    associator_appIso_inv_app, Category.id_comp, Category.assoc]
  exact comp_idComp_comp_comp_idComp _ _ _ _

/-- **The diagram chase behind the right bracketing of a triple composite**, in an arbitrary
category. -/
theorem assocRightSquare {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {p1 p2 p3 q1 q2 q3 q4 r1 m1 n1 n2 n3 n4 o1 k1 l1 l2 w1 : C}
    {csr : p1 ⟶ p2} {sb1 : p2 ⟶ p3}
    {ctr : q1 ⟶ q2} {tb2 : q2 ⟶ q3} {ctt : q3 ⟶ q4} {tbg2 : q4 ⟶ r1}
    {tb1 : m1 ⟶ n1} {ccp : n1 ⟶ n2}
    {cst : o1 ⟶ n3} {g1m : n3 ⟶ n2} {ccr : m1 ⟶ k1} {sb2 : k1 ⟶ o1}
    {tg1 : n4 ⟶ l1} {c3 : l1 ⟶ l2} {cct : n4 ⟶ w1} {sg2 : w1 ⟶ l2}
    {e : F.obj p3 ⟶ F.obj r1}
    {cmpg1 : F.obj p3 ⟶ F.obj n1} {cmpg2 : F.obj n2 ⟶ F.obj l1}
    {cmpg3 : F.obj l2 ⟶ F.obj r1} {cmpfar : F.obj p2 ⟶ F.obj m1}
    {cmpsar : F.obj k1 ⟶ F.obj q2} {cmpfat : F.obj n3 ⟶ F.obj n4}
    {cmpsat : F.obj w1 ⟶ F.obj q4} {cmpcr : F.obj p1 ⟶ F.obj q1}
    {cmpct : F.obj o1 ⟶ F.obj q3}
    (he : e = cmpg1 ≫ F.map ccp ≫ cmpg2 ≫ F.map c3 ≫ cmpg3)
    (hA1 : F.map csr ≫ cmpfar ≫ F.map ccr ≫ cmpsar = cmpcr ≫ F.map ctr)
    (hA2 : F.map cst ≫ cmpfat ≫ F.map cct ≫ cmpsat = cmpct ≫ F.map ctt)
    (hB : tb1 ≫ ccp = ccr ≫ sb2 ≫ cst ≫ g1m)
    (hC : tg1 ≫ c3 = cct ≫ sg2)
    (hN1 : F.map sb1 ≫ cmpg1 = cmpfar ≫ F.map tb1)
    (hN2 : F.map sb2 ≫ cmpct = cmpsar ≫ F.map tb2)
    (hN3 : F.map g1m ≫ cmpg2 = cmpfat ≫ F.map tg1)
    (hN4 : F.map sg2 ≫ cmpg3 = cmpsat ≫ F.map tbg2) :
    F.map (csr ≫ sb1) ≫ e = cmpcr ≫ F.map (ctr ≫ tb2 ≫ ctt ≫ tbg2) := by
  have hB3 : F.map tb1 ≫ F.map ccp = F.map ccr ≫ F.map sb2 ≫ F.map cst ≫ F.map g1m := by
    simp only [← Functor.map_comp]; rw [hB]
  have hC3 : F.map tg1 ≫ F.map c3 = F.map cct ≫ F.map sg2 := by
    simp only [← Functor.map_comp]; rw [hC]
  rw [he]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hN1, reassoc_of% hB3, reassoc_of% hN3, reassoc_of% hC3, hN4,
    reassoc_of% hA2, reassoc_of% hN2, reassoc_of% hA1]

set_option backward.isDefEq.respectTransparency false in
/-- **The right bracketing of a triple composite classifies `assocCone`.** -/
theorem assocRightClassifies (R : Genuine f f) :
    ConeLiftClassifies R.toStackTwoPullback R.assocCone
      (Pseudofunctor.StrongTrans.vcomp R.assocRightPair R.compose)
      R.assocRightFstIso R.assocRightSndIso := by
  intro V x
  apply Iso.ext
  change
    (f.appFunctor V).map ((R.assocRightFstIso.appIso V).hom.app x) ≫
        (R.assocConeComparison.appIso V).hom.app x =
      (R.comparison.appIso V).hom.app
          ((R.compose.appFunctor V).obj ((R.assocRightPair.appFunctor V).obj x)) ≫
        (f.appFunctor V).map ((R.assocRightSndIso.appIso V).hom.app x)
  rw [assocRightFstIso_appIso_hom_app, assocRightSndIso_appIso_hom_app]
  exact assocRightSquare (R.assocConeComparison_appIso_hom_app V x)
    (R.compose_comparison V ((R.assocRightPair.appFunctor V).obj x))
    (R.compose_comparison V ((R.tailPair.appFunctor V).obj x))
    (R.assocRightPair_snd_eq V x) (R.tailPair_comparison V x)
    (R.comparison_naturality V
      (a := (R.firstArrow.appFunctor V).obj ((R.assocRightPair.appFunctor V).obj x))
      (b := (R.firstArrow.appFunctor V).obj ((R.composable3.fst.appFunctor V).obj x))
      ((R.assocRightPair_firstArrow.appIso V).hom.app x))
    (R.comparison_naturality V
      (a := (R.secondArrow.appFunctor V).obj ((R.assocRightPair.appFunctor V).obj x))
      (b := (R.compose.appFunctor V).obj ((R.tailPair.appFunctor V).obj x))
      ((R.assocRightPair_secondArrow.appIso V).hom.app x))
    (R.comparison_naturality V
      (a := (R.firstArrow.appFunctor V).obj ((R.tailPair.appFunctor V).obj x))
      (b := (R.secondArrow.appFunctor V).obj ((R.composable3.fst.appFunctor V).obj x))
      ((R.tailPair_firstArrow.appIso V).hom.app x))
    (R.comparison_naturality V
      (a := (R.secondArrow.appFunctor V).obj ((R.tailPair.appFunctor V).obj x))
      (b := (R.composable3.snd.appFunctor V).obj x)
      ((R.tailPair_secondArrow.appIso V).hom.app x))

/-- **Associativity of composition in the presentation groupoid.**  The two bracketings of the
composite of a triple of composable arrows are 2-isomorphic as maps
`composable3.pullback ⟶ R.pullback`. -/
noncomputable def compose_assoc (R : Genuine f f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp R.assocLeftPair R.compose)
      (Pseudofunctor.StrongTrans.vcomp R.assocRightPair R.compose) :=
  (R.bilimit.lift_unique R.assocCone
      (Pseudofunctor.StrongTrans.vcomp R.assocLeftPair R.compose)
      R.assocLeftFstIso R.assocLeftSndIso R.assocLeftClassifies).trans
    (R.bilimit.lift_unique R.assocCone
      (Pseudofunctor.StrongTrans.vcomp R.assocRightPair R.compose)
      R.assocRightFstIso R.assocRightSndIso R.assocRightClassifies).symm

end Genuine

namespace PresentationGroupoidObject

variable {U X : FppfStack.{u}} {f : StackHom U X}

/-- The stack of triples of composable arrows of the groupoid object. -/
noncomputable abbrev composable3 (P : PresentationGroupoidObject f) : FppfStack.{u} :=
  P.R.composable3.pullback

/-- **The right unit law** of the presentation groupoid object. -/
noncomputable def unit_compose_right (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.R.rightUnitPair P.compose)
      (Pseudofunctor.StrongTrans.id P.arrows.toPseudofunctor) :=
  P.R.unit_compose_right

/-- **The left unit law** of the presentation groupoid object. -/
noncomputable def unit_compose_left (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.R.leftUnitPair P.compose)
      (Pseudofunctor.StrongTrans.id P.arrows.toPseudofunctor) :=
  P.R.unit_compose_left

/-- **The right inverse law** of the presentation groupoid object. -/
noncomputable def inverse_compose_right (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.R.invPairRight P.compose)
      (Pseudofunctor.StrongTrans.vcomp P.source P.unit) :=
  P.R.inverse_compose_right

/-- **The left inverse law** of the presentation groupoid object. -/
noncomputable def inverse_compose_left (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.R.invPairLeft P.compose)
      (Pseudofunctor.StrongTrans.vcomp P.target P.unit) :=
  P.R.inverse_compose_left

/-- **Associativity of composition** in the presentation groupoid object. -/
noncomputable def compose_assoc (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.R.assocLeftPair P.compose)
      (Pseudofunctor.StrongTrans.vcomp P.R.assocRightPair P.compose) :=
  P.R.compose_assoc

/-- **Inversion is an involution** in the presentation groupoid object. -/
noncomputable def inverse_inverse (P : PresentationGroupoidObject f) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp P.inverse P.inverse)
      (Pseudofunctor.StrongTrans.id P.arrows.toPseudofunctor) :=
  P.R.inverse_inverse

end PresentationGroupoidObject

end StackTwoPullback

/-! ## Agreement with the fibrewise presentation groupoid

For the canonical genuine self two-pullback of an atlas, the fibre of the arrow stack over a test
scheme `T` *is* the categorical pullback `StackInGroupoids.FiberTwoPullback f f T`, whose objects
are precisely the arrows of `PresentationGroupoid f T` by `PresentationGroupoid.arrowEquiv`.
Under that identification the unit, composition and inversion maps constructed in
`Stacks.AtlasRefinement` act as the identity, the composition and the inverse of the fibrewise
groupoid, so the two encodings of the presentation groupoid agree. -/

namespace PresentationGroupoid

variable {U X : FppfStack.{u}} {f : StackHom U X} {T : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The comparison isomorphism carried by a unit arrow of the canonical presentation is the
identity isomorphism. -/
theorem canonicalUnit_iso (a : PresentationGroupoid f T) :
    CategoricalPullback.iso
        (((StackTwoPullback.canonicalGenuine f f).unit.appFunctor T).obj a) =
      Iso.refl ((f.appFunctor T).obj a) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The comparison isomorphism carried by an inverted arrow of the canonical presentation is the
inverse of the original comparison isomorphism. -/
theorem canonicalInverse_iso
    (p : StackFiber (StackTwoPullback.canonicalGenuine f f).pullback T) :
    CategoricalPullback.iso
        (((StackTwoPullback.canonicalGenuine f f).inverse.appFunctor T).obj p) =
      (CategoricalPullback.iso p).symm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The comparison isomorphism carried by a composite arrow of the canonical presentation is the
composite of the two comparison isomorphisms with the atlas image of the composability
isomorphism. -/
theorem canonicalCompose_iso
    (y : StackFiber (StackTwoPullback.canonicalGenuine f f).composable.pullback T) :
    CategoricalPullback.iso
        (((StackTwoPullback.canonicalGenuine f f).compose.appFunctor T).obj y) =
      (CategoricalPullback.iso (CategoricalPullback.fst y)).trans
        (((f.appFunctor T).mapIso (CategoricalPullback.iso y)).trans
          (CategoricalPullback.iso (CategoricalPullback.snd y))) := by
  apply Iso.ext
  change ((StackTwoPullback.canonicalGenuine f f).composeConeComparison.appIso T).hom.app y = _
  rw [StackTwoPullback.Genuine.composeConeComparison_appIso_hom_app]
  exact rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The unit of the presentation groupoid object is the identity arrow of the fibrewise
presentation groupoid.** -/
theorem unit_agrees (a : PresentationGroupoid f T) :
    (⟨CategoricalPullback.iso
      (((StackTwoPullback.canonicalGenuine f f).unit.appFunctor T).obj a)⟩ : Arrow f a a) =
      𝟙 a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Inversion in the presentation groupoid object is inversion in the fibrewise presentation
groupoid.** -/
theorem inverse_agrees {a b : PresentationGroupoid f T} (p : a ⟶ b) :
    (⟨CategoricalPullback.iso
      (((StackTwoPullback.canonicalGenuine f f).inverse.appFunctor T).obj
        ⟨a, b, p.iso⟩)⟩ : Arrow f b a) = Groupoid.inv p :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Composition in the presentation groupoid object is composition in the fibrewise
presentation groupoid.**  A pair of arrows `a ⟶ b` and `b ⟶ c` of the fibrewise groupoid is a
composable pair of the canonical presentation, with identity composability isomorphism, and
`compose` sends it to the composite arrow `a ⟶ c`. -/
theorem compose_agrees {a b c : PresentationGroupoid f T} (p : a ⟶ b) (q : b ⟶ c) :
    (⟨CategoricalPullback.iso
      (((StackTwoPullback.canonicalGenuine f f).compose.appFunctor T).obj
        ⟨⟨a, b, p.iso⟩, ⟨b, c, q.iso⟩, Iso.refl _⟩)⟩ : Arrow f a c) = p ≫ q := by
  apply PresentationGroupoid.Arrow.ext
  rw [canonicalCompose_iso]
  apply Iso.ext
  simp

end PresentationGroupoid

end GromovWitten.AlgebraicGeometry
