/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.InertiaFunctoriality
import GromovWitten.AlgebraicGeometry.Cones.StackBaseChangeComp

/-!
# Coherence of the inertia functoriality construction (issue #38)

`Stacks.InertiaFunctoriality` constructs, for every morphism of fppf stacks `f : X ⟶ Y`, a
morphism `inertiaMap f : inertiaStack X ⟶ inertiaStack Y` as the bilimit lift of an explicit
cone `inertiaMapCone f` over the diagonal of `Y`.  This file proves the two-dimensional
functoriality of that construction and deduces that the inertia stack is invariant under
equivalence of stacks.

## Main results

* `stackDiagonal_naturality_appIso_hom_app` and `stackDiagonal_naturality_appIso_inv_app`: the
  diagonal naturality square `stackDiagonal_naturality f` is *pointwise the identity* natural
  transformation.  This is the computation on which everything else rests.
* `inertiaMapCone_comparison_appIso_hom_app`: the comparison face of `inertiaMapCone f` is, in
  every fibre, the image under `stackProdMap f f` of the comparison face of
  `inertiaPresentation X`.
* `inertiaPresentation_comparison_inertiaMap_app`: consequently the comparison face of
  `inertiaPresentation Y`, evaluated at the image of a point under `inertiaMap f`, is the image
  of the comparison face of `inertiaPresentation X`.
* `inertiaMap_congr`: invertible 2-cells transport through `inertiaMap`.
* `inertiaMap_id`: `inertiaMap` of an identity is 2-isomorphic to the identity.
* `inertiaMap_comp`: `inertiaMap` of a composite is 2-isomorphic to the composite of the
  `inertiaMap`s.
* `inertiaEquivalence`: equivalent stacks have equivalent inertia stacks.  This is the global
  (not merely fibrewise) statement; the fibrewise shadow is
  `inertiaFiberEquivalenceOfStackEquivalence` in `Stacks.Inertia`.
* `stackPair_congr`, `stackProdMap_congr`: the pairing and the product of stack morphisms are
  2-functorial in their arguments.
* `inertiaMap_appFunctor_obj_fst` and `inertiaMap_aut`: on a point of the inertia fibre — an
  object of a fibre together with an automorphism of it — `inertiaMap f` applies `f` to both the
  object and the automorphism.  With `representedStack_aut` (every such automorphism of a
  represented stack is the identity) this identifies the inertia map of a morphism of represented
  stacks with the morphism itself, read through `representedStack_inertiaFiberEquivalence`.

## Implementation notes

All the 2-cells appearing in `stackDiagonal_naturality` and in `inertiaMapCone` are built from
associators, unitors, whiskerings and the `lift_fst`/`lift_snd` cells of the *canonical*
`StackTwoPullback.canonicalGenuine` bilimits, and every one of those is componentwise literally
the identity natural transformation.  The composites are therefore identities as well, but the
intermediate objects are only *definitionally* equal, so `rw`/`simp` regularly fail to see the
composability; the small abstract lemmas `idComp_comp_id`, `idComp_mapId_comp_id`,
`eq_of_mapId_comp`, `idComp_comp_congr`, `idComp_eq_comp_id` and `mapId_comp_law` (all stated in
an arbitrary category, in the style of `Cones/StackCoherence.lean`) are applied with `exact`,
through definitional unfolding, to finish those goals; `rw` is unusable there because the
surrounding terms are not type-correct at `implicit` transparency.  Unfolding
`stackDiagonal_naturality` with
`unfold` before rewriting with `stackProd_ext_hom_fst`/`stackProd_ext_hom_snd` is what makes the
first computation go through: without it the rewrite has to cross the definitional identity
`stackProduct Y Y = stackSelfProduct Y` and fails with an application type mismatch.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false

/-! ## Two-functoriality of products of stack morphisms -/

/-- **The pairing of two stack morphisms is 2-functorial.**  An invertible 2-cell on each
component transports along the pairing. -/
noncomputable def stackPair_congr {T X Y : FppfStack.{u}}
    {p p' : StackHom T X} {q q' : StackHom T Y}
    (α : StackIso2 p p') (β : StackIso2 q q') :
    StackIso2 (stackPair p q) (stackPair p' q') :=
  stackPair_unique _ ((stackPair_fst p q).trans α) ((stackPair_snd p q).trans β)

/-- **The product of two stack morphisms is 2-functorial.** -/
noncomputable def stackProdMap_congr {X Y X' Y' : FppfStack.{u}}
    {f f' : StackHom X X'} {g g' : StackHom Y Y'}
    (α : StackIso2 f f') (β : StackIso2 g g') :
    StackIso2 (stackProdMap f g) (stackProdMap f' g') :=
  stackPair_congr (StackIso2.whiskerLeft (stackProdFst X Y) α)
    (StackIso2.whiskerLeft (stackProdSnd X Y) β)

/-! ## Componentwise identities of the atomic projection 2-cells

Every one of the following 2-cells is a `lift_fst`/`lift_snd` field of a concrete
`StackTwoPullback.canonicalGenuine` bilimit, whose fibrewise construction is designed so that the
lift is *definitionally* (not just isomorphically) equal to the corresponding cone leg on
objects; consequently the comparison 2-cell is literally the identity natural transformation. -/

@[simp]
theorem stackDiagonal_fst_appIso_hom_app (X : FppfStack.{u}) (U : Scheme.{u})
    (x : StackFiber X U) :
    ((stackDiagonal_fst X).appIso U).hom.app x = 𝟙 _ := rfl

@[simp]
theorem stackDiagonal_fst_appIso_inv_app (X : FppfStack.{u}) (U : Scheme.{u})
    (x : StackFiber X U) :
    ((stackDiagonal_fst X).appIso U).inv.app x = 𝟙 _ := rfl

@[simp]
theorem stackDiagonal_snd_appIso_hom_app (X : FppfStack.{u}) (U : Scheme.{u})
    (x : StackFiber X U) :
    ((stackDiagonal_snd X).appIso U).hom.app x = 𝟙 _ := rfl

@[simp]
theorem stackDiagonal_snd_appIso_inv_app (X : FppfStack.{u}) (U : Scheme.{u})
    (x : StackFiber X U) :
    ((stackDiagonal_snd X).appIso U).inv.app x = 𝟙 _ := rfl

@[simp]
theorem inertiaMap_projection_naturality_appIso_hom_app {X Y : FppfStack.{u}}
    (f : StackHom X Y) (U : Scheme.{u}) (x : StackFiber (inertiaStack X) U) :
    ((inertiaMap_projection_naturality f).appIso U).hom.app x = 𝟙 _ := rfl

@[simp]
theorem inertiaMap_secondProjection_naturality_appIso_hom_app {X Y : FppfStack.{u}}
    (f : StackHom X Y) (U : Scheme.{u}) (x : StackFiber (inertiaStack X) U) :
    ((inertiaMap_secondProjection_naturality f).appIso U).hom.app x = 𝟙 _ := rfl

namespace StackIso2

/-- The `inv` component of a left whiskering, matching `whiskerLeft_appIso_hom_app`. -/
@[simp]
theorem whiskerLeft_appIso_inv_app {A B C : FppfStack.{u}} (q : StackHom A B)
    {f g : StackHom B C} (e : StackIso2 f g) (U : Scheme.{u}) (x : StackFiber A U) :
    ((StackIso2.whiskerLeft q e).appIso U).inv.app x =
      (e.appIso U).inv.app ((q.appFunctor U).obj x) := rfl

/-- The `inv` component of a right whiskering, matching `whiskerRight_appIso_hom_app`. -/
@[simp]
theorem whiskerRight_appIso_inv_app {A B C : FppfStack.{u}} {f g : StackHom A B}
    (e : StackIso2 f g) (r : StackHom B C) (U : Scheme.{u}) (x : StackFiber A U) :
    ((StackIso2.whiskerRight e r).appIso U).inv.app x =
      (r.appFunctor U).map ((e.appIso U).inv.app x) := rfl

/-- The `inv` component of the inverse of an invertible 2-cell. -/
@[simp]
theorem symm_appIso_inv_app {A B : FppfStack.{u}} {p q : StackHom A B}
    (e : StackIso2 p q) (U : Scheme.{u}) (x : StackFiber A U) :
    (e.symm.appIso U).inv.app x = (e.appIso U).hom.app x := rfl

end StackIso2

/-- The `inv` component of a transitivity composite, matching `StackTwoPullback.
trans_appIso_hom_app`. -/
@[simp]
theorem StackTwoPullback.trans_appIso_inv_app {A B : FppfStack.{u}} {p q r : StackHom A B}
    (e : StackIso2 p q) (e' : StackIso2 q r) (U : Scheme.{u}) (x : StackFiber A U) :
    ((e.trans e').appIso U).inv.app x =
      (e'.appIso U).inv.app x ≫ (e.appIso U).inv.app x := rfl

/-! ## Abstract identity-composition lemmas

The intermediate objects of the composites below are only definitionally equal, so `simp` cannot
use `Category.id_comp`/`Category.comp_id` on them.  These statements in an arbitrary category are
applied through definitional unfolding instead, exactly as in `Cones/StackCoherence.lean`. -/

/-- An arrow surrounded by identities, in an arbitrary category. -/
theorem idComp_comp_id {W : Type*} [Category W] {a b : W} (v : a ⟶ b) :
    (𝟙 a ≫ v) ≫ 𝟙 b = v := by simp

/-- Identities around the image of an identity, in an arbitrary category. -/
theorem idComp_mapId_comp_id {W V : Type*} [Category W] [Category V] (F : W ⥤ V) (a : W) :
    (𝟙 (F.obj a) ≫ F.map (𝟙 a)) ≫ 𝟙 (F.obj a) = 𝟙 (F.obj a) := by simp

/-! ## The diagonal naturality square is the identity -/

/-- **The diagonal naturality square of a stack morphism is pointwise the identity.**  Both of
its product components reduce, through `stackProd_ext_hom_fst`/`stackProd_ext_hom_snd`, to
composites of identity components of associators, unitors, whiskerings and the projection cells
of the canonical bilimits. -/
theorem stackDiagonal_naturality_appIso_hom_app {X Y : FppfStack.{u}} (f : StackHom X Y)
    (T : Scheme.{u}) (z : StackFiber X T) :
    ((stackDiagonal_naturality f).appIso T).hom.app z = 𝟙 _ := by
  apply CategoricalPullback.hom_ext
  · unfold stackDiagonal_naturality
    rw [stackProd_ext_hom_fst]
    simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
      StackIso2.whiskerLeft_appIso_hom_app, StackIso2.whiskerRight_appIso_hom_app,
      StackIso2.symm_appIso_hom_app, StackTwoPullback.leftUnitor_appIso_hom_app,
      StackIso2.associator_appIso_inv_app, stackProdMap_fst_hom_app,
      stackDiagonal_fst_appIso_hom_app, StackTwoPullback.trans_appIso_inv_app,
      StackTwoPullback.rightUnitor_appIso_inv_app, StackIso2.whiskerLeft_appIso_inv_app,
      stackDiagonal_fst_appIso_inv_app, Category.id_comp, Category.comp_id]
    exact idComp_mapId_comp_id (f.appFunctor T) _
  · unfold stackDiagonal_naturality
    rw [stackProd_ext_hom_snd]
    simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
      StackIso2.whiskerLeft_appIso_hom_app, StackIso2.whiskerRight_appIso_hom_app,
      StackIso2.symm_appIso_hom_app, StackTwoPullback.leftUnitor_appIso_hom_app,
      StackIso2.associator_appIso_inv_app, stackProdMap_snd_hom_app,
      stackDiagonal_snd_appIso_hom_app, StackTwoPullback.trans_appIso_inv_app,
      StackTwoPullback.rightUnitor_appIso_inv_app, StackIso2.whiskerLeft_appIso_inv_app,
      stackDiagonal_snd_appIso_inv_app, Category.id_comp, Category.comp_id]
    exact idComp_mapId_comp_id (f.appFunctor T) _

/-- The inverse of the diagonal naturality square is pointwise the identity as well. -/
theorem stackDiagonal_naturality_appIso_inv_app {X Y : FppfStack.{u}} (f : StackHom X Y)
    (T : Scheme.{u}) (z : StackFiber X T) :
    ((stackDiagonal_naturality f).appIso T).inv.app z = 𝟙 _ := by
  have h := ((stackDiagonal_naturality f).appIso T).hom_inv_id_app z
  rw [stackDiagonal_naturality_appIso_hom_app, Category.id_comp] at h
  exact h

/-! ## The comparison face of the inertia cone -/

/-- **The comparison face of `inertiaMapCone f` is the image of the comparison face of the source
inertia presentation.**  All the remaining factors of the composite defining it are identities,
by `stackDiagonal_naturality_appIso_hom_app`. -/
theorem inertiaMapCone_comparison_appIso_hom_app {X Y : FppfStack.{u}} (f : StackHom X Y)
    (U : Scheme.{u}) (x : StackFiber (inertiaStack X) U) :
    ((inertiaMapCone f).comparison.appIso U).hom.app x =
      ((stackProdMap f f).appFunctor U).map
        (((inertiaPresentation X).comparison.appIso U).hom.app x) := by
  unfold inertiaMapCone
  dsimp only
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, StackIso2.whiskerRight_appIso_hom_app,
    StackIso2.symm_appIso_hom_app, StackIso2.associator_appIso_inv_app,
    StackTwoPullback.trans_appIso_inv_app, StackIso2.whiskerLeft_appIso_inv_app,
    StackIso2.symm_appIso_inv_app, stackDiagonal_naturality_appIso_hom_app,
    stackDiagonal_naturality_appIso_inv_app, Category.id_comp, Category.comp_id]
  exact idComp_comp_id _

/-! ## Alignment lemmas

Object and arrow spellings that are definitionally but not syntactically equal, recorded as `rfl`
simp lemmas so that `simp` can align the two sides of the coherence equations below. -/

/-- The identity stack morphism acts as the identity on objects of every fibre. -/
@[simp]
theorem identityAppFunctor_obj (A : FppfStack.{u}) (U : Scheme.{u}) (x : StackFiber A U) :
    (StackHom.appFunctor (Pseudofunctor.StrongTrans.id A.toPseudofunctor) U).obj x = x := rfl

/-- The inertia projection of the image of a point under `inertiaMap f`. -/
@[simp]
theorem inertiaProjection_inertiaMap_appFunctor_obj {X Y : FppfStack.{u}} (f : StackHom X Y)
    (U : Scheme.{u}) (x : StackFiber (inertiaStack X) U) :
    ((inertiaProjection Y).appFunctor U).obj (((inertiaMap f).appFunctor U).obj x) =
      (f.appFunctor U).obj (((inertiaProjection X).appFunctor U).obj x) := rfl

/-- The second inertia projection of the image of a point under `inertiaMap f`. -/
@[simp]
theorem inertiaSecondProjection_inertiaMap_appFunctor_obj {X Y : FppfStack.{u}}
    (f : StackHom X Y) (U : Scheme.{u}) (x : StackFiber (inertiaStack X) U) :
    ((inertiaPresentation Y).snd.appFunctor U).obj (((inertiaMap f).appFunctor U).obj x) =
      (f.appFunctor U).obj (((inertiaPresentation X).snd.appFunctor U).obj x) := rfl

/-- The first component of a composite in a fibre of a self product. -/
@[simp]
theorem stackSelfProduct_comp_fst {X : FppfStack.{u}} {T : Scheme.{u}}
    {p q r : StackFiber (stackSelfProduct X).pullback T} (a : p ⟶ q) (b : q ⟶ r) :
    (a ≫ b).fst = a.fst ≫ b.fst := rfl

/-- The second component of a composite in a fibre of a self product. -/
@[simp]
theorem stackSelfProduct_comp_snd {X : FppfStack.{u}} {T : Scheme.{u}}
    {p q r : StackFiber (stackSelfProduct X).pullback T} (a : p ⟶ q) (b : q ⟶ r) :
    (a ≫ b).snd = a.snd ≫ b.snd := rfl

/-- Cancelling images of identities on both sides of an equation. -/
theorem eq_of_mapId_comp {W V : Type*} [Category W] [Category V] (F : W ⥤ V)
    {a b : W} {u v : F.obj a ⟶ F.obj b}
    (h : F.map (𝟙 a) ≫ u = v ≫ F.map (𝟙 b)) : v = u := by
  rw [F.map_id, F.map_id, Category.id_comp, Category.comp_id] at h
  exact h.symm

/-- An identity-prefixed composite, given the underlying equation.  Stated abstractly because
`rw [Category.id_comp]` is not usable in the goals below: the ambient terms are not type-correct
at `implicit` transparency. -/
theorem idComp_comp_congr {W : Type*} [Category W] {a b c d : W} {v : a ⟶ b} {w : b ⟶ c}
    {u : a ⟶ d} {t : d ⟶ c} (h : v ≫ w = u ≫ t) : (𝟙 a ≫ v) ≫ w = u ≫ t := by
  rw [Category.id_comp]; exact h

/-! ## The comparison face at an image point -/

/-- **The comparison face of `inertiaPresentation Y` at the image of a point under
`inertiaMap f`** is the image of the comparison face of `inertiaPresentation X`.  This is the
compatibility clause `inertiaMap_cone_classifies`, made explicit. -/
theorem inertiaPresentation_comparison_inertiaMap_app {X Y : FppfStack.{u}} (f : StackHom X Y)
    (U : Scheme.{u}) (x : StackFiber (inertiaStack X) U) :
    ((inertiaPresentation Y).comparison.appIso U).hom.app
        (((inertiaMap f).appFunctor U).obj x) =
      ((stackProdMap f f).appFunctor U).map
        (((inertiaPresentation X).comparison.appIso U).hom.app x) := by
  have h := congrArg Iso.hom (inertiaMap_cone_classifies f U x)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    inertiaMap_projection_naturality_appIso_hom_app,
    inertiaMap_secondProjection_naturality_appIso_hom_app,
    inertiaMapCone_comparison_appIso_hom_app] at h
  exact eq_of_mapId_comp ((stackDiagonal Y).appFunctor U) h

/-! ## Two-functoriality in 2-cells -/

/-- The first projection cell used for `inertiaMap_congr`. -/
noncomputable def inertiaMapCongrFst {X Y : FppfStack.{u}} {f g : StackHom X Y}
    (e : StackIso2 f g) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (inertiaMap f) (inertiaProjection Y))
      (Pseudofunctor.StrongTrans.vcomp (inertiaProjection X) g) :=
  (inertiaMap_projection_naturality f).trans
    (StackIso2.whiskerLeft (inertiaProjection X) e)

/-- The second projection cell used for `inertiaMap_congr`. -/
noncomputable def inertiaMapCongrSnd {X Y : FppfStack.{u}} {f g : StackHom X Y}
    (e : StackIso2 f g) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp (inertiaMap f) (inertiaPresentation Y).snd)
      (Pseudofunctor.StrongTrans.vcomp (inertiaPresentation X).snd g) :=
  (inertiaMap_secondProjection_naturality f).trans
    (StackIso2.whiskerLeft (inertiaPresentation X).snd e)

/-- **`inertiaMap f` classifies the cone of `g`** whenever `f` and `g` are 2-isomorphic.  In every
fibre the comparison equation is exactly the naturality of the fibre component of the given
2-cell at the comparison arrow of `inertiaPresentation X`. -/
theorem inertiaMapCongr_classifies {X Y : FppfStack.{u}} {f g : StackHom X Y}
    (e : StackIso2 f g) :
    StackTwoPullback.ConeLiftClassifies (inertiaPresentation Y).toStackTwoPullback
      (inertiaMapCone g) (inertiaMap f) (inertiaMapCongrFst e) (inertiaMapCongrSnd e) := by
  intro U x
  apply Iso.ext
  apply CategoricalPullback.hom_ext
  · simp only [inertiaMapCongrFst, inertiaMapCongrSnd, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, StackTwoPullback.trans_appIso_hom_app,
      inertiaMap_projection_naturality_appIso_hom_app,
      inertiaMap_secondProjection_naturality_appIso_hom_app,
      StackIso2.whiskerLeft_appIso_hom_app, inertiaMapCone_comparison_appIso_hom_app,
      inertiaPresentation_comparison_inertiaMap_app,
      inertiaProjection_inertiaMap_appFunctor_obj,
      inertiaSecondProjection_inertiaMap_appFunctor_obj,
      StackTwoPullback.vcomp_appFunctor_obj,
      Category.id_comp, stackSelfProduct_comp_fst, stackDiagonal_app_map_fst,
      stackProdMap_app_map_fst]
    exact idComp_comp_congr ((e.appIso U).hom.naturality _).symm
  · simp only [inertiaMapCongrFst, inertiaMapCongrSnd, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, StackTwoPullback.trans_appIso_hom_app,
      inertiaMap_projection_naturality_appIso_hom_app,
      inertiaMap_secondProjection_naturality_appIso_hom_app,
      StackIso2.whiskerLeft_appIso_hom_app, inertiaMapCone_comparison_appIso_hom_app,
      inertiaPresentation_comparison_inertiaMap_app,
      inertiaProjection_inertiaMap_appFunctor_obj,
      inertiaSecondProjection_inertiaMap_appFunctor_obj,
      StackTwoPullback.vcomp_appFunctor_obj,
      Category.id_comp, stackSelfProduct_comp_snd, stackDiagonal_app_map_snd,
      stackProdMap_app_map_snd]
    exact idComp_comp_congr ((e.appIso U).hom.naturality _).symm

/-- **The inertia map is 2-functorial on invertible 2-cells.** -/
noncomputable def inertiaMap_congr {X Y : FppfStack.{u}} {f g : StackHom X Y}
    (e : StackIso2 f g) : StackIso2 (inertiaMap f) (inertiaMap g) :=
  (inertiaPresentation Y).bilimit.lift_unique (inertiaMapCone g) (inertiaMap f)
    (inertiaMapCongrFst e) (inertiaMapCongrSnd e) (inertiaMapCongr_classifies e)

/-! ## Identity and composition coherence -/

/-- An arrow with an identity on either side, in an arbitrary category. -/
theorem idComp_eq_comp_id {W : Type*} [Category W] {a b : W} (v : a ⟶ b) :
    𝟙 a ≫ v = v ≫ 𝟙 b := by simp

/-- Images of identities on either side of the image of an arrow, in an arbitrary category. -/
theorem mapId_comp_law {W V : Type*} [Category W] [Category V] (F : W ⥤ V) {a b : W}
    (v : a ⟶ b) :
    (𝟙 (F.obj a) ≫ F.map (𝟙 a)) ≫ F.map v = F.map v ≫ F.map (𝟙 b) := by simp

/-- The first projection cell used for `inertiaMap_id`. -/
noncomputable def inertiaMapIdFst (X : FppfStack.{u}) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (inertiaStack X).toPseudofunctor) (inertiaProjection X))
      (Pseudofunctor.StrongTrans.vcomp (inertiaProjection X)
        (Pseudofunctor.StrongTrans.id X.toPseudofunctor)) :=
  (StackIso2.leftUnitor (inertiaProjection X)).trans
    (StackIso2.rightUnitor (inertiaProjection X)).symm

/-- The second projection cell used for `inertiaMap_id`. -/
noncomputable def inertiaMapIdSnd (X : FppfStack.{u}) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (inertiaStack X).toPseudofunctor)
        (inertiaPresentation X).snd)
      (Pseudofunctor.StrongTrans.vcomp (inertiaPresentation X).snd
        (Pseudofunctor.StrongTrans.id X.toPseudofunctor)) :=
  (StackIso2.leftUnitor (inertiaPresentation X).snd).trans
    (StackIso2.rightUnitor (inertiaPresentation X).snd).symm

/-- **The identity of the inertia stack classifies the cone of the identity morphism.** -/
theorem inertiaMapId_classifies (X : FppfStack.{u}) :
    StackTwoPullback.ConeLiftClassifies (inertiaPresentation X).toStackTwoPullback
      (inertiaMapCone (Pseudofunctor.StrongTrans.id X.toPseudofunctor))
      (Pseudofunctor.StrongTrans.id (inertiaStack X).toPseudofunctor)
      (inertiaMapIdFst X) (inertiaMapIdSnd X) := by
  intro U x
  apply Iso.ext
  apply CategoricalPullback.hom_ext
  · simp only [inertiaMapIdFst, inertiaMapIdSnd, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      StackTwoPullback.trans_appIso_hom_app, StackTwoPullback.leftUnitor_appIso_hom_app,
      StackIso2.symm_appIso_hom_app, StackTwoPullback.rightUnitor_appIso_inv_app,
      inertiaMapCone_comparison_appIso_hom_app, identityAppFunctor_obj,
      StackTwoPullback.identityAppFunctor_map, StackTwoPullback.vcomp_appFunctor_obj,
      stackSelfProduct_comp_fst, stackDiagonal_app_map_fst, stackProdMap_app_map_fst,
      Category.comp_id]
    exact idComp_eq_comp_id _
  · simp only [inertiaMapIdFst, inertiaMapIdSnd, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      StackTwoPullback.trans_appIso_hom_app, StackTwoPullback.leftUnitor_appIso_hom_app,
      StackIso2.symm_appIso_hom_app, StackTwoPullback.rightUnitor_appIso_inv_app,
      inertiaMapCone_comparison_appIso_hom_app, identityAppFunctor_obj,
      StackTwoPullback.identityAppFunctor_map, StackTwoPullback.vcomp_appFunctor_obj,
      stackSelfProduct_comp_snd, stackDiagonal_app_map_snd, stackProdMap_app_map_snd,
      Category.comp_id]
    exact idComp_eq_comp_id _

/-- **The inertia map of an identity is the identity**, up to an invertible 2-cell. -/
noncomputable def inertiaMap_id (X : FppfStack.{u}) :
    StackIso2 (inertiaMap (Pseudofunctor.StrongTrans.id X.toPseudofunctor))
      (Pseudofunctor.StrongTrans.id (inertiaStack X).toPseudofunctor) :=
  ((inertiaPresentation X).bilimit.lift_unique
    (inertiaMapCone (Pseudofunctor.StrongTrans.id X.toPseudofunctor))
    (Pseudofunctor.StrongTrans.id (inertiaStack X).toPseudofunctor)
    (inertiaMapIdFst X) (inertiaMapIdSnd X) (inertiaMapId_classifies X)).symm

/-- The first projection cell used for `inertiaMap_comp`. -/
noncomputable def inertiaMapCompFst {X Y Z : FppfStack.{u}} (f : StackHom X Y)
    (g : StackHom Y Z) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (inertiaMap f) (inertiaMap g)) (inertiaProjection Z))
      (Pseudofunctor.StrongTrans.vcomp (inertiaProjection X)
        (Pseudofunctor.StrongTrans.vcomp f g)) :=
  ((((StackIso2.associator (inertiaMap f) (inertiaMap g) (inertiaProjection Z)).trans
    (StackIso2.whiskerLeft (inertiaMap f) (inertiaMap_projection_naturality g))).trans
    (StackIso2.associator (inertiaMap f) (inertiaProjection Y) g).symm).trans
    (StackIso2.whiskerRight (inertiaMap_projection_naturality f) g)).trans
    (StackIso2.associator (inertiaProjection X) f g)

/-- The second projection cell used for `inertiaMap_comp`. -/
noncomputable def inertiaMapCompSnd {X Y Z : FppfStack.{u}} (f : StackHom X Y)
    (g : StackHom Y Z) :
    StackIso2 (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (inertiaMap f) (inertiaMap g))
        (inertiaPresentation Z).snd)
      (Pseudofunctor.StrongTrans.vcomp (inertiaPresentation X).snd
        (Pseudofunctor.StrongTrans.vcomp f g)) :=
  ((((StackIso2.associator (inertiaMap f) (inertiaMap g) (inertiaPresentation Z).snd).trans
    (StackIso2.whiskerLeft (inertiaMap f) (inertiaMap_secondProjection_naturality g))).trans
    (StackIso2.associator (inertiaMap f) (inertiaPresentation Y).snd g).symm).trans
    (StackIso2.whiskerRight (inertiaMap_secondProjection_naturality f) g)).trans
    (StackIso2.associator (inertiaPresentation X).snd f g)

/-- **The composite of two inertia maps classifies the cone of the composite morphism.** -/
theorem inertiaMapComp_classifies {X Y Z : FppfStack.{u}} (f : StackHom X Y)
    (g : StackHom Y Z) :
    StackTwoPullback.ConeLiftClassifies (inertiaPresentation Z).toStackTwoPullback
      (inertiaMapCone (Pseudofunctor.StrongTrans.vcomp f g))
      (Pseudofunctor.StrongTrans.vcomp (inertiaMap f) (inertiaMap g))
      (inertiaMapCompFst f g) (inertiaMapCompSnd f g) := by
  intro U x
  apply Iso.ext
  apply CategoricalPullback.hom_ext
  · simp only [inertiaMapCompFst, inertiaMapCompSnd, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, StackTwoPullback.trans_appIso_hom_app,
      StackIso2.associator_appIso_hom_app, StackIso2.symm_appIso_hom_app,
      StackIso2.associator_appIso_inv_app, StackIso2.whiskerLeft_appIso_hom_app,
      StackIso2.whiskerRight_appIso_hom_app,
      inertiaMap_projection_naturality_appIso_hom_app,
      inertiaMap_secondProjection_naturality_appIso_hom_app,
      inertiaMapCone_comparison_appIso_hom_app,
      inertiaPresentation_comparison_inertiaMap_app,
      inertiaProjection_inertiaMap_appFunctor_obj,
      inertiaSecondProjection_inertiaMap_appFunctor_obj,
      StackTwoPullback.vcomp_appFunctor_obj, StackTwoPullback.vcomp_appFunctor_map,
      stackSelfProduct_comp_fst, stackDiagonal_app_map_fst, stackProdMap_app_map_fst,
      Category.id_comp, Category.comp_id]
    exact mapId_comp_law (g.appFunctor U) _
  · simp only [inertiaMapCompFst, inertiaMapCompSnd, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, StackTwoPullback.trans_appIso_hom_app,
      StackIso2.associator_appIso_hom_app, StackIso2.symm_appIso_hom_app,
      StackIso2.associator_appIso_inv_app, StackIso2.whiskerLeft_appIso_hom_app,
      StackIso2.whiskerRight_appIso_hom_app,
      inertiaMap_projection_naturality_appIso_hom_app,
      inertiaMap_secondProjection_naturality_appIso_hom_app,
      inertiaMapCone_comparison_appIso_hom_app,
      inertiaPresentation_comparison_inertiaMap_app,
      inertiaProjection_inertiaMap_appFunctor_obj,
      inertiaSecondProjection_inertiaMap_appFunctor_obj,
      StackTwoPullback.vcomp_appFunctor_obj, StackTwoPullback.vcomp_appFunctor_map,
      stackSelfProduct_comp_snd, stackDiagonal_app_map_snd, stackProdMap_app_map_snd,
      Category.id_comp, Category.comp_id]
    exact mapId_comp_law (g.appFunctor U) _

/-- **The inertia map of a composite is the composite of the inertia maps**, up to an invertible
2-cell. -/
noncomputable def inertiaMap_comp {X Y Z : FppfStack.{u}} (f : StackHom X Y)
    (g : StackHom Y Z) :
    StackIso2 (inertiaMap (Pseudofunctor.StrongTrans.vcomp f g))
      (Pseudofunctor.StrongTrans.vcomp (inertiaMap f) (inertiaMap g)) :=
  ((inertiaPresentation Z).bilimit.lift_unique
    (inertiaMapCone (Pseudofunctor.StrongTrans.vcomp f g))
    (Pseudofunctor.StrongTrans.vcomp (inertiaMap f) (inertiaMap g))
    (inertiaMapCompFst f g) (inertiaMapCompSnd f g) (inertiaMapComp_classifies f g)).symm

/-! ## Invariance of the inertia stack under equivalence -/

/-- **Equivalent fppf stacks have equivalent inertia stacks.**  The two composition laws come from
`inertiaMap_comp`, `inertiaMap_congr` and `inertiaMap_id`.  This is the global statement; its
fibrewise shadow is `inertiaFiberEquivalenceOfStackEquivalence`. -/
noncomputable def inertiaEquivalence {X Y : FppfStack.{u}} (e : StackEquivalenceData X Y) :
    StackEquivalenceData (inertiaStack X) (inertiaStack Y) where
  hom := inertiaMap e.hom
  inv := inertiaMap e.inv
  homInv := (((inertiaMap_comp e.hom e.inv).symm.trans
    (inertiaMap_congr e.homInv)).trans (inertiaMap_id X))
  invHom := (((inertiaMap_comp e.inv e.hom).symm.trans
    (inertiaMap_congr e.invHom)).trans (inertiaMap_id Y))

/-! ## The inertia map on objects with automorphisms

A point of the inertia fibre `InertiaFiber X T` is an object of `X(T)` together with an
automorphism of it (`Stacks.Inertia`'s `InertiaFiber.aut`, `inertiaFiberEquivalence`).  The
lemmas below identify `inertiaMap f` in these terms: it applies `f` to the object and to the
automorphism.  For a stack with thin fibres -- in particular a represented stack -- the
automorphism part is forced to be the identity, so `inertiaMap f` is just `f`. -/

/-- The underlying object of the image of a point of the inertia fibre. -/
theorem inertiaMap_appFunctor_obj_fst {X Y : FppfStack.{u}} (f : StackHom X Y) (T : Scheme.{u})
    (p : InertiaFiber X T) :
    CategoricalPullback.fst (((inertiaMap f).appFunctor T).obj p) =
      (f.appFunctor T).obj (CategoricalPullback.fst p) := rfl

/-- The comparison face of the inertia presentation is the structural isomorphism of the point of
the inertia fibre. -/
theorem inertiaPresentation_comparison_appIso_hom_app (X : FppfStack.{u}) (T : Scheme.{u})
    (p : InertiaFiber X T) :
    ((inertiaPresentation X).comparison.appIso T).hom.app p = p.iso.hom := rfl

/-- The inverse comparison face of the inertia presentation. -/
theorem inertiaPresentation_comparison_appIso_inv_app (X : FppfStack.{u}) (T : Scheme.{u})
    (p : InertiaFiber X T) :
    ((inertiaPresentation X).comparison.appIso T).inv.app p = p.iso.inv := rfl

/-- The comparison isomorphism of the image of a point under the inertia map. -/
theorem inertiaMap_appFunctor_obj_iso_hom {X Y : FppfStack.{u}} (f : StackHom X Y)
    (T : Scheme.{u}) (p : InertiaFiber X T) :
    (((inertiaMap f).appFunctor T).obj p).iso.hom =
      ((inertiaMapCone f).comparison.appIso T).hom.app p := rfl

/-- The inverse comparison isomorphism of the image of a point under the inertia map. -/
theorem inertiaMap_appFunctor_obj_iso_inv {X Y : FppfStack.{u}} (f : StackHom X Y)
    (T : Scheme.{u}) (p : InertiaFiber X T) :
    (((inertiaMap f).appFunctor T).obj p).iso.inv =
      ((inertiaMapCone f).comparison.appIso T).inv.app p := rfl

/-- The inverse of the comparison face of `inertiaMapCone f`. -/
theorem inertiaMapCone_comparison_appIso_inv_app {X Y : FppfStack.{u}} (f : StackHom X Y)
    (U : Scheme.{u}) (x : StackFiber (inertiaStack X) U) :
    ((inertiaMapCone f).comparison.appIso U).inv.app x =
      ((stackProdMap f f).appFunctor U).map
        (((inertiaPresentation X).comparison.appIso U).inv.app x) := by
  have h : ((inertiaMapCone f).comparison.appIso U).app x =
      ((stackProdMap f f).appFunctor U).mapIso
        (((inertiaPresentation X).comparison.appIso U).app x) :=
    Iso.ext (inertiaMapCone_comparison_appIso_hom_app f U x)
  exact congrArg Iso.inv h

/-- The inertia map preserves the first leg of a point of the inertia fibre. -/
theorem inertiaMap_firstLeg_hom {X Y : FppfStack.{u}} (f : StackHom X Y) (T : Scheme.{u})
    (p : InertiaFiber X T) :
    (InertiaFiber.firstLeg (((inertiaMap f).appFunctor T).obj p)).hom =
      (f.appFunctor T).map (InertiaFiber.firstLeg p).hom := by
  change (((inertiaMap f).appFunctor T).obj p).iso.hom.fst = _
  rw [inertiaMap_appFunctor_obj_iso_hom, inertiaMapCone_comparison_appIso_hom_app,
    stackProdMap_app_map_fst, inertiaPresentation_comparison_appIso_hom_app]
  rfl

/-- The inertia map preserves the inverse of the second leg of a point of the inertia fibre. -/
theorem inertiaMap_secondLeg_inv {X Y : FppfStack.{u}} (f : StackHom X Y) (T : Scheme.{u})
    (p : InertiaFiber X T) :
    (InertiaFiber.secondLeg (((inertiaMap f).appFunctor T).obj p)).inv =
      (f.appFunctor T).map (InertiaFiber.secondLeg p).inv := by
  change (((inertiaMap f).appFunctor T).obj p).iso.inv.snd = _
  rw [inertiaMap_appFunctor_obj_iso_inv, inertiaMapCone_comparison_appIso_inv_app,
    stackProdMap_app_map_snd, inertiaPresentation_comparison_appIso_inv_app]
  rfl

/-- **The inertia map acts on automorphisms by applying the morphism.** -/
theorem inertiaMap_aut {X Y : FppfStack.{u}} (f : StackHom X Y) (T : Scheme.{u})
    (p : InertiaFiber X T) :
    InertiaFiber.aut (((inertiaMap f).appFunctor T).obj p) =
      (f.appFunctor T).map (InertiaFiber.aut p) := by
  rw [InertiaFiber.aut_eq, InertiaFiber.aut_eq, Functor.map_comp, inertiaMap_firstLeg_hom,
    inertiaMap_secondLeg_inv]

/-- **The automorphism attached to a point of the inertia fibre of a represented stack is
trivial.**  With `inertiaMap_appFunctor_obj_fst` this says that the inertia map of a morphism of
represented stacks is that morphism, read through
`representedStack_inertiaFiberEquivalence`. -/
theorem representedStack_aut (S T : Scheme.{u}) (p : InertiaFiber (representedStack S) T) :
    InertiaFiber.aut p = 𝟙 _ :=
  (representedStack_hom_subsingleton S T _ _).elim _ _

end GromovWitten.AlgebraicGeometry
