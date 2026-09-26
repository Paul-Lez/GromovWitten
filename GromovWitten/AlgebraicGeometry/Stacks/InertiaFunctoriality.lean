/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.StackProductProjections

/-!
# Functoriality of the inertia construction

The inertia stack is a genuine two-pullback of the diagonal.  This file constructs its map
along an arbitrary stack morphism by giving the actual cone over the target diagonal.  The
comparison face of that cone is retained throughout; in particular this construction does not
replace the two-pullback by a strict equalizer of objects.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false

/-! ## Naturality of the diagonal -/

/-- The diagonal square associated to a stack morphism `f`.

The two component cells are obtained from the two product projections.  Thus this is a genuine
2-cell between the diagonal followed by `f × f` and `f` followed by the target diagonal. -/
noncomputable def stackDiagonal_naturality {X Y : FppfStack.{u}}
    (f : StackHom X Y) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (stackDiagonal X) (stackProdMap f f))
      (Pseudofunctor.StrongTrans.vcomp f (stackDiagonal Y)) := by
  apply stackProd_ext
  · exact
      let left :=
        (((StackIso2.associator (stackDiagonal X) (stackProdMap f f)
            (stackProdFst Y Y)).trans
          (StackIso2.whiskerLeft (stackDiagonal X) (stackProdMap_fst f f))).trans
          (StackIso2.associator (stackDiagonal X) (stackProdFst X X) f).symm).trans
          (StackIso2.whiskerRight (stackDiagonal_fst X) f)
      let right :=
        ((StackIso2.associator f (stackDiagonal Y) (stackProdFst Y Y)).trans
          (StackIso2.whiskerLeft f (stackDiagonal_fst Y))).trans
          (StackIso2.rightUnitor f)
      (left.trans (StackIso2.leftUnitor f)).trans right.symm
  · exact
      let left :=
        (((StackIso2.associator (stackDiagonal X) (stackProdMap f f)
            (stackProdSnd Y Y)).trans
          (StackIso2.whiskerLeft (stackDiagonal X) (stackProdMap_snd f f))).trans
          (StackIso2.associator (stackDiagonal X) (stackProdSnd X X) f).symm).trans
          (StackIso2.whiskerRight (stackDiagonal_snd X) f)
      let right :=
        ((StackIso2.associator f (stackDiagonal Y) (stackProdSnd Y Y)).trans
          (StackIso2.whiskerLeft f (stackDiagonal_snd Y))).trans
          (StackIso2.rightUnitor f)
      (left.trans (StackIso2.leftUnitor f)).trans right.symm

/-! ## The target cone and the global inertia map -/

/-- The cone over the target diagonal used to define the inertia map.

Its comparison is the source inertia comparison transported across the diagonal square. -/
noncomputable def inertiaMapCone {X Y : FppfStack.{u}} (f : StackHom X Y) :
    StackTwoPullback.Cone (f := stackDiagonal Y) (g := stackDiagonal Y)
      (inertiaStack X) where
  fst := Pseudofunctor.StrongTrans.vcomp (inertiaProjection X) f
  snd := Pseudofunctor.StrongTrans.vcomp (inertiaPresentation X).snd f
  comparison := by
    let fstCell :=
      (StackIso2.associator (inertiaProjection X) f (stackDiagonal Y)).trans
        (StackIso2.whiskerLeft (inertiaProjection X)
          (stackDiagonal_naturality f).symm)
    let sndCell :=
      (StackIso2.associator (inertiaPresentation X).snd f (stackDiagonal Y)).trans
        (StackIso2.whiskerLeft (inertiaPresentation X).snd
          (stackDiagonal_naturality f).symm)
    exact
      (((fstCell.trans
        (StackIso2.associator (inertiaProjection X) (stackDiagonal X)
          (stackProdMap f f)).symm)).trans
        (StackIso2.whiskerRight (inertiaPresentation X).comparison
          (stackProdMap f f))).trans
        ((StackIso2.associator (inertiaPresentation X).snd (stackDiagonal X)
          (stackProdMap f f)).trans sndCell.symm)

/-- The global inertia map associated to a stack morphism. -/
noncomputable def inertiaMap {X Y : FppfStack.{u}} (f : StackHom X Y) :
    StackHom (inertiaStack X) (inertiaStack Y) :=
  (inertiaPresentation Y).bilimit.lift (inertiaMapCone f)

/-- Naturality of the inertia projection. -/
noncomputable def inertiaMap_projection_naturality {X Y : FppfStack.{u}}
    (f : StackHom X Y) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (inertiaMap f) (inertiaProjection Y))
      (Pseudofunctor.StrongTrans.vcomp (inertiaProjection X) f) :=
  (inertiaPresentation Y).bilimit.lift_fst (inertiaMapCone f)

/-! ## Global compatibility of the inertia map -/

/-- The second projection of the inertia map, retained as an explicit global 2-isomorphism. -/
noncomputable def inertiaMap_secondProjection_naturality {X Y : FppfStack.{u}}
    (f : StackHom X Y) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (inertiaMap f)
        (inertiaPresentation Y).snd)
      (Pseudofunctor.StrongTrans.vcomp (inertiaPresentation X).snd f) :=
  (inertiaPresentation Y).bilimit.lift_snd (inertiaMapCone f)

/-- The actual inertia map satisfies the complete two-pullback comparison face.  This theorem
records the compatibility equation alongside both projection isomorphisms, so later uniqueness
arguments can use the global map without replacing the two-pullback by an equalizer. -/
theorem inertiaMap_cone_classifies {X Y : FppfStack.{u}} (f : StackHom X Y) :
    StackTwoPullback.ConeLiftClassifies (inertiaPresentation Y).toStackTwoPullback
      (inertiaMapCone f) (inertiaMap f)
      (inertiaMap_projection_naturality f)
      (inertiaMap_secondProjection_naturality f) :=
  (inertiaPresentation Y).bilimit.lift_compatible (inertiaMapCone f)

end GromovWitten.AlgebraicGeometry
