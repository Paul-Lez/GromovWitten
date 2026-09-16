/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.InducedBicategory
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Groupoid-valued stacks

Mathlib's `Pseudofunctor.IsStack` deliberately allows arbitrary category-valued fibres.  An
algebraic stack instead starts with a pseudofunctor whose fibres are groupoids.  This file adds
that condition without defining a competing descent predicate, bundles it with Mathlib's stack
condition, and equips the resulting objects with the full induced bicategory of strong
transformations and modifications.

The Grothendieck construction of the underlying pseudofunctor is also exposed.  Its forgetful
functor is a fibre category in Mathlib's sense, and the theorem `fiberIsGroupoid` records that all
of those fibres are groupoids.  Thus the pseudofunctor and fibred-category views use the same
objects rather than parallel definitions.
-/

open CategoryTheory
open CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe v v' u u'

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C]

/-- A category-valued pseudofunctor is groupoid-valued when every one of its fibres is a
groupoid.  This is intentionally separate from Mathlib's `IsStack`, which carries only the
descent conditions. -/
class IsGroupoidValued (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) : Prop where
  fiber (X : C) : IsGroupoid (F.obj ⟨Opposite.op X⟩)

variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- The groupoid instance on a fibre of a groupoid-valued pseudofunctor. -/
noncomputable instance [F.IsGroupoidValued] (X : C) :
    IsGroupoid (F.obj ⟨Opposite.op X⟩) :=
  IsGroupoidValued.fiber X

/-- The Grothendieck construction of a groupoid-valued pseudofunctor has groupoid fibres.

Mathlib's preferred fibre categories for this construction are definitionally the values of the
pseudofunctor, so this is the precise link between the two presentations. -/
noncomputable instance fiberIsGroupoid [F.IsGroupoidValued] (X : C) :
    IsGroupoid (HasFibers.Fib (CoGrothendieck.forget F) X) := by
  dsimp only [HasFibers.Fib]
  infer_instance

end Pseudofunctor
end CategoryTheory

namespace GromovWitten.AlgebraicGeometry

set_option linter.checkUnivs false in
/-- A stack in groupoids on a Grothendieck site.

The two fields are kept separate so results about descent continue to use Mathlib's
`Pseudofunctor.IsStack`, while geometric results can request the groupoid-valued condition on its
own. -/
structure StackInGroupoids (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  /-- The underlying contravariant pseudofunctor. -/
  toPseudofunctor : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}
  /-- Every fibre is a groupoid. -/
  isGroupoidValued : toPseudofunctor.IsGroupoidValued
  /-- Objects and arrows satisfy effective descent. -/
  isStack : toPseudofunctor.IsStack J

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

instance (X : StackInGroupoids.{v, v', u, u'} C J) :
    X.toPseudofunctor.IsGroupoidValued :=
  X.isGroupoidValued

instance (X : StackInGroupoids.{v, v', u, u'} C J) :
    X.toPseudofunctor.IsStack J :=
  X.isStack

/-- The total category associated to a stack in groupoids. -/
abbrev total (X : StackInGroupoids.{v, v', u, u'} C J) :=
  Pseudofunctor.CoGrothendieck X.toPseudofunctor

/-- The projection of the total category of a stack to its base site. -/
abbrev projection (X : StackInGroupoids.{v, v', u, u'} C J) : X.total ⥤ C :=
  Pseudofunctor.CoGrothendieck.forget X.toPseudofunctor

/-- The projection associated to a stack in groupoids is a fibre category. -/
instance projectionIsFibered (X : StackInGroupoids.{v, v', u, u'} C J) :
    Functor.IsFibered X.projection := inferInstance

/-- Every preferred fibre of the Grothendieck construction of a stack in groupoids is a
groupoid. -/
noncomputable instance fiberIsGroupoid (X : StackInGroupoids.{v, v', u, u'} C J) (U : C) :
    IsGroupoid (HasFibers.Fib X.projection U) := by
  change IsGroupoid (X.toPseudofunctor.obj ⟨Opposite.op U⟩)
  infer_instance

end StackInGroupoids

set_option linter.checkUnivs false in
/-- The full bicategory of stacks in groupoids on `(C,J)`.  Its 1-morphisms are strong natural
transformations of pseudofunctors and its 2-morphisms are modifications. -/
abbrev StackBicategory (C : Type u) [Category.{v} C] (J : GrothendieckTopology C) :=
  InducedBicategory
    (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
    (fun X : StackInGroupoids.{v, v', u, u'} C J ↦ X.toPseudofunctor)

namespace StackBicategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Forget a stack in groupoids to its underlying pseudofunctor.  This is a strict
pseudofunctor, since the bicategory above is induced from the pseudofunctor bicategory. -/
abbrev forget :
    StrictPseudofunctor
      (StackBicategory.{v, v', u, u'} C J)
      (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) :=
  InducedBicategory.forget
    (C := LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
    (F := fun X : StackInGroupoids.{v, v', u, u'} C J ↦ X.toPseudofunctor)

end StackBicategory

end GromovWitten.AlgebraicGeometry
