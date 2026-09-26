/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorStackBundle

/-!
# Issue #128: `[U/G]` and `BG` inherit the `FppfStack` API

`Stacks/Algebraic.lean` moved `GromovWitten.AlgebraicGeometry.FppfStack` to fibres in
`Cat.{u + 1, u + 1}`, exactly the universe in which the quotient stack `[U/G]` and the
classifying stack `BG` already lived (`Stacks/TorsorStackBundle.lean`).  Consequently
`ActionTorsor.quotientStack`/`ActionTorsor.classifyingStack` are now literally `FppfStack.{u}`-
valued, so every declaration of `Stacks/Algebraic.lean` (`StackHom`, `StackChart`,
`HasRepresentableDiagonal`, `AlgebraicStack`, `DeligneMumfordStack`, ...) applies to them without
change.  This file records that the API elaborates for `[U/G]`/`BG`; it proves no new
mathematics.
-/

open GromovWitten.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.ActionTorsor

universe u

/-- The quotient stack `[U/G]` is an `FppfStack`. -/
noncomputable example (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) :
    FppfStack.{u} :=
  quotientStack G U

/-- The classifying stack `BG` is an `FppfStack`. -/
noncomputable example (G : AlgebraicSpaceGroup.{u}) : FppfStack.{u} :=
  classifyingStack G

/-- A `T`-point of the quotient stack `[U/G]`: a strong morphism from the represented stack of a
test scheme `T` into `[U/G]`. -/
abbrev QuotientStackPoint {G : AlgebraicSpaceGroup.{u}} (U : AlgebraicSpaceAction G)
    (T : Scheme.{u}) :=
  StackHom (representedStack T) (quotientStack G U)

/-- A `T`-point of the classifying stack `BG`. -/
abbrev ClassifyingStackPoint (G : AlgebraicSpaceGroup.{u}) (T : Scheme.{u}) :=
  StackHom (representedStack T) (classifyingStack G)

/-- Charts of the quotient stack `[U/G]`, in the sense of `Stacks/Algebraic.lean`. -/
abbrev QuotientStackChart {G : AlgebraicSpaceGroup.{u}} (U : AlgebraicSpaceAction G) :=
  StackChart (quotientStack G U)

/-- Charts of the classifying stack `BG`. -/
abbrev ClassifyingStackChart (G : AlgebraicSpaceGroup.{u}) :=
  StackChart (classifyingStack G)

/-- The diagonal-representability predicate of `Stacks/Algebraic.lean` applies to the quotient
stack `[U/G]`. -/
abbrev QuotientStackHasRepresentableDiagonal {G : AlgebraicSpaceGroup.{u}}
    (U : AlgebraicSpaceAction G) : Prop :=
  HasRepresentableDiagonal (quotientStack G U)
