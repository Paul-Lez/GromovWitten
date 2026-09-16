/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Sites.PreservesLimits

/-!
# Representable morphisms of fppf sheaves

This file specializes Mathlib's functor-relative representability API to the Yoneda embedding of
schemes into fppf sheaves.  A morphism of fppf sheaves is representable when every pullback along
a scheme is represented by a scheme.  A representable morphism has a scheme-morphism property
`P` when the representing map to every test scheme has `P`.

Mathlib's definition retains a chosen representing object, both legs, and the pullback witness.
The aliases below therefore expose that existing API rather than creating a parallel notion.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

/-- Type-valued sheaves on the big fppf site of schemes. -/
abbrev FppfSheaf :=
  Sheaf (Scheme.fppfTopology : GrothendieckTopology Scheme.{u}) (Type u)

/-- The Yoneda embedding of schemes into fppf sheaves. -/
abbrev fppfYoneda : Scheme.{u} ⥤ FppfSheaf.{u} :=
  (Scheme.fppfTopology : GrothendieckTopology Scheme.{u}).yoneda

namespace FppfSheaf

/-- Representable morphisms of fppf sheaves, in Mathlib's functor-relative sense. -/
abbrev IsRepresentable : MorphismProperty FppfSheaf.{u} :=
  fppfYoneda.relativelyRepresentable

/-- The transfer of a scheme-morphism property to representable morphisms of fppf sheaves. -/
def HasRepresentableProperty (P : MorphismProperty Scheme.{u}) :
    MorphismProperty FppfSheaf.{u} :=
  P.relative fppfYoneda

theorem hasRepresentableProperty_rep {P : MorphismProperty Scheme.{u}}
    {X Y : FppfSheaf.{u}} {f : X ⟶ Y} (hf : HasRepresentableProperty P f) :
    IsRepresentable f := by
  exact (show P.relative fppfYoneda f from hf).rep

/-- A property stable under scheme base change holds representably on a Yoneda morphism exactly
when it holds on the original scheme morphism. -/
theorem yoneda_map_hasRepresentableProperty_iff
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} {f : X ⟶ Y} :
    HasRepresentableProperty P (fppfYoneda.map f) ↔ P f :=
  MorphismProperty.relative_map_iff

/-- In particular, every morphism of schemes becomes a representable morphism of fppf sheaves. -/
theorem yoneda_map_isRepresentable {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsRepresentable (fppfYoneda.map f) :=
  Functor.relativelyRepresentable.map fppfYoneda f

end FppfSheaf

end GromovWitten.AlgebraicGeometry
