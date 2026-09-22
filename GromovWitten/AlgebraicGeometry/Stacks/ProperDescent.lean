/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Morphisms.ProperDescent
import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent

/-!
# Proper and separated descent for representable stack morphisms

The scheme-level fpqc and fppf descent instances are applied to the actual pullback square of
scheme presentations supplied by `StackMorphismPresentation`.  In particular, the statements
apply to arbitrary genuine two-pullbacks of stack morphisms.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackHom

variable {X Y : FppfStack.{u}} {f : StackHom X Y}

open _root_.AlgebraicGeometry renaming IsSeparated → SchIsSeparated, IsProper → SchIsProper

/-! ### Descent along covers of the test schemes -/

/-- Representable separatedness descends along fpqc covers of the test schemes. -/
theorem separated_of_fpqcCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsSeparated FpqcCover.{u}) : f.Separated :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable separatedness descends along fppf covers of the test schemes. -/
theorem separated_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsSeparated FppfCover.{u}) : f.Separated :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable separatedness descends along smooth surjective covers of the test schemes. -/
theorem separated_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsSeparated SmoothCover.{u}) : f.Separated :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _
    smoothCover_le_fppfCover hrep h

/-- Representable properness descends along fpqc covers of the test schemes. -/
theorem proper_of_fpqcCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsProper FpqcCover.{u}) : f.Proper :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable properness descends along fppf covers of the test schemes. -/
theorem proper_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsProper FppfCover.{u}) : f.Proper :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable properness descends along smooth surjective covers of the test schemes. -/
theorem proper_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsProper SmoothCover.{u}) : f.Proper :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _
    smoothCover_le_fppfCover hrep h

/-! ### Equivalences for raw presentations -/

/-- For a raw-representable morphism, checking separatedness on an fpqc cover is equivalent to
checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_separated_iff_fpqcCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsSeparated ↔
      f.HasRepresentablePropertyOnCover @SchIsSeparated FpqcCover.{u} := by
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩

/-- For a raw-representable morphism, checking separatedness on an fppf cover is equivalent to
checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_separated_iff_fppfCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsSeparated ↔
      f.HasRepresentablePropertyOnCover @SchIsSeparated FppfCover.{u} := by
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩

/-- For a raw-representable morphism, checking separatedness on a smooth surjective cover is
equivalent to checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_separated_iff_smoothCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsSeparated ↔
      f.HasRepresentablePropertyOnCover @SchIsSeparated SmoothCover.{u} := by
  let _ : MorphismProperty.DescendsAlong (@SchIsSeparated : MorphismProperty Scheme.{u})
      SmoothCover.{u} :=
    MorphismProperty.DescendsAlong.of_le smoothCover_le_fppfCover
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨inferInstance, inferInstance⟩⟩

/-- For a raw-representable morphism, checking properness on an fpqc cover is equivalent to
checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_proper_iff_fpqcCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsProper ↔
      f.HasRepresentablePropertyOnCover @SchIsProper FpqcCover.{u} := by
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩

/-- For a raw-representable morphism, checking properness on an fppf cover is equivalent to
checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_proper_iff_fppfCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsProper ↔
      f.HasRepresentablePropertyOnCover @SchIsProper FppfCover.{u} := by
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩

/-- For a raw-representable morphism, checking properness on a smooth surjective cover is
equivalent to checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_proper_iff_smoothCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsProper ↔
      f.HasRepresentablePropertyOnCover @SchIsProper SmoothCover.{u} := by
  let _ : MorphismProperty.DescendsAlong (@SchIsProper : MorphismProperty Scheme.{u})
      SmoothCover.{u} :=
    MorphismProperty.DescendsAlong.of_le smoothCover_le_fppfCover
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨inferInstance, inferInstance⟩⟩

end StackHom

end GromovWitten.AlgebraicGeometry
