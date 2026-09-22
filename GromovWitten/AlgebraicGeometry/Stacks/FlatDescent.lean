/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Morphisms.FlatDescent
import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent

/-!
# Flat descent for representable stack morphisms

The scheme-level fpqc theorem is applied to the actual pullback square of
scheme presentations supplied by `StackMorphismPresentation`.  Thus these
results apply to arbitrary genuine two-pullbacks and do not require choosing a
particular presentation.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackHom

variable {X Y : FppfStack.{u}} {f : StackHom X Y}

open _root_.AlgebraicGeometry renaming Flat → SchFlat

/-! ### Descent along covers of the test schemes -/

/-- Representable flatness descends along fpqc covers of the test schemes. -/
theorem flat_of_fpqcCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchFlat FpqcCover.{u}) : f.Flat :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable flatness descends along fppf covers of the test schemes. -/
theorem flat_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchFlat FppfCover.{u}) : f.Flat :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable flatness descends along smooth surjective covers of the test schemes. -/
theorem flat_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchFlat SmoothCover.{u}) : f.Flat :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _ smoothCover_le_fppfCover hrep h

/-- For a raw-representable morphism, checking flatness on an fpqc cover is
equivalent to checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_flat_iff_fpqcCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchFlat ↔
      f.HasRepresentablePropertyOnCover @SchFlat FpqcCover.{u} := by
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩

end StackHom

end GromovWitten.AlgebraicGeometry
