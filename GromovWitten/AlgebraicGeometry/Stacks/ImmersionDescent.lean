/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Morphisms.ImmersionDescent
import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent

/-!
# Descent for representable immersions of stacks

The stack-level statements use actual scheme presentations and the scheme-level fppf descent
theorem, so they apply to arbitrary genuine two-pullbacks.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackHom

variable {X Y : FppfStack.{u}} {f : StackHom X Y}

open _root_.AlgebraicGeometry renaming IsImmersion → SchIsImmersion

/-- Representable immersions descend along fppf covers of the test schemes. -/
theorem immersion_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsImmersion FppfCover.{u}) : f.Immersion :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable immersions descend along smooth surjective covers of the test schemes. -/
theorem immersion_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsImmersion SmoothCover.{u}) : f.Immersion :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _
    smoothCover_le_fppfCover hrep h

/-- For a raw-representable morphism, checking immersion on an fppf cover is equivalent to
checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_immersion_iff_fppfCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsImmersion ↔
      f.HasRepresentablePropertyOnCover @SchIsImmersion FppfCover.{u} := by
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩

/-- For a raw-representable morphism, checking immersion on a smooth cover is equivalent to
checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_immersion_iff_smoothCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsImmersion ↔
      f.HasRepresentablePropertyOnCover @SchIsImmersion SmoothCover.{u} := by
  let _ : MorphismProperty.DescendsAlong (@SchIsImmersion :
      MorphismProperty Scheme.{u}) SmoothCover.{u} := inferInstance
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨inferInstance, inferInstance⟩⟩

end StackHom

end GromovWitten.AlgebraicGeometry
