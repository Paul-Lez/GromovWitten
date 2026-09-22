/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Morphisms.ClosedImmersionDescent
import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent

/-!
# Descent for representable closed immersions of stacks

The stack-level statements use the actual scheme presentations supplied by
`StackMorphismPresentation`.  The scheme-level closed-immersion descent theorem therefore applies
to arbitrary genuine two-pullbacks, while the cover hypotheses remain properties of the test-scheme
map.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackHom

variable {X Y : FppfStack.{u}} {f : StackHom X Y}

open _root_.AlgebraicGeometry renaming IsClosedImmersion → SchIsClosedImmersion

/-! ## Descent along covers of the test schemes -/

/-- Representable closed immersions descend along fpqc covers of the test schemes. -/
theorem closedImmersion_of_fpqcCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsClosedImmersion FpqcCover.{u}) :
    f.ClosedImmersion :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable closed immersions descend along fppf covers of the test schemes. -/
theorem closedImmersion_of_fppfCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsClosedImmersion FppfCover.{u}) :
    f.ClosedImmersion :=
  hasRepresentableProperty_of_cover _ _ hrep h

/-- Representable closed immersions descend along smooth surjective covers of the test schemes. -/
theorem closedImmersion_of_smoothCover (hrep : f.IsRepresentable)
    (h : f.HasRepresentablePropertyOnCover @SchIsClosedImmersion SmoothCover.{u}) :
    f.ClosedImmersion :=
  hasRepresentableProperty_of_cover_of_le _ FppfCover.{u} _
    smoothCover_le_fppfCover hrep h

/-! ## Equivalences for raw presentations -/

/-- For a raw-representable morphism, checking closed immersion on an fpqc cover is equivalent to
checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_closedImmersion_iff_fpqcCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsClosedImmersion ↔
      f.HasRepresentablePropertyOnCover @SchIsClosedImmersion FpqcCover.{u} := by
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩

/-- For a raw-representable morphism, checking closed immersion on an fppf cover is equivalent to
checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_closedImmersion_iff_fppfCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsClosedImmersion ↔
      f.HasRepresentablePropertyOnCover @SchIsClosedImmersion FppfCover.{u} := by
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩

/-- For a raw-representable morphism, checking closed immersion on a smooth cover is equivalent to
checking it on every presentation. -/
theorem hasRepresentablePropertyRaw_closedImmersion_iff_smoothCover
    (hrep : f.HasRepresentablePropertyRaw ⊤) :
    f.HasRepresentablePropertyRaw @SchIsClosedImmersion ↔
      f.HasRepresentablePropertyOnCover @SchIsClosedImmersion SmoothCover.{u} := by
  let _ : MorphismProperty.DescendsAlong (@SchIsClosedImmersion :
      MorphismProperty Scheme.{u}) SmoothCover.{u} := inferInstance
  apply hasRepresentablePropertyRaw_iff_cover _ _ hrep
  intro T
  exact ⟨T, 𝟙 T, ⟨inferInstance, inferInstance⟩⟩

end StackHom

end GromovWitten.AlgebraicGeometry
