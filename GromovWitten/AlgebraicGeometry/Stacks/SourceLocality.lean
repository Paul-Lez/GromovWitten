/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.PropertiesDescent

/-!
# Source-local properties of representable stack morphisms

The open covers in this file cover the representing scheme `p.space`.  They are therefore
different from the open covers of a test scheme used by `HasRepresentablePropertyOnOpenCover`.
For an actual presentation `p`, source locality is exactly the scheme theorem applied to
`p.map`.

The source-cover predicate below quantifies over actual presentations.  This makes the raw
statement independent of a silently selected presentation; the invariant statement is obtained
by the same explicit 2-isomorphism closure as `HasRepresentableProperty`.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackMorphismPresentation

variable {X Y : FppfStack.{u}} {f : StackHom X Y}

open _root_.AlgebraicGeometry

/-! ### A single presentation -/

/-- A source-local property can be checked after restricting a genuine presentation to every
member of an arbitrary open cover of its representing scheme. -/
theorem property_iff_of_sourceOpenCover (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] {T : Scheme.{u}} {y : StackFiber Y T}
    (p : StackMorphismPresentation f T y) (U : p.space.OpenCover.{u}) :
    P p.map ↔ ∀ i, P (U.f i ≫ p.map) :=
  IsZariskiLocalAtSource.iff_of_openCover U

end StackMorphismPresentation

namespace StackHom

variable {X Y : FppfStack.{u}} {f : StackHom X Y}

open _root_.AlgebraicGeometry

/-! ### Raw and invariant source-cover tests -/

/-- A scheme property is witnessed on a source open cover of an actual presentation of every
base change.  The cover is a cover of the presentation space, rather than of the test scheme. -/
def HasRepresentablePropertyRawOnSourceOpenCover (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (T : Scheme.{u}) (y : StackFiber Y T),
    ∃ (p : StackMorphismPresentation f T y) (U : p.space.OpenCover.{u}),
      ∀ i, P (U.f i ≫ p.map)

/-- The 2-isomorphism-invariant source-cover version of
`HasRepresentablePropertyRawOnSourceOpenCover`. -/
def HasRepresentablePropertyOnSourceOpenCover (P : MorphismProperty Scheme.{u}) : Prop :=
  ∃ g : StackHom X Y, Nonempty (StackIso2 f g) ∧
    g.HasRepresentablePropertyRawOnSourceOpenCover P

/-- The raw source-cover test is preserved by transporting every genuine presentation across an
invertible 2-cell. -/
theorem hasRepresentablePropertyRawOnSourceOpenCover_congr
    (P : MorphismProperty Scheme.{u}) {g : StackHom X Y} (e : StackIso2 f g) :
    f.HasRepresentablePropertyRawOnSourceOpenCover P ↔
      g.HasRepresentablePropertyRawOnSourceOpenCover P := by
  constructor
  · intro hf T y
    obtain ⟨p, U, hp⟩ := hf T y
    exact ⟨StackMorphismPresentation.transport e.symm p, U, hp⟩
  · intro hg T y
    obtain ⟨p, U, hp⟩ := hg T y
    exact ⟨StackMorphismPresentation.transport e p, U, hp⟩

/-- For every source-local scheme property, raw representability is equivalent to the existence
of a genuine presentation whose source open restrictions all have that property. -/
theorem hasRepresentablePropertyRaw_iff_sourceOpenCover
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P] :
    f.HasRepresentablePropertyRaw P ↔
      f.HasRepresentablePropertyRawOnSourceOpenCover P := by
  constructor
  · intro h T y
    obtain ⟨⟨p, hp⟩⟩ := h T y
    refine ⟨p, p.space.affineCover, ?_⟩
    intro i
    exact IsZariskiLocalAtSource.comp hp _
  · intro h T y
    obtain ⟨p, U, hp⟩ := h T y
    exact ⟨⟨p, (StackMorphismPresentation.property_iff_of_sourceOpenCover P p U).2 hp⟩⟩

/-- The source-cover test is independent of the chosen representative of a stack morphism. -/
theorem hasRepresentableProperty_iff_sourceOpenCover
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P] :
    f.HasRepresentableProperty P ↔ f.HasRepresentablePropertyOnSourceOpenCover P := by
  constructor
  · intro h
    obtain ⟨g, ⟨e⟩, hg⟩ := h
    exact ⟨g, ⟨e⟩, (hasRepresentablePropertyRaw_iff_sourceOpenCover P).1 hg⟩
  · intro h
    obtain ⟨g, ⟨e⟩, hg⟩ := h
    exact ⟨g, ⟨e⟩, (hasRepresentablePropertyRaw_iff_sourceOpenCover P).2 hg⟩

/-! ### Named source-local consequences -/

-- Specify the associated ring-hom property so instance search does not have to infer it.
local instance : IsZariskiLocalAtSource
    (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)

local instance : IsZariskiLocalAtSource
    (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)

local instance : IsZariskiLocalAtSource
    (@_root_.AlgebraicGeometry.FormallyUnramified : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FormallyUnramified)

local instance : IsZariskiLocalAtSource
    (@_root_.AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)

local instance : IsZariskiLocalAtSource
    (@_root_.AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FiniteType)

local instance : IsZariskiLocalAtSource
    (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)


theorem hasRepresentablePropertyRaw_smooth_iff_sourceOpenCover :
    f.HasRepresentablePropertyRaw @_root_.AlgebraicGeometry.Smooth ↔
      f.HasRepresentablePropertyRawOnSourceOpenCover @_root_.AlgebraicGeometry.Smooth :=
  hasRepresentablePropertyRaw_iff_sourceOpenCover _

theorem hasRepresentableProperty_smooth_iff_sourceOpenCover :
    f.Smooth ↔ f.HasRepresentablePropertyOnSourceOpenCover @_root_.AlgebraicGeometry.Smooth :=
  hasRepresentableProperty_iff_sourceOpenCover _

theorem hasRepresentablePropertyRaw_etale_iff_sourceOpenCover :
    f.HasRepresentablePropertyRaw @_root_.AlgebraicGeometry.Etale ↔
      f.HasRepresentablePropertyRawOnSourceOpenCover @_root_.AlgebraicGeometry.Etale :=
  hasRepresentablePropertyRaw_iff_sourceOpenCover _

theorem hasRepresentableProperty_etale_iff_sourceOpenCover :
    f.Etale ↔ f.HasRepresentablePropertyOnSourceOpenCover @_root_.AlgebraicGeometry.Etale :=
  hasRepresentableProperty_iff_sourceOpenCover _

theorem hasRepresentablePropertyRaw_formallyUnramified_iff_sourceOpenCover :
    f.HasRepresentablePropertyRaw @_root_.AlgebraicGeometry.FormallyUnramified ↔
      f.HasRepresentablePropertyRawOnSourceOpenCover
        @_root_.AlgebraicGeometry.FormallyUnramified :=
  hasRepresentablePropertyRaw_iff_sourceOpenCover _

theorem hasRepresentableProperty_formallyUnramified_iff_sourceOpenCover :
    f.HasRepresentableProperty @_root_.AlgebraicGeometry.FormallyUnramified ↔
      f.HasRepresentablePropertyOnSourceOpenCover
        @_root_.AlgebraicGeometry.FormallyUnramified :=
  hasRepresentableProperty_iff_sourceOpenCover _

theorem hasRepresentablePropertyRaw_flat_iff_sourceOpenCover :
    f.HasRepresentablePropertyRaw @_root_.AlgebraicGeometry.Flat ↔
      f.HasRepresentablePropertyRawOnSourceOpenCover @_root_.AlgebraicGeometry.Flat :=
  hasRepresentablePropertyRaw_iff_sourceOpenCover _

theorem hasRepresentableProperty_flat_iff_sourceOpenCover :
    f.Flat ↔ f.HasRepresentablePropertyOnSourceOpenCover @_root_.AlgebraicGeometry.Flat :=
  hasRepresentableProperty_iff_sourceOpenCover _

theorem hasRepresentablePropertyRaw_locallyOfFiniteType_iff_sourceOpenCover :
    f.HasRepresentablePropertyRaw @_root_.AlgebraicGeometry.LocallyOfFiniteType ↔
      f.HasRepresentablePropertyRawOnSourceOpenCover
        @_root_.AlgebraicGeometry.LocallyOfFiniteType :=
  hasRepresentablePropertyRaw_iff_sourceOpenCover _

theorem hasRepresentableProperty_locallyOfFiniteType_iff_sourceOpenCover :
    f.LocallyOfFiniteType ↔ f.HasRepresentablePropertyOnSourceOpenCover
      @_root_.AlgebraicGeometry.LocallyOfFiniteType :=
  hasRepresentableProperty_iff_sourceOpenCover _

theorem hasRepresentablePropertyRaw_locallyOfFinitePresentation_iff_sourceOpenCover :
    f.HasRepresentablePropertyRaw @_root_.AlgebraicGeometry.LocallyOfFinitePresentation ↔
      f.HasRepresentablePropertyRawOnSourceOpenCover
        @_root_.AlgebraicGeometry.LocallyOfFinitePresentation :=
  hasRepresentablePropertyRaw_iff_sourceOpenCover _

theorem hasRepresentableProperty_locallyOfFinitePresentation_iff_sourceOpenCover :
    f.LocallyOfFinitePresentation ↔ f.HasRepresentablePropertyOnSourceOpenCover
      @_root_.AlgebraicGeometry.LocallyOfFinitePresentation :=
  hasRepresentableProperty_iff_sourceOpenCover _

end StackHom

end GromovWitten.AlgebraicGeometry
