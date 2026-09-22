/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Morphisms.FlatDescent
import GromovWitten.AlgebraicGeometry.Morphisms.ProperDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.MorphismProperty.Descent

/-!
# Descent for closed immersions of schemes

Closed immersions are proper monomorphisms.  Properness descends along the faithfully flat covers
used here by `Morphisms/ProperDescent`; monomorphisms descend because their diagonals are
isomorphisms, using the generic diagonal theorem in `MorphismProperty/Limits`.  This gives the
closed-immersion descent statements without assuming quasi-compactness of an arbitrary immersion.
-/

public section

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe u

namespace AlgebraicGeometry

/-! ## Descent instances -/

set_option backward.isDefEq.respectTransparency false in
instance monomorphisms_descendsAlong_fpqc :
    DescendsAlong (MorphismProperty.monomorphisms Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [← diagonal_isomorphisms (C := Scheme.{u})]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance monomorphisms_descendsAlong_fppf :
    DescendsAlong (MorphismProperty.monomorphisms Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  rw [← diagonal_isomorphisms (C := Scheme.{u})]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance closedImmersion_descendsAlong_fpqc :
    DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [IsClosedImmersion.eq_proper_inf_monomorphisms]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance closedImmersion_descendsAlong_fppf :
    DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  rw [IsClosedImmersion.eq_proper_inf_monomorphisms]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance closedImmersion_descendsAlong_smooth :
    DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Smooth) := by
  apply DescendsAlong.of_le (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
  rintro X Y f ⟨hs, hsm⟩
  let _ : Smooth f := hsm
  exact ⟨⟨hs, inferInstance⟩, inferInstance⟩

/-! ## Arbitrary pullback squares -/

theorem isClosedImmersion_iff_of_isPullback_fpqcCover
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) :
      MorphismProperty Scheme.{u}) f) :
    IsClosedImmersion fst ↔ IsClosedImmersion g :=
  MorphismProperty.iff_of_isPullback sq hf

theorem isClosedImmersion_iff_of_isPullback_fppfCover
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
      MorphismProperty Scheme.{u}) f) :
    IsClosedImmersion fst ↔ IsClosedImmersion g :=
  MorphismProperty.iff_of_isPullback sq hf

theorem isClosedImmersion_iff_of_isPullback_smoothCover
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : ((@Surjective ⊓ @Smooth) : MorphismProperty Scheme.{u}) f) :
    IsClosedImmersion fst ↔ IsClosedImmersion g := by
  let _ : DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Smooth) := closedImmersion_descendsAlong_smooth
  exact MorphismProperty.iff_of_isPullback sq hf

end AlgebraicGeometry
