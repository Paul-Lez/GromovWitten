/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Flat descent for separated and proper morphisms

The diagonal of a morphism of schemes is always an immersion.  Consequently, a diagonal is a
closed immersion exactly when it is universally closed: the forward implication is standard, and
the reverse implication follows by applying the closed-map condition to the image of the whole
source.  This identifies separatedness with the diagonal of universal closedness, so the generic
diagonal descent theorem gives fpqc and fppf descent for separated morphisms.  Properness then
follows from its separated, universally closed, and locally finite type presentation.
-/

public section

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Separatedness and the diagonal -/

/-- A morphism is separated exactly when its diagonal is universally closed. -/
lemma isSeparated_iff_universallyClosed_diagonal :
    IsSeparated f ↔ UniversallyClosed (pullback.diagonal f) := by
  constructor
  · intro hf
    let _ : IsSeparated f := hf
    infer_instance
  · intro hf
    let _ : UniversallyClosed (pullback.diagonal f) := hf
    let _ : IsImmersion (pullback.diagonal f) := inferInstance
    exact ⟨IsClosedImmersion.of_isPreimmersion _
      (by simpa only [Set.image_univ] using
        (pullback.diagonal f).isClosedMap _ isClosed_univ)⟩

/-- Separatedness is the diagonal of universal closedness. -/
lemma isSeparated_eq_diagonal_universallyClosed :
    @IsSeparated = MorphismProperty.diagonal
      (@UniversallyClosed : MorphismProperty Scheme.{u}) := by
  ext X Y f
  change IsSeparated f ↔ UniversallyClosed (pullback.diagonal f)
  exact isSeparated_iff_universallyClosed_diagonal f

/-! ### Descent instances -/

set_option backward.isDefEq.respectTransparency false in
/-- Separated morphisms satisfy fpqc descent. -/
instance separated_descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme.{u}) := by
  apply DescendsAlong.mk'
  introv hf hfst
  apply (isSeparated_iff_universallyClosed_diagonal g).2
  apply (MorphismProperty.diagonal_iff (P :=
    (@UniversallyClosed : MorphismProperty _))).mp
  apply MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := MorphismProperty.diagonal
      (@UniversallyClosed : MorphismProperty Scheme.{u}))
    (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact)) hf
  exact (isSeparated_iff_universallyClosed_diagonal _).1 hfst

set_option backward.isDefEq.respectTransparency false in
/-- Separated morphisms satisfy fppf descent. -/
instance separated_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation :
    DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
        MorphismProperty Scheme.{u}) := by
  apply DescendsAlong.mk'
  introv hf hfst
  apply (isSeparated_iff_universallyClosed_diagonal g).2
  apply (MorphismProperty.diagonal_iff (P :=
    (@UniversallyClosed : MorphismProperty _))).mp
  apply MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := MorphismProperty.diagonal
      (@UniversallyClosed : MorphismProperty Scheme.{u}))
    (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)) hf
  exact (isSeparated_iff_universallyClosed_diagonal _).1 hfst

set_option backward.isDefEq.respectTransparency false in
/-- Proper morphisms satisfy fpqc descent. -/
instance proper_descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong (@IsProper : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme.{u}) := by
  apply DescendsAlong.mk'
  introv hf hfst
  rw [isProper_eq] at hfst ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @IsSeparated) (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact)) hf hfst.1.1
  · exact MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @UniversallyClosed) (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact)) hf hfst.1.2
  · exact MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @LocallyOfFiniteType) (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact)) hf hfst.2

set_option backward.isDefEq.respectTransparency false in
/-- Proper morphisms satisfy fppf descent. -/
instance proper_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation :
    DescendsAlong (@IsProper : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
        MorphismProperty Scheme.{u}) := by
  apply DescendsAlong.mk'
  introv hf hfst
  rw [isProper_eq] at hfst ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @IsSeparated)
      (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)) hf hfst.1.1
  · exact MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @UniversallyClosed)
      (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)) hf hfst.1.2
  · exact MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @LocallyOfFiniteType)
      (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)) hf hfst.2

/-! ### Arbitrary pullback squares -/

/-- Separatedness can be checked on either leg of an arbitrary pullback square whose left leg is
fpqc. -/
theorem isSeparated_iff_of_isPullback_fpqcCover
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) :
      MorphismProperty Scheme.{u}) f) :
    IsSeparated fst ↔ IsSeparated g :=
  MorphismProperty.iff_of_isPullback sq hf

/-- Separatedness can be checked on either leg of an arbitrary pullback square whose left leg is
fppf. -/
theorem isSeparated_iff_of_isPullback_fppfCover
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
      MorphismProperty Scheme.{u}) f) :
    IsSeparated fst ↔ IsSeparated g :=
  MorphismProperty.iff_of_isPullback sq hf

/-- Separatedness can be checked on either leg of an arbitrary pullback square whose left leg is
smooth and surjective. -/
theorem isSeparated_iff_of_isPullback_smoothCover
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : ((@Surjective ⊓ @Smooth) : MorphismProperty Scheme.{u}) f) :
    IsSeparated fst ↔ IsSeparated g := by
  let _ : DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Smooth) : MorphismProperty Scheme.{u}) :=
    DescendsAlong.of_le (P := (@IsSeparated : MorphismProperty Scheme.{u}))
      (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)) (by
        rintro A B f ⟨hs, hsm⟩
        exact ⟨⟨hs, inferInstance⟩, inferInstance⟩)
  exact MorphismProperty.iff_of_isPullback sq hf

/-- Properness can be checked on either leg of an arbitrary pullback square whose left leg is
fpqc. -/
theorem isProper_iff_of_isPullback_fpqcCover
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) :
      MorphismProperty Scheme.{u}) f) :
    IsProper fst ↔ IsProper g :=
  MorphismProperty.iff_of_isPullback sq hf

/-- Properness can be checked on either leg of an arbitrary pullback square whose left leg is
fppf. -/
theorem isProper_iff_of_isPullback_fppfCover
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
      MorphismProperty Scheme.{u}) f) :
    IsProper fst ↔ IsProper g :=
  MorphismProperty.iff_of_isPullback sq hf

/-- Properness can be checked on either leg of an arbitrary pullback square whose left leg is
smooth and surjective. -/
theorem isProper_iff_of_isPullback_smoothCover
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : ((@Surjective ⊓ @Smooth) : MorphismProperty Scheme.{u}) f) :
    IsProper fst ↔ IsProper g := by
  let _ : DescendsAlong (@IsProper : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Smooth) : MorphismProperty Scheme.{u}) :=
    DescendsAlong.of_le (P := (@IsProper : MorphismProperty Scheme.{u}))
      (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)) (by
        rintro A B f ⟨hs, hsm⟩
        exact ⟨⟨hs, inferInstance⟩, inferInstance⟩)
  exact MorphismProperty.iff_of_isPullback sq hf

end AlgebraicGeometry
