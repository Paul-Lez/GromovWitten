/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Flat descent for morphisms of schemes

Flatness of ring maps reflects faithfully flat tensor base change.  The affine
criterion in `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent` then upgrades
this to fpqc descent for flat morphisms of schemes.
-/

public section

open CategoryTheory Limits MorphismProperty

universe u

namespace RingHom

/-- Flatness descends along faithfully flat ring maps. -/
lemma Flat.codescendsAlong_faithfullyFlat :
    CodescendsAlong Flat FaithfullyFlat := by
  refine .mk _ Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [flat_algebraMap_iff] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_flat_tensorProduct R T S

end RingHom

namespace AlgebraicGeometry

/-- Flatness is local on the target in the affine-local ring hom presentation. -/
instance Flat.isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (@Flat) (Q := RingHom.Flat)

/-- Surjective flat morphisms are stable under base change. -/
instance surjective_inf_flat_isStableUnderBaseChange :
    IsStableUnderBaseChange ((@Surjective ⊓ @Flat) : MorphismProperty Scheme.{u}) := by
  exact IsStableUnderBaseChange.inf

/-- The conjunction defining an fppf cover is stable under base change. -/
instance fppfCover_isStableUnderBaseChange :
    IsStableUnderBaseChange
      ((@Surjective ⊓ @Flat) ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := by
  exact IsStableUnderBaseChange.inf

/-- Flat morphisms descend along fpqc covers. -/
instance Flat.descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @Flat (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Flat.codescendsAlong_faithfullyFlat

/- The generic fpqc-to-fppf theorem in Mathlib is available once the cover's
   conjunction is exposed as a base-change-stable morphism property. -/
instance Flat.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation :
    DescendsAlong @Flat (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  apply _root_.AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong
  rintro R X Y f g ⟨⟨h₁, h₂⟩, h₃⟩ H
  obtain ⟨V : X.Opens, hV, e⟩ := f.isOpenMap.exists_opens_image_eq_of_prespectralSpace
    f.continuous (by simp) isOpen_univ isCompact_univ
  refine MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (.paste_vert (.of_hasPullback V.ι _) (.of_hasPullback f g)) ⟨⟨?_, inferInstance⟩,
      (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp hV)⟩ ?_
  · exact ⟨fun x ↦ have ⟨y, hyV, e⟩ := e.ge (Set.mem_univ x); ⟨⟨y, hyV⟩, e⟩⟩
  · exact _root_.AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback
      (.flip <| .of_hasPullback _ _) H

/-- Flatness is equivalent before and after an fpqc base change. -/
lemma Flat.pullback_fst_iff_fpqc {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Surjective f] [Flat f] [QuasiCompact f] :
    Flat (pullback.fst f g) ↔ Flat g := by
  apply MorphismProperty.pullback_fst_iff
    (P := @Flat) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f) (g := g)
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end AlgebraicGeometry
