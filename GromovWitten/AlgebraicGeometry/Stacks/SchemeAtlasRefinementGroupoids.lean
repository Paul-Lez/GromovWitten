/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.SchemeAtlasRefinementCoherence
import GromovWitten.AlgebraicGeometry.Stacks.AtlasRefinement

/-!
# Groupoid comparisons for a common scheme atlas

The common scheme atlas has fully faithful functors to the presentation
groupoids of both input atlases on every test-scheme fibre. The right
comparison uses the actual invertible modification of chart maps; the
resulting conjugation retains every arrow and every stabilizer.
-/

open CategoryTheory
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry.StackChart

universe u

variable {X : FppfStack.{u}} {A B : StackChart X}

/-- The first projection of a common scheme atlas induces a functor of
presentation groupoids, with the identity comparison 2-cell. -/
noncomputable def commonSchemeAtlasLeftFunctor
    (p : B.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    (T : Scheme.{u}) :
    PresentationGroupoid (commonSchemeAtlasChart p).map T ⥤
      PresentationGroupoid A.map T :=
  PresentationGroupoid.refinementFunctor (FppfStack.mapOfSchemeHom p.fst)
    (StackIso2.refl _) T

/-- The second projection uses the coherent overlap 2-cell. Its arrow map
retains every stabilizer, by conjugation with that comparison. -/
noncomputable def commonSchemeAtlasRightFunctor
    (p : B.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    (T : Scheme.{u}) :
    PresentationGroupoid (commonSchemeAtlasChart p).map T ⥤
      PresentationGroupoid B.map T :=
  PresentationGroupoid.refinementFunctor (FppfStack.mapOfSchemeHom p.snd)
    (commonSchemeAtlasComparisonIso p).symm T

/-- Both maps from the common scheme presentation are fully faithful on
every test-scheme fibre, so they preserve all arrows and stabilizers. -/
theorem commonSchemeAtlasFunctors_full_faithful
    (p : B.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme)))
    (T : Scheme.{u}) :
    (commonSchemeAtlasLeftFunctor p T).Full ∧
      (commonSchemeAtlasLeftFunctor p T).Faithful ∧
      (commonSchemeAtlasRightFunctor p T).Full ∧
      (commonSchemeAtlasRightFunctor p T).Faithful := by
  exact ⟨PresentationGroupoid.refinementFunctor_full _ _ _,
    PresentationGroupoid.refinementFunctor_faithful _ _ _,
    PresentationGroupoid.refinementFunctor_full _ _ _,
    PresentationGroupoid.refinementFunctor_faithful _ _ _⟩

/-- Smooth surjective scheme atlases admit a common scheme atlas with smooth
surjective projections and fully faithful comparison functors on every fibre.
The common atlas and its comparison 2-cell are constructed, not assumed. -/
theorem exists_commonSchemeAtlas_with_groupoidComparisons
    (A B : StackChart X) (hA : A.IsSmoothSurjective) (hB : B.IsSmoothSurjective) :
    ∃ (p : B.PullbackPresentation A.scheme (A.obj A.scheme (𝟙 A.scheme))),
      (commonSchemeAtlasChart p).IsSmoothSurjective ∧
      (@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective) p.fst ∧
      (@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.Surjective) p.snd ∧
      ∀ T : Scheme.{u},
        (commonSchemeAtlasLeftFunctor p T).Full ∧
        (commonSchemeAtlasLeftFunctor p T).Faithful ∧
        (commonSchemeAtlasRightFunctor p T).Full ∧
        (commonSchemeAtlasRightFunctor p T).Faithful := by
  obtain ⟨p, hp, hf, hs⟩ := exists_commonSchemeAtlas A B hA hB
  exact ⟨p, hp, hf, hs, commonSchemeAtlasFunctors_full_faithful p⟩

end GromovWitten.AlgebraicGeometry.StackChart
