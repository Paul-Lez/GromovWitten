/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CurveCohomologyDimension
import GromovWitten.AlgebraicGeometry.Curves.ModuleDerived
import GromovWitten.AlgebraicGeometry.SheafCohomology.LocalVanishing
import GromovWitten.AlgebraicGeometry.SheafCohomology.OpenRestriction
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Higher direct images from schemes of dimension at most one

The source-dimension bound is local on the target.  We apply the affine-open basis
criterion for a derived pushforward, restrict to the inverse image of each basis open,
and use the global dimension-one vanishing there.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X Y : Scheme.{u}}

/-- Higher direct images of an arbitrary abelian sheaf from a Noetherian scheme of
topological Krull dimension at most one vanish in degrees at least two. -/
theorem isZero_higherDirectImageAb_of_isNoetherian_topologicalKrullDim_le_one
    (f : X ⟶ Y) [IsNoetherian X] (hd : topologicalKrullDim X ≤ 1)
    (F : X.toTopCat.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    IsZero ((higherDirectImageAb f (n + 2)).obj F) := by
  have hzero : IsZero
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).rightDerived (n + 2)).obj F) := by
    refine isZero_rightDerived_pushforward_of_basis f.base F (n + 2)
      Y.isBasis_affineOpens ?_
    intro U hU
    let V : X.Opens := f ⁻¹ᵁ U
    let j : V.toScheme ⟶ X := V.ι
    let _ : NoetherianSpace (V : Type u) :=
      TopologicalSpace.NoetherianSpace.set (V : Set X)
    let _ : CompactSpace (V : Type u) := NoetherianSpace.compactSpace (V : Type u)
    let _ : IsNoetherian V.toScheme :=
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := inferInstance }
    have hdV : topologicalKrullDim V.toScheme ≤ 1 := by
      exact (topologicalKrullDim_subspace_le X (V : Set X)).trans hd
    have hlocal : IsZero (((sections (⊤ : Opens V.toScheme)).rightDerived
        (n + 2)).obj ((j.isOpenEmbedding.sheafPullback AddCommGrpCat).obj F)) :=
      isZero_rightDerived_sections_of_isNoetherian_topologicalKrullDim_le_one
        hdV ((j.isOpenEmbedding.sheafPullback AddCommGrpCat).obj F) n
    have himage : j.isOpenEmbedding.functor.obj (⊤ : Opens V.toScheme) =
        (Opens.map f.base).obj U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change f y.1 ∈ U
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, by trivial⟩
    have hopen := derivedSectionsOpenIso j.isOpenEmbedding F (n + 2)
    rw [himage] at hopen
    exact IsZero.of_iso hlocal hopen
  exact hzero

/-- The underlying abelian higher direct images of a module vanish above degree one
when the Noetherian source has dimension at most one. -/
theorem isZero_higherDirectImageModuleAb_of_isNoetherian_topologicalKrullDim_le_one
    (f : X ⟶ Y) [IsNoetherian X] (hd : topologicalKrullDim X ≤ 1)
    (M : X.Modules) (n : ℕ) :
    IsZero (higherDirectImageModuleAb f M (n + 2)) :=
  isZero_higherDirectImageAb_of_isNoetherian_topologicalKrullDim_le_one
    f hd ((moduleToSheafAb X).obj M) n

/-- Higher direct images of an arbitrary module from a Noetherian scheme of
topological Krull dimension at most one vanish in degrees at least two. -/
theorem isZero_higherDirectImageModule_of_isNoetherian_topologicalKrullDim_le_one
    (f : X ⟶ Y) [IsNoetherian X] (hd : topologicalKrullDim X ≤ 1)
    (M : X.Modules) (n : ℕ) :
    IsZero (higherDirectImageModule f M (n + 2)) := by
  apply module_isZero_of_underlying
  exact IsZero.of_iso
    (isZero_higherDirectImageModuleAb_of_isNoetherian_topologicalKrullDim_le_one
      f hd M n)
    (higherDirectImageModuleAbIso f M (n + 2))

end GromovWitten.AlgebraicGeometry.Curves
