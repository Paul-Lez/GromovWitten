/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleFlasque
import GromovWitten.AlgebraicGeometry.SheafCohomology.Flasque
import GromovWitten.AlgebraicGeometry.SheafCohomology.DiscreteSpace
import GromovWitten.AlgebraicGeometry.SheafCohomology.OpenRestriction
import GromovWitten.AlgebraicGeometry.Curves.CohomologyVanishing
import Mathlib.AlgebraicGeometry.Artinian
import GromovWitten.AlgebraicGeometry.Curves.GenericPointSheaf
import GromovWitten.AlgebraicGeometry.SheafCohomology.GenericSupport
import GromovWitten.AlgebraicGeometry.SheafCohomology.FlasqueCohomology

/-!
# Cohomological dimension of Noetherian schemes of dimension at most one

In dimension zero the underlying space is discrete and every sheaf is flasque.
In dimension one, restriction to the generic-point scheme has flasque target,
kernel and cokernel. The long exact cohomology sequence therefore gives
vanishing in degrees at least two for arbitrary abelian and module sheaves.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

/-! ### The zero-dimensional noetherian case -/

variable {X : Scheme.{u}}

/-- A noetherian zero-dimensional scheme has a finite discrete underlying
topological space. -/
theorem finite_of_isNoetherian_topologicalKrullDim_zero
    [IsNoetherian X] (hX : topologicalKrullDim X ≤ 0) : Finite X := by
  have : IsLocallyArtinian X :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero hX
  have : DiscreteTopology X := inferInstance
  exact finite_of_compact_of_discrete

/-- A locally noetherian scheme of topological Krull dimension zero is discrete,
and hence the underlying abelian sheaf of every module is flasque. -/
theorem isFlasque_moduleToSheafAb_of_isLocallyNoetherian_topologicalKrullDim_zero
    [IsLocallyNoetherian X] (hX : topologicalKrullDim X ≤ 0)
    (M : X.Modules) :
    TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj M) := by
  have : IsLocallyArtinian X :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero hX
  have : DiscreteTopology X := inferInstance
  exact isFlasque_of_discreteTopology ((moduleToSheafAb X).obj M)

/-- Positive derived global sections vanish for every module on a locally
noetherian zero-dimensional scheme. -/
theorem isZero_rightDerived_sections_of_isLocallyNoetherian_topologicalKrullDim_zero
    [IsLocallyNoetherian X] (hX : topologicalKrullDim X ≤ 0)
    (M : X.Modules) (n : ℕ) :
    IsZero (((sections (⊤ : Opens X)).rightDerived (n + 1)).obj
      ((moduleToSheafAb X).obj M)) := by
  have : IsLocallyArtinian X :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero hX
  have : DiscreteTopology X := inferInstance
  have : TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj M) :=
    isFlasque_of_discreteTopology ((moduleToSheafAb X).obj M)
  have hz := TopCat.Sheaf.isZero_rightDerived_pushforward_of_isFlasque
    (toPoint X.toTopCat) ((moduleToSheafAb X).obj M) n
  have hg := Functor.map_isZero PointSheaves.globalSections.{u} hz
  exact IsZero.of_iso hg (derivedSectionsTopIso X.toTopCat
    ((moduleToSheafAb X).obj M) (n + 1))

/-- The corresponding positive-degree `Sheaf.H` vanishing statement. -/
theorem isZero_cohomology_of_isLocallyNoetherian_topologicalKrullDim_zero
    [IsLocallyNoetherian X] (hX : topologicalKrullDim X ≤ 0)
    (M : X.Modules) (n : ℕ) :
    IsZero (cohomology X M (n + 1)) := by
  exact isZero_sheafH_of_isZero_rightDerivedSections (F := (moduleToSheafAb X).obj M)
    n (isZero_rightDerived_sections_of_isLocallyNoetherian_topologicalKrullDim_zero hX M n)


/-! ### The dimension-one bound -/

/-- Every abelian sheaf on a Noetherian scheme of dimension at most one has
vanishing cohomology in degrees at least two. -/
theorem isZero_sheafH_of_isNoetherian_topologicalKrullDim_le_one
    [IsNoetherian X] (hd : topologicalKrullDim X ≤ 1)
    (F : Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) (n : ℕ) :
    IsZero (AddCommGrpCat.of (F.H (n + 2))) := by
  let φ := genericPointSheafMap X F
  have hK : TopCat.Sheaf.IsFlasque (kernel φ) :=
    isFlasque_of_zero_generic_stalks hd (kernel φ)
      (genericPointSheafMap_kernel_stalk_isZero F)
  have hC : TopCat.Sheaf.IsFlasque (cokernel φ) :=
    isFlasque_of_zero_generic_stalks hd (cokernel φ)
      (genericPointSheafMap_cokernel_stalk_isZero F)
  have hG := isFlasque_genericPointCoproduct_pushforward X
    ((presheafToSheaf (Opens.grothendieckTopology
      (genericPointCoproduct X).toTopCat) AddCommGrpCat).obj
        ((TopCat.Presheaf.pullback AddCommGrpCat
          (genericPointsToScheme X).base).obj F.1))
  exact isZero_sheafH_of_flasque_kernel_cokernel (X := X.toTopCat) φ n

/-- Derived global sections vanish in degrees at least two for every abelian
sheaf on a Noetherian scheme of dimension at most one. -/
theorem isZero_rightDerived_sections_of_isNoetherian_topologicalKrullDim_le_one
    [IsNoetherian X] (hd : topologicalKrullDim X ≤ 1)
    (F : X.toTopCat.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    IsZero (((sections (⊤ : Opens X)).rightDerived (n + 2)).obj F) := by
  exact isZero_rightDerivedSections_of_isZero_sheafH (n + 1)
    (isZero_sheafH_of_isNoetherian_topologicalKrullDim_le_one hd F n)

/-- Cohomology of an arbitrary module sheaf on a Noetherian scheme of dimension
at most one vanishes in degrees at least two. -/
theorem isZero_cohomology_of_isNoetherian_topologicalKrullDim_le_one
    [IsNoetherian X] (hd : topologicalKrullDim X ≤ 1) (M : X.Modules) (n : ℕ) :
    IsZero (cohomology X M (n + 2)) :=
  isZero_sheafH_of_isNoetherian_topologicalKrullDim_le_one hd ((moduleToSheafAb X).obj M) n

end GromovWitten.AlgebraicGeometry.Curves
