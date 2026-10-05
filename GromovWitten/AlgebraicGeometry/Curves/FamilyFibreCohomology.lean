/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeDimension
import GromovWitten.AlgebraicGeometry.Curves.CurveCohomologyDimension
/-!
# Cohomological dimension of fibres of curve families

Every base change of a family of curves to a field has module cohomology
concentrated in degrees zero and one, including scheme-theoretic residue fibres.
-/

open CategoryTheory Limits AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S Y : Scheme.{u}}
/-- After base change to any field, cohomology of any module vanishes above degree one. -/
lemma familyFieldBaseChange_cohomology_isZero (f : X ⟶ S) [FamilyOfCurves f]
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ Spec (.of K)) (h : IsPullback p g f b)
    (M : Y.Modules) (n : ℕ) :
    IsZero (cohomologyModuleCat K g M (n + 2)) := by
  have : LocallyOfFiniteType g :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h inferInstance
  have : QuasiCompact g :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) h inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Y :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have hdim : topologicalKrullDim Y ≤ 1 :=
    (FamilyOfCurves.geometricRelativeDimensionLE f).2 b p g h
  have hz := isZero_cohomology_of_isNoetherian_topologicalKrullDim_le_one hdim M n
  have : Subsingleton (cohomologyModuleCat K g M (n + 2)) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  exact ModuleCat.isZero_of_subsingleton _

/-- Cohomology of any module on a fibre of a curve family vanishes above degree one. -/
lemma familyFibre_cohomology_isZero (f : X ⟶ S) [FamilyOfCurves f]
    (s : S) (M : (f.fiber s).Modules) (n : ℕ) :
    IsZero (cohomologyModuleCat (S.residueField s) (f.fiberToSpecResidueField s) M (n + 2)) :=
  familyFieldBaseChange_cohomology_isZero f (S.residueField s) (S.fromSpecResidueField s)
    (f.fiberι s) (f.fiberToSpecResidueField s) (IsPullback.of_hasPullback _ _) M n
end GromovWitten.AlgebraicGeometry.Curves
