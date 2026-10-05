/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineBaseFibreCohomology
import GromovWitten.AlgebraicGeometry.Curves.FamilyFibreCohomology

/-!
# Vanishing of affine-base fibre cohomology

The residue-field base change of a curve family has cohomology only in degrees
zero and one. This uses the algebraic residue field of a prime ideal, matching
scalar extension of a complex over the affine base ring.
-/

open CategoryTheory Limits AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- Actual cohomology of the algebraic residue-field fibre vanishes above degree one. -/
lemma affineBaseFibreCohomology_isZero
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) (q : PrimeSpectrum R) (n : ℕ) :
    IsZero (affineBaseFibreCohomology s M q (n + 2)) :=
  familyFieldBaseChange_cohomology_isZero s q.asIdeal.ResidueField
    (Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField)))
    _ _ (IsPullback.of_hasPullback _ _) _ n

end GromovWitten.AlgebraicGeometry.Curves
