/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.ProjectiveRank
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import GromovWitten.Algebra.ModuleCatScalarExtension

/-!
# Residue-field dimension and local rank

The dimension of scalar extension to a residue field agrees with the local rank
of a finite-projective module.
-/

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace GromovWitten.AlgebraicGeometry.FiniteProjectiveFibreRank
universe u
noncomputable section
variable {R : Type u} [CommRing R]

/-- Scalar extension to a residue field computes the local rank. -/
theorem finrank_extendScalars_eq_rankAtStalk
    (M : ModuleCat.{u} R) [Module.Finite R (M : Type u)]
    [Module.Projective R (M : Type u)] (p : PrimeSpectrum R) :
    Module.finrank p.asIdeal.ResidueField
      ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).obj M : Type u) =
      Module.rankAtStalk (R := R) (M : Type u) p := by
  rw [Module.rankAtStalk_eq]
  let e := ModuleCat.extendScalarsAlgebraIso (C := p.asIdeal.ResidueField) M
  exact e.toLinearEquiv.finrank_eq

end
end GromovWitten.AlgebraicGeometry.FiniteProjectiveFibreRank
