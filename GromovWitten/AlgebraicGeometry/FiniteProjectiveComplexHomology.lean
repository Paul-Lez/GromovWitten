/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.FiniteProjectiveHomologyLocus
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
/-!
# Fibre homology semicontinuity for complexes

In a fixed degree, homology after residue-field scalar extension is upper semicontinuous
when the three terms that compute it are finite projective. No boundedness condition on
the rest of the complex is needed. The proof uses the actual homology object of the
scalar-extended complex and the finite-projective short-complex theorem.
-/

open CategoryTheory
open GromovWitten.AlgebraicGeometry.FiniteFreeHomologyLocus
open GromovWitten.AlgebraicGeometry.FiniteProjectiveHomologyLocus
universe u v
noncomputable section
namespace GromovWitten.AlgebraicGeometry
variable {R : Type u} [CommRing R] {ι : Type v} {c : ComplexShape ι}
set_option backward.isDefEq.respectTransparency false in
/-- Fibre homology dimension is upper semicontinuous in each finite-projective degree. -/
theorem upperSemicontinuous_fibreHomologyFinrank_complex
    (K : HomologicalComplex (ModuleCat.{u} R) c) (i : ι)
    [Module.Finite R (K.X (c.prev i) : Type u)]
    [Module.Projective R (K.X (c.prev i) : Type u)]
    [Module.Finite R (K.X i : Type u)] [Module.Projective R (K.X i : Type u)]
    [Module.Finite R (K.X (c.next i) : Type u)]
    [Module.Projective R (K.X (c.next i) : Type u)] :
    UpperSemicontinuous (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          c).obj K).homology i : Type u)) := by
  change UpperSemicontinuous (fibreHomologyFinrank (S := K.sc i))
  exact @upperSemicontinuous_fibreHomologyFinrank_of_finite_projective R _ (K.sc i)
    (inferInstanceAs (Module.Finite R (K.X (c.prev i) : Type u)))
    (inferInstanceAs (Module.Projective R (K.X (c.prev i) : Type u)))
    (inferInstanceAs (Module.Finite R (K.X i : Type u)))
    (inferInstanceAs (Module.Projective R (K.X i : Type u)))
    (inferInstanceAs (Module.Finite R (K.X (c.next i) : Type u)))
    (inferInstanceAs (Module.Projective R (K.X (c.next i) : Type u)))
end GromovWitten.AlgebraicGeometry
