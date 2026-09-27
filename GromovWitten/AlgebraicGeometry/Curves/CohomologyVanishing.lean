/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineCoverVanishing
import GromovWitten.AlgebraicGeometry.SheafCohomology.SheafHComparison

/-!
# Vanishing of curve cohomology from affine covers

The finite-affine-cover theorem is proved first for actual derived sections.  The
Ext definition used by the curve API is then transported by the comparison with
right-derived global sections. -/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X : Scheme.{u}}

/-- A finite affine cover of a separated locally Noetherian scheme gives the
corresponding genuine `Sheaf.H` vanishing bound for every quasi-coherent module. -/
theorem isZero_cohomology_finiteAffineCover
    [IsLocallyNoetherian X] [X.IsSeparated] (Us : List X.Opens)
    (hUs : ∀ U ∈ Us, IsAffineOpen U) (hcover : affineUnion Us = ⊤)
    (hne : Us ≠ []) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (cohomology X M (n + Us.length + 1)) := by
  have hsections := isZero_rightDerived_sections_finiteAffineCover Us hUs hcover hne M (n + 1)
  have hsections' :
      IsZero (((sections (⊤ : Opens X)).rightDerived
        ((n + Us.length) + 1)).obj ((moduleToSheafAb X).obj M)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsections
  have hH := isZero_sheafH_of_isZero_rightDerivedSections
    (F := (moduleToSheafAb X).obj M) (n + Us.length) hsections'
  let Fg : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat :=
    (moduleToSheafAb X).obj M
  change IsZero (AddCommGrpCat.of (Fg.H (n + Us.length + 1)))
  exact hH

end GromovWitten.AlgebraicGeometry.Curves
