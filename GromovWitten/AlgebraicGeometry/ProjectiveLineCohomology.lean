/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineHigherVanishing
import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import GromovWitten.AlgebraicGeometry.ProjectiveLineCharts
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineCoverVanishing
import GromovWitten.AlgebraicGeometry.SheafCohomology.SheafHComparison

/-!
# Higher direct-image vanishing for the projective line

The two standard affine charts and their affine overlap give a relative vanishing theorem for
quasi-coherent modules on the projective line over a Noetherian base ring.
-/

open CategoryTheory Limits TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.ProjectiveLine

/-- Higher direct images along the structure morphism of the projective line vanish in degrees
at least two for every quasi-coherent module over a Noetherian base ring. -/
theorem isZero_higherDirectImageModule_structureMap
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : (scheme R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (higherDirectImageModule (structureMap R) M (n + 2)) := by
  let U : (scheme R).Opens := (chartZero R).opensRange
  let V : (scheme R).Opens := (chartOne R).opensRange
  let _ : IsAffine U.toScheme := isAffineOpen_opensRange_chartZero R
  let _ : IsAffine V.toScheme := isAffineOpen_opensRange_chartOne R
  have hI : IsAffineOpen (U ⊓ V) := by
    dsimp [U, V]
    rw [opensRange_chartZero_inf_chartOne R]
    exact isAffineOpen_opensRange _
  let _ : IsAffine (U ⊓ V).toScheme := hI
  let _ : IsAffineHom (U.ι ≫ structureMap R) := inferInstance
  let _ : IsAffineHom (V.ι ≫ structureMap R) := inferInstance
  let _ : IsAffineHom ((U ⊓ V).ι ≫ structureMap R) := inferInstance
  exact isZero_higherDirectImageModule_twoAffineCover (structureMap R) U V
    (opensRange_chartZero_sup_chartOne R) M n

/-- Higher cohomology of every quasicoherent module on the projective line vanishes over a
Noetherian base ring.  No finite-presentation hypothesis on the module is needed here. -/
theorem isZero_cohomology_succ_succ
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : (scheme R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (cohomology (scheme R) M (n + 2)) := by
  let U : (scheme R).Opens := (chartZero R).opensRange
  let V : (scheme R).Opens := (chartOne R).opensRange
  have hU : IsAffineOpen U := by
    dsimp [U]
    exact isAffineOpen_opensRange_chartZero R
  have hV : IsAffineOpen V := by
    dsimp [V]
    exact isAffineOpen_opensRange_chartOne R
  have hI : IsAffineOpen (U ⊓ V) := by
    dsimp [U, V]
    rw [opensRange_chartZero_inf_chartOne R]
    exact isAffineOpen_opensRange _
  have hz := isZero_rightDerived_sections_sup ((moduleToSheafAb (scheme R)).obj M)
    U V (n + 1)
    (isZero_rightDerived_sections_affineOpen_succ U hU M (n + 1))
    (isZero_rightDerived_sections_affineOpen_succ V hV M (n + 1))
    (isZero_rightDerived_sections_affineOpen_succ (U ⊓ V) hI M n)
  dsimp [U, V] at hz
  rw [opensRange_chartZero_sup_chartOne R] at hz
  exact isZero_sheafH_of_isZero_rightDerivedSections
    (F := (moduleToSheafAb (scheme R)).obj M) (n + 1) hz

/-- The degree-at-least-two cohomology modules of a quasicoherent module on the projective line
are finite over the Noetherian base ring because they vanish. -/
theorem finite_cohomology_succ_succ
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : (scheme R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    Module.Finite R (cohomologyModuleCat R (structureMap R) M (n + 2)) := by
  have hz := isZero_cohomology_succ_succ R M n
  let _ : Subsingleton (cohomologyModuleCat R (structureMap R) M (n + 2)) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  infer_instance

end GromovWitten.AlgebraicGeometry.ProjectiveLine
