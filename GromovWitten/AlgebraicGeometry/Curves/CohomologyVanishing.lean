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
    IsZero (cohomology X M (n + Us.length)) := by
  have hlen : Us.length ≠ 0 := by
    intro hz
    apply hne
    exact List.eq_nil_of_length_eq_zero hz
  have htotal : n + Us.length ≠ 0 := by
    intro hz
    apply hlen
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero htotal
  have hsections := isZero_rightDerived_sections_finiteAffineCover Us hUs hcover hne M n
  have hsections' :
      IsZero (((sections (⊤ : Opens X)).rightDerived
        k.succ).obj ((moduleToSheafAb X).obj M)) := by
    simpa [hk] using hsections
  have hH := isZero_sheafH_of_isZero_rightDerivedSections
    (F := (moduleToSheafAb X).obj M) k hsections'
  let Fg : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat :=
    (moduleToSheafAb X).obj M
  change IsZero (AddCommGrpCat.of (Fg.H (n + Us.length)))
  rw [hk]
  exact hH

/-- The finite-cover theorem at the first positive degree above an arbitrary offset. -/
theorem isZero_cohomology_finiteAffineCover_succ
    [IsLocallyNoetherian X] [X.IsSeparated] (Us : List X.Opens)
    (hUs : ∀ U ∈ Us, IsAffineOpen U) (hcover : affineUnion Us = ⊤)
    (hne : Us ≠ []) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (cohomology X M (n + Us.length + 1)) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (isZero_cohomology_finiteAffineCover Us hUs hcover hne M (n + 1))

/-- An affine noetherian scheme has no positive coherent cohomology. -/
theorem isZero_cohomology_affine_succ {X : Scheme.{u}} [IsAffine X]
    [IsNoetherianRing (affineGlobalRing X)] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    IsZero (cohomology X M (n + 1)) := by
  have hp := SheafCohomology.isZero_affine_rightDerived_succ M n
  have hg := Functor.map_isZero PointSheaves.globalSections.{u} hp
  have hs := IsZero.of_iso hg (derivedSectionsTopIso X.toTopCat
    ((moduleToSheafAb X).obj M) (n + 1))
  exact isZero_sheafH_of_isZero_rightDerivedSections
    (F := (moduleToSheafAb X).obj M) n hs

/-- The affine vanishing theorem gives zero fibrewise cohomology dimension in
every positive degree. -/
theorem hDim_succ_eq_zero_of_affine (k : Type u) [Field k]
    {X : Scheme.{u}} [IsAffine X] [IsNoetherianRing (affineGlobalRing X)]
    (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) : hDim k f M (n + 1) = 0 := by
  have hz := isZero_cohomology_affine_succ M n
  let _ : Subsingleton (cohomologyModuleCat k f M (n + 1)) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  exact Module.finrank_zero_of_subsingleton

end GromovWitten.AlgebraicGeometry.Curves
