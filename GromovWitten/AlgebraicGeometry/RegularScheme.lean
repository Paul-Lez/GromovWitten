/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular schemes

This file supplies the pointwise local-ring definition of a regular scheme and its basic
locality API.  Mathlib has regular local rings and regular commutative rings, but the pinned
version does not yet bundle the corresponding scheme property.
-/

open CategoryTheory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u v

noncomputable section

/-- A scheme is regular when all of its local rings are regular local rings. -/
def SchemeIsRegular (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

namespace SchemeIsRegular

/-- The spectrum of a regular ring is a regular scheme. -/
theorem spec (R : Type u) [CommRing R] [IsRegularRing R] :
    SchemeIsRegular (Spec (.of R)) := by
  intro x
  let p : PrimeSpectrum R := x
  let _ : p.asIdeal.IsPrime := p.isPrime
  let _ : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := inferInstance
  exact IsRegularLocalRing.of_ringEquiv
    (_root_.AlgebraicGeometry.Spec.stalkIso (.of R) p).commRingCatIsoToRingEquiv.symm

/-- Regularity is invariant under scheme isomorphism. -/
theorem of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (hX : SchemeIsRegular X) :
    SchemeIsRegular Y := by
  intro y
  let _ : IsRegularLocalRing (X.presheaf.stalk (e.inv y)) := hX (e.inv y)
  let _ : IsIso (e.inv.stalkMap y) := by infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv

/-- Regularity is symmetric across a scheme isomorphism. -/
theorem iso_iff {X Y : Scheme.{u}} (e : X ≅ Y) :
    SchemeIsRegular X ↔ SchemeIsRegular Y :=
  ⟨of_iso e, of_iso e.symm⟩

/-- Regularity can be checked on a scheme-theoretic open cover. -/
theorem of_openCover {X : Scheme.{u}} (U : Scheme.OpenCover.{v} X)
    (hU : ∀ i, SchemeIsRegular (U.X i)) : SchemeIsRegular X := by
  intro x
  obtain ⟨y, hy⟩ := U.covers x
  let _ : IsRegularLocalRing ((U.X (U.idx x)).presheaf.stalk y) := hU (U.idx x) y
  let _ : IsIso ((U.f (U.idx x)).stalkMap y) := by infer_instance
  rw [← hy]
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((U.f (U.idx x)).stalkMap y)).commRingCatIsoToRingEquiv.symm

/-- Regularity can be checked on an affine open cover. -/
theorem of_affineOpenCover {X : Scheme.{u}} (U : Scheme.AffineOpenCover.{v} X)
    (hU : ∀ i, SchemeIsRegular (U.openCover.X i)) : SchemeIsRegular X :=
  of_openCover U.openCover hU

end SchemeIsRegular

end

end GromovWitten.AlgebraicGeometry
