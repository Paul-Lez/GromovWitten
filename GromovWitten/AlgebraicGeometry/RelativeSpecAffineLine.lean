/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.RelativeSpecPolynomial
import GromovWitten.AlgebraicGeometry.RelativeSpecCartesian
import GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

/-!
# The affine-line product of a relative spectrum

The spectrum of the polynomial extension of a quasi-coherent algebra is the product of its
relative spectrum with the affine line over the base scheme.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

open RelativeSpec VectorBundleTotalSpace

universe u

noncomputable section

namespace AlgebraData

variable {X : Scheme.{u}} (𝒜 : AlgebraData X)

/-- The structural algebra maps form a compatible family. -/
def toStructure : Hom X 𝒜 (structureData X) where
  app U := Algebra.ofId Γ(X, U.1) (𝒜.ring U)
  naturality h := by
    apply RingHom.ext
    intro r
    exact (map_algebraMap X 𝒜 h r).symm

/-- The structural family induces the existing projection to the base. -/
theorem toStructure_map : 𝒜.toStructure.map ≫ (baseIso X).hom = toBase X 𝒜 :=
  𝒜.toStructure.map_toBase

/-- The relative affine line, constructed by polynomial extension of the structure sheaf. -/
abbrev affineLine (X : Scheme.{u}) : Scheme.{u} := relativeSpec X (structureData X).polynomial

/-- Polynomial extension of an algebra is the fibre product with the relative affine line. -/
theorem isPullback_affineLine :
    IsPullback 𝒜.polynomialProjection 𝒜.toStructure.polynomial.map
      (toBase X 𝒜) (toBase X (structureData X).polynomial) := by
  have H : IsPullback 𝒜.polynomialProjection 𝒜.toStructure.polynomial.map
      𝒜.toStructure.map (structureData X).polynomialProjection := by
    apply RelativeSpec.isPullback_map
    intro U
    exact isPullback_SpecMap_of_isPushout _ _ _ _
      (isPushout_polynomialMap (algebraMap Γ(X, U.1) (𝒜.ring U))).flip
  refine H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (baseIso X) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simpa using 𝒜.toStructure_map
  · simpa [polynomialProjection] using (structureData X).polynomialInclusion.map_toBase

/-- The canonical product identification for the polynomial relative spectrum. -/
def polynomialIsoPullback : relativeSpec X 𝒜.polynomial ≅
    pullback (toBase X 𝒜) (toBase X (structureData X).polynomial) :=
  𝒜.isPullback_affineLine.isoPullback

end AlgebraData

end

end GromovWitten.AlgebraicGeometry
