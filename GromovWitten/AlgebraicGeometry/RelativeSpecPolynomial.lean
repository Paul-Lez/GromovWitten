/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.RelativeSpecFunctoriality
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Polynomial extension of a quasi-coherent algebra

Polynomial extension commutes with restriction to affine opens. The resulting relative
spectrum is the affine-line extension of the original relative spectrum.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

noncomputable section

/-- Polynomial coefficient extension is a pushout of commutative rings. -/
theorem isPushout_polynomialMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    IsPushout (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))
      (CommRingCat.ofHom f) (CommRingCat.ofHom (Polynomial.mapRingHom f))
      (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) := by
  algebraize [f, Polynomial.mapRingHom f]
  exact (CommRingCat.isPushout_of_isPushout A B (Polynomial A) (Polynomial B)).flip

namespace AlgebraData

variable {X : Scheme.{u}} (𝒜 : AlgebraData X)

/-- Adjoin one polynomial variable on every affine open. -/
def polynomial : AlgebraData X where
  ring U := Polynomial (𝒜.ring U)
  map h := Polynomial.mapRingHom (𝒜.map h)
  map_id U := by
    apply RingHom.ext
    intro p
    change Polynomial.map (𝒜.map (le_refl U)) p = p
    rw [𝒜.map_id, Polynomial.map_id]
  map_comp h₁ h₂ := by
    apply RingHom.ext
    intro p
    change Polynomial.map (𝒜.map (h₁.trans h₂)) p =
      Polynomial.map (𝒜.map h₁) (Polynomial.map (𝒜.map h₂) p)
    rw [𝒜.map_comp, Polynomial.map_map]
  isPushout h := by
    exact (𝒜.isPushout h).paste_horiz (isPushout_polynomialMap (𝒜.map h))

/-- The coefficient inclusion gives the projection from the polynomial extension. -/
def polynomialInclusion : RelativeSpec.Hom X 𝒜.polynomial 𝒜 where
  app U := Polynomial.CAlgHom
  naturality h := by
    apply RingHom.ext
    intro a
    exact (Polynomial.map_C (𝒜.map h)).symm

/-- The projection of the polynomial extension to the original relative spectrum. -/
def polynomialProjection :
    RelativeSpec.relativeSpec X 𝒜.polynomial ⟶ RelativeSpec.relativeSpec X 𝒜 :=
  𝒜.polynomialInclusion.map

theorem polynomialProjection_affineι (U : X.affineOpens) :
    RelativeSpec.affineι X 𝒜.polynomial U ≫ 𝒜.polynomialProjection =
      Spec.map (CommRingCat.ofHom (Polynomial.C : 𝒜.ring U →+* _)) ≫
        RelativeSpec.affineι X 𝒜 U :=
  𝒜.polynomialInclusion.affineι_map U

/-- The affine-line extension has the expected cartesian square on every affine piece. -/
theorem isPullback_polynomialProjection (U : X.affineOpens) :
    IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.C : 𝒜.ring U →+* _)))
      (RelativeSpec.affineι X 𝒜.polynomial U) (RelativeSpec.affineι X 𝒜 U)
      𝒜.polynomialProjection :=
  𝒜.polynomialInclusion.isPullback_map U

end AlgebraData

namespace RelativeSpec.Hom

variable {X : Scheme.{u}} {𝒜 ℬ 𝒞 : AlgebraData X}

/-- Apply a compatible algebra map coefficientwise to polynomials. -/
def polynomial (φ : Hom X 𝒜 ℬ) : Hom X 𝒜.polynomial ℬ.polynomial where
  app U := Polynomial.mapAlgHom (φ.app U)
  naturality {U V} h := by
    apply RingHom.ext
    intro p
    change Polynomial (ℬ.ring V) at p
    change Polynomial.map (φ.app _).toRingHom (Polynomial.map (ℬ.map h) p) =
      Polynomial.map (𝒜.map h) (Polynomial.map (φ.app _).toRingHom p)
    rw [Polynomial.map_map, Polynomial.map_map, φ.naturality h]

@[simp]
theorem polynomial_app (φ : Hom X 𝒜 ℬ) (U : X.affineOpens) :
    φ.polynomial.app U = Polynomial.mapAlgHom (φ.app U) := rfl

@[simp]
theorem polynomial_id (𝒜 : AlgebraData X) : (id 𝒜).polynomial = id 𝒜.polynomial := by
  apply Hom.ext
  intro U
  apply AlgHom.ext
  intro p
  exact Polynomial.map_id

theorem polynomial_comp (φ : Hom X 𝒜 ℬ) (ψ : Hom X ℬ 𝒞) :
    (φ.comp ψ).polynomial = φ.polynomial.comp ψ.polynomial := by
  apply Hom.ext
  intro U
  apply AlgHom.ext
  intro p
  exact (Polynomial.map_map _ _ p).symm

/-- Polynomial projection is natural in the algebra data. -/
theorem polynomial_comp_inclusion (φ : Hom X 𝒜 ℬ) :
    φ.polynomial.comp ℬ.polynomialInclusion = 𝒜.polynomialInclusion.comp φ := by
  apply Hom.ext
  intro U
  apply AlgHom.ext
  intro a
  exact Polynomial.map_C (φ.app U).toRingHom

end RelativeSpec.Hom

end

end GromovWitten.AlgebraicGeometry
