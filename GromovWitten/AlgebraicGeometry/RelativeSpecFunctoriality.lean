/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.RelativeSpec

/-!
# Functoriality of relative spectra

Compatible algebra maps induce maps of the glued relative spectra.  The identity and
composition laws below allow affine identities, such as cone contraction laws, to be
transported to the global scheme without supplying global compatibility as extra data.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.RelativeSpec

universe u

noncomputable section

variable {X : Scheme.{u}} {𝒜 ℬ 𝒞 : AlgebraData X}

/-- Maps out of a relative spectrum agree if they agree on every affine piece. -/
theorem hom_ext {Y : Scheme.{u}} {f g : relativeSpec X 𝒜 ⟶ Y}
    (h : ∀ U, affineι X 𝒜 U ≫ f = affineι X 𝒜 U ≫ g) : f = g :=
  colimit.hom_ext h

namespace Hom

/-- Compatible algebra maps are determined by their affine components. -/
@[ext]
theorem ext {φ ψ : Hom X 𝒜 ℬ} (h : ∀ U, φ.app U = ψ.app U) : φ = ψ := by
  cases φ
  cases ψ
  congr
  funext U
  exact h U

/-- The identity compatible algebra map. -/
def id (𝒜 : AlgebraData X) : Hom X 𝒜 𝒜 where
  app U := AlgHom.id _ _
  naturality _ := by ext; rfl

/-- Composition in the direction of the induced maps of relative spectra. -/
def comp (φ : Hom X 𝒜 ℬ) (ψ : Hom X ℬ 𝒞) : Hom X 𝒜 𝒞 where
  app U := (φ.app U).comp (ψ.app U)
  naturality h := by
    ext a
    change φ.app _ (ψ.app _ (𝒞.map h a)) = 𝒜.map h (φ.app _ (ψ.app _ a))
    have hψ := RingHom.congr_fun (ψ.naturality h) a
    have hφ := RingHom.congr_fun (φ.naturality h) (ψ.app _ a)
    exact (congrArg (φ.app _) hψ).trans hφ

@[simp]
theorem id_app (𝒜 : AlgebraData X) (U : X.affineOpens) :
    (id 𝒜).app U = AlgHom.id _ _ := rfl

@[simp]
theorem comp_app (φ : Hom X 𝒜 ℬ) (ψ : Hom X ℬ 𝒞) (U : X.affineOpens) :
    (φ.comp ψ).app U = (φ.app U).comp (ψ.app U) := rfl

@[simp]
theorem id_comp (φ : Hom X 𝒜 ℬ) : (id 𝒜).comp φ = φ := by ext; rfl

@[simp]
theorem comp_id (φ : Hom X 𝒜 ℬ) : φ.comp (id ℬ) = φ := by ext; rfl

theorem comp_assoc {𝒟 : AlgebraData X} (φ : Hom X 𝒜 ℬ) (ψ : Hom X ℬ 𝒞)
    (χ : Hom X 𝒞 𝒟) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by ext; rfl

/-- The identity family induces the identity of the glued scheme. -/
@[simp]
theorem map_id (𝒜 : AlgebraData X) : (id 𝒜).map = 𝟙 (relativeSpec X 𝒜) := by
  apply RelativeSpec.hom_ext
  intro U
  rw [affineι_map]
  simp [id, CommRingCat.ofHom_id, Spec.map_id]

/-- Relative `Spec` carries compatible algebra composition to scheme composition. -/
@[simp]
theorem map_comp (φ : Hom X 𝒜 ℬ) (ψ : Hom X ℬ 𝒞) :
    (φ.comp ψ).map = φ.map ≫ ψ.map := by
  apply RelativeSpec.hom_ext
  intro U
  rw [affineι_map, ← Category.assoc, affineι_map, Category.assoc, affineι_map]
  change Spec.map (CommRingCat.ofHom ((φ.app U).toRingHom.comp (ψ.app U).toRingHom)) ≫ _ = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- A compatible algebra map is determined by its induced morphism of relative spectra. -/
theorem map_injective : Function.Injective (map : Hom X 𝒜 ℬ → _) := by
  intro φ ψ h
  apply Hom.ext
  intro U
  have hc := congrArg (fun f ↦ affineι X 𝒜 U ≫ f) h
  rw [affineι_map, affineι_map, cancel_mono] at hc
  have hr := Spec.map_injective hc
  apply AlgHom.ext
  intro a
  exact congrArg (fun f : CommRingCat.of (ℬ.ring U) ⟶ CommRingCat.of (𝒜.ring U) ↦ f a) hr

/-- Mutually inverse affine algebra families induce inverse global scheme morphisms. -/
def mapIso (φ : Hom X 𝒜 ℬ) (ψ : Hom X ℬ 𝒜)
    (hφψ : φ.comp ψ = id 𝒜) (hψφ : ψ.comp φ = id ℬ) :
    relativeSpec X 𝒜 ≅ relativeSpec X ℬ where
  hom := φ.map
  inv := ψ.map
  hom_inv_id := by rw [← map_comp, hφψ, map_id]
  inv_hom_id := by rw [← map_comp, hψφ, map_id]

end Hom

end

end GromovWitten.AlgebraicGeometry.RelativeSpec
