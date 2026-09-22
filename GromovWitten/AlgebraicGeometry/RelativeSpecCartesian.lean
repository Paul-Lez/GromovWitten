/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GromovWitten.AlgebraicGeometry.RelativeSpecFunctoriality

/-!
# Cartesian squares of relative spectra

A square of relative spectra is cartesian when the corresponding affine squares are
cartesian. This is proved by descent along the affine open cover of a relative spectrum.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace RelativeSpec

/-- Check a cartesian square on any chosen presentations of its inverse-image cover. -/
theorem isPullback_of_cover_presentations {W Y Z T : Scheme.{u}}
    (f : W ⟶ Y) (g : W ⟶ Z) (h : Y ⟶ T) (k : Z ⟶ T)
    (𝒰 : Y.OpenCover) (V : 𝒰.I₀ → Scheme.{u})
    (a : ∀ i, V i ⟶ W) (b : ∀ i, V i ⟶ 𝒰.X i)
    (ha : ∀ i, IsPullback (b i) (a i) (𝒰.f i) f)
    (hb : ∀ i, IsPullback (b i) (a i ≫ g) (𝒰.f i ≫ h) k) :
    IsPullback f g h k := by
  apply Scheme.isPullback_of_openCover f g h k 𝒰
  intro i
  refine (hb i).of_iso (ha i).flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simpa only [Scheme.Cover.pullbackHom, Iso.refl_hom, Category.comp_id]
      using! ((ha i).flip.isoPullback_hom_snd).symm
  · change a i ≫ g = (ha i).flip.isoPullback.hom ≫ pullback.fst f (𝒰.f i) ≫ g
    rw [← Category.assoc, (ha i).flip.isoPullback_hom_fst]
  · simp
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- Affine cartesian squares glue to a cartesian square of relative spectra. -/
theorem isPullback_map {X : Scheme.{u}} {𝒜 ℬ 𝒞 𝒟 : AlgebraData X}
    (φ : Hom X 𝒜 ℬ) (ψ : Hom X 𝒜 𝒞) (f : Hom X ℬ 𝒟) (g : Hom X 𝒞 𝒟)
    (H : ∀ U : X.affineOpens,
      IsPullback (Spec.map (CommRingCat.ofHom (φ.app U).toRingHom))
        (Spec.map (CommRingCat.ofHom (ψ.app U).toRingHom))
        (Spec.map (CommRingCat.ofHom (f.app U).toRingHom))
        (Spec.map (CommRingCat.ofHom (g.app U).toRingHom))) :
    IsPullback φ.map ψ.map f.map g.map := by
  apply isPullback_of_cover_presentations φ.map ψ.map f.map g.map
    (gluingData X ℬ).cover (fun U ↦ Spec (.of (𝒜.ring U)))
    (affineι X 𝒜) (fun U ↦ Spec.map (CommRingCat.ofHom (φ.app U).toRingHom))
  · intro U
    exact φ.isPullback_map U
  · intro U
    have h := (H U).paste_vert (g.isPullback_map U)
    rw [← ψ.affineι_map U, ← f.affineι_map U] at h
    exact h

end RelativeSpec

end GromovWitten.AlgebraicGeometry
