/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.VeroneseLocalization
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Affine schemes of Veronese homogeneous charts

The positive-index homogeneous localization equivalence induces the corresponding affine `Spec`
isomorphism.  This is the local affine statement; compatibility and gluing across all Proj charts
are separate results.
-/

namespace GromovWitten.AlgebraicGeometry

open CategoryTheory _root_.AlgebraicGeometry
open HomogeneousLocalization

universe u

noncomputable section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]

/-- The affine scheme isomorphism induced by the positive-index Veronese chart equivalence. -/
def veroneseLocalizationSpecIso (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e) (hd : 0 < d) :
    Spec (CommRingCat.of
      (HomogeneousLocalization.Away (veroneseComponent d 𝒜)
        (veronesePower (𝒜 := 𝒜) d e s hs))) ≅
      Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 s)) :=
  Scheme.Spec.mapIso (veroneseLocalizationEquiv (𝒜 := 𝒜) d e s hs hd).toCommRingCatIso.symm.op

@[simp]
theorem veroneseLocalizationSpecIso_hom (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e) (hd : 0 < d) :
    (veroneseLocalizationSpecIso (𝒜 := 𝒜) d e s hs hd).hom =
      Spec.map (CommRingCat.ofHom
        (veroneseLocalizationEquiv (𝒜 := 𝒜) d e s hs hd).symm.toRingHom) := rfl

@[simp]
theorem veroneseLocalizationSpecIso_inv (d e : ℕ) (s : A) (hs : s ∈ 𝒜 e) (hd : 0 < d) :
    (veroneseLocalizationSpecIso (𝒜 := 𝒜) d e s hs hd).inv =
      Spec.map (CommRingCat.ofHom
        (veroneseLocalizationEquiv (𝒜 := 𝒜) d e s hs hd).toRingHom) := rfl

end
end GromovWitten.AlgebraicGeometry
