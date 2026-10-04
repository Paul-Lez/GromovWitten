/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# A surjection of graded rings induces a closed immersion of `Proj`s

Mathlib's `AlgebraicGeometry.Proj.map` constructs, from a graded ring homomorphism
`φ : 𝒜 →+*ᵍ ℬ` together with the hypothesis `ℬ₊ ≤ 𝒜₊.map φ` (needed so that `φ` descends to a
morphism of the irrelevant loci), a scheme morphism `Proj ℬ ⟶ Proj 𝒜`. This file proves that
when `φ` is (ring-theoretically) surjective, this morphism is a closed immersion.

The hypothesis `ℬ₊ ≤ 𝒜₊.map φ` is in fact automatic from surjectivity (and gradedness) of `φ`,
so we also provide a version of the theorem that does not require it as a separate hypothesis.

## Main results

* `GromovWitten.AlgebraicGeometry.degree_surjective_of_surjective`: if `φ : 𝒜 →+*ᵍ ℬ` is
  surjective (as a plain ring homomorphism), then for every homogeneous element `b` of `ℬ`
  there is a homogeneous element of `𝒜` of the *same* degree mapping to it: the degree-`n`
  component of any preimage of `b` already maps to `b`.
* `GromovWitten.AlgebraicGeometry.irrelevant_le_map_of_surjective`: surjectivity of `φ` implies
  the hypothesis `ℬ₊ ≤ 𝒜₊.map φ` needed to form `Proj.map φ _`.
* `GromovWitten.AlgebraicGeometry.awayMap_surjective_of_surjective`: surjectivity of `φ`
  implies surjectivity of the induced map `Away.map φ s` between the homogeneous localisations
  at a homogeneous element `s` and its image.
* `GromovWitten.AlgebraicGeometry.isClosedImmersion_projMap`: if `φ : 𝒜 →+*ᵍ ℬ` is surjective,
  `Proj.map φ hf : Proj ℬ ⟶ Proj 𝒜` is a closed immersion.
* `GromovWitten.AlgebraicGeometry.isClosedImmersion_projMap_of_surjective`: the same statement,
  packaged with the irrelevant-ideal hypothesis supplied automatically from surjectivity.
-/

open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

namespace GromovWitten.AlgebraicGeometry

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)

open HomogeneousIdeal (irrelevant mem_irrelevant_of_mem irrelevant_le)

/-- If `φ : 𝒜 →+*ᵍ ℬ` is surjective and `b` is a homogeneous element of `ℬ` of degree `n`, then
some homogeneous element of `𝒜` of the *same* degree `n` already maps to `b`: namely, the
degree-`n` component of any preimage of `b` under `φ`. -/
theorem degree_surjective_of_surjective (hφ : Function.Surjective φ) (n : ℕ) {b : B}
    (hb : b ∈ ℬ n) : ∃ a ∈ 𝒜 n, φ a = b := by
  obtain ⟨a₀, ha₀⟩ := hφ b
  refine ⟨(DirectSum.decompose 𝒜 a₀ n : A), SetLike.coe_mem _, ?_⟩
  rw [φ.map_directSumDecompose, ha₀, DirectSum.decompose_of_mem_same ℬ hb]

/-- Surjectivity of a graded ring homomorphism `φ : 𝒜 →+*ᵍ ℬ` already gives the irrelevant-ideal
hypothesis `ℬ₊ ≤ 𝒜₊.map φ` needed to form `Proj.map φ _` (every homogeneous generator of `ℬ₊`
is the image of a homogeneous element of `𝒜` of the same positive degree, hence lies in `𝒜₊`). -/
theorem irrelevant_le_map_of_surjective (hφ : Function.Surjective φ) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map φ := by
  rw [irrelevant_le]
  rintro i hi x hx
  obtain ⟨a, ha, rfl⟩ := degree_surjective_of_surjective φ hφ i hx
  exact Ideal.mem_map_of_mem φ.toRingHom (mem_irrelevant_of_mem 𝒜 hi ha)

/-- If `φ : 𝒜 →+*ᵍ ℬ` is surjective and `s ∈ 𝒜 i` is homogeneous, the induced ring homomorphism
`Away.map φ s` between the homogeneous localisations at `s` and at `φ s` is surjective. -/
theorem awayMap_surjective_of_surjective (hφ : Function.Surjective φ) {i : ℕ} {s : A}
    (hs : s ∈ 𝒜 i) : Function.Surjective (Away.map φ s) := by
  intro y
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (φ.map_mem hs) y
  obtain ⟨a, ha, rfl⟩ := degree_surjective_of_surjective φ hφ (n • i) hb
  exact ⟨Away.mk 𝒜 hs n a ha, by rw [Away.map_mk]⟩

/-- For a graded ring homomorphism `φ : 𝒜 →+*ᵍ ℬ` satisfying `hf : ℬ₊ ≤ 𝒜₊.map φ`, the open
immersion `Proj.awayι ℬ (φ s) _ hi` into `Proj ℬ` fits into a pullback square over
`Proj.awayι 𝒜 s hs hi`, with the other leg `Spec.map (Away.map φ s)`: the square
```
Spec (Away ℬ (φ s)) ⟶ Spec (Away 𝒜 s)
        |                    |
        v                    v
    Proj ℬ ---- map φ hf ---> Proj 𝒜
```
is a pullback. -/
theorem isPullback_awayι_map (hf : irrelevant ℬ ≤ (irrelevant 𝒜).map φ) {i : ℕ} (hi : 0 < i)
    {s : A} (hs : s ∈ 𝒜 i) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map φ s)))
      (Proj.awayι ℬ (φ s) (φ.map_mem hs) hi) (Proj.awayι 𝒜 s hs hi) (Proj.map φ hf) :=
  IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map φ hf hi s hs) <| by
    rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen]

-- The `PNat` index of the canonical affine open cover makes the degree of `s` appear as a
-- coercion `↑⟨i, hi⟩` rather than the bare `i`; without relaxing the transparency used for
-- `isDefEq` checks, the final `rw` below fails to match terms that differ only by unfolding
-- this coercion.
set_option backward.isDefEq.respectTransparency false in
/-- If `φ : 𝒜 →+*ᵍ ℬ` is a surjective graded ring homomorphism and `hf : ℬ₊ ≤ 𝒜₊.map φ`, the
induced morphism `Proj.map φ hf : Proj ℬ ⟶ Proj 𝒜` is a closed immersion.

The proof checks this on the canonical affine open cover of `Proj 𝒜` by the loci `D₊(s)`: over
each such piece, `Proj.map φ hf` restricts (up to the canonical isomorphisms with `Proj.awayι`)
to `Spec.map (Away.map φ s)`, which is a closed immersion because `Away.map φ s` is surjective
(`awayMap_surjective_of_surjective`). -/
theorem isClosedImmersion_projMap (hφ : Function.Surjective φ)
    (hf : irrelevant ℬ ≤ (irrelevant 𝒜).map φ) : IsClosedImmersion (Proj.map φ hf) := by
  refine IsZariskiLocalAtTarget.of_openCover (Proj.affineOpenCover 𝒜).openCover ?_
  rintro ⟨⟨i, hi⟩, s, hs⟩
  change IsClosedImmersion
    (Limits.pullback.snd (Proj.map φ hf) (Proj.awayι 𝒜 s hs hi))
  have hpb := isPullback_awayι_map φ hf hi hs
  rw [← hpb.flip.isoPullback_inv_snd,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  exact IsClosedImmersion.spec_of_surjective _ (awayMap_surjective_of_surjective φ hφ hs)

/-- The surjective-graded-ring-homomorphism version of `isClosedImmersion_projMap`, with the
irrelevant-ideal hypothesis supplied automatically from surjectivity via
`irrelevant_le_map_of_surjective`. -/
theorem isClosedImmersion_projMap_of_surjective (hφ : Function.Surjective φ) :
    IsClosedImmersion (Proj.map φ (irrelevant_le_map_of_surjective φ hφ)) :=
  isClosedImmersion_projMap φ hφ _

end GromovWitten.AlgebraicGeometry
