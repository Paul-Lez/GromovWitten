/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineHigherDirectImage
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineCoverVanishing

/-!
# Relative higher direct-image vanishing from two affine opens

A two-open affine cover of the source gives vanishing of module-valued higher direct images
from degree two onwards.  The statement is relative: the three open morphisms to the target
are required to be affine, while the target itself need not be affine or separated.
-/

open CategoryTheory Limits TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X Y : Scheme.{u}}

/-- The intersection of an affine open source piece with the preimage of an affine target open
is affine when the corresponding restricted morphism is affine. -/
lemma isAffineOpen_inf_preimage_of_affineHom (f : X ⟶ Y) (U : X.Opens)
    [IsAffineHom (U.ι ≫ f)] (W : Y.Opens) (hW : IsAffineOpen W) :
    IsAffineOpen (U ⊓ f ⁻¹ᵁ W) := by
  have h := (IsAffineHom.isAffine_preimage (f := U.ι ≫ f) W hW).image_of_isOpenImmersion U.ι
  convert h using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

/-- If a morphism has a two-open affine cover whose pieces and intersection are affine over the
target, its module higher direct images vanish from degree two onwards. -/
theorem isZero_higherDirectImageModule_twoAffineCover (f : X ⟶ Y) [IsLocallyNoetherian X]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [IsAffineHom (U.ι ≫ f)] [IsAffineHom (V.ι ≫ f)]
    [IsAffineHom ((U ⊓ V).ι ≫ f)]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (higherDirectImageModule f M (n + 2)) := by
  apply module_isZero_of_underlying
  apply IsZero.of_iso _ (higherDirectImageModuleAbIso f M (n + 2))
  refine isZero_rightDerived_pushforward_of_basis f.base
    ((moduleToSheafAb X).obj M) (n + 2) Y.isBasis_affineOpens ?_
  intro W hW
  let U' := U ⊓ f ⁻¹ᵁ W
  let V' := V ⊓ f ⁻¹ᵁ W
  have hu : IsAffineOpen U' := isAffineOpen_inf_preimage_of_affineHom f U W hW
  have hv : IsAffineOpen V' := isAffineOpen_inf_preimage_of_affineHom f V W hW
  have hi : IsAffineOpen (U' ⊓ V') := by
    have he : U' ⊓ V' = (U ⊓ V) ⊓ f ⁻¹ᵁ W := by
      dsimp [U', V']
      exact inf_inf_inf_comm _ _ _ _ |>.trans (by rw [inf_idem])
    rw [he]
    exact isAffineOpen_inf_preimage_of_affineHom f (U ⊓ V) W hW
  have hc : U' ⊔ V' = f ⁻¹ᵁ W := by
    dsimp [U', V']
    rw [← inf_sup_right, hcover, top_inf_eq]
  have hz := isZero_rightDerived_sections_sup ((moduleToSheafAb X).obj M) U' V' (n + 1)
    (isZero_rightDerived_sections_affineOpen_succ U' hu M (n + 1))
    (isZero_rightDerived_sections_affineOpen_succ V' hv M (n + 1))
    (isZero_rightDerived_sections_affineOpen_succ (U' ⊓ V') hi M n)
  rw [hc] at hz
  exact hz

end GromovWitten.AlgebraicGeometry.Curves
