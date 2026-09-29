/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCohomologyBaseChange

/-!
# Projection compatibility for two-affine degree-zero base change

The flat two-affine degree-zero comparison is compatible with the Čech kernel inclusions.  This
is the projection identity needed to compare it with the canonical global-sections map.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Projection compatibility of the flat two-affine degree-zero comparison with Čech kernels. -/
lemma twoAffineCohomologyZeroBaseChangeIso_projection [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Flat R (cohomologyModuleCat R s M 1)]
    (hc : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤) :
    (twoAffineCohomologyZeroBaseChangeIso_of_flat s φ p g h M U V hU hV hI hcover hflat).hom ≫
      (cohomologyZeroIsoBaseCechKernel g ((Scheme.Modules.pullback p).obj M)
        (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hc).hom ≫
      kernel.ι (baseCechPairMap g ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)) =
    (ModuleCat.extendScalars φ.hom).map
      ((cohomologyZeroIsoBaseCechKernel s M U V hcover).hom ≫
        kernel.ι (baseCechPairMap s M U V)) ≫ cechPairBaseChangeMap s φ p g h M U V := by
  simp only [twoAffineCohomologyZeroBaseChangeIso_of_flat, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc,
    kernel.mapIso_hom, asIso_hom, kernel.map, kernel.lift_ι,
    PreservesKernel.iso_hom, kernelComparison_comp_ι_assoc, Functor.map_comp]

end GromovWitten.AlgebraicGeometry.Curves
