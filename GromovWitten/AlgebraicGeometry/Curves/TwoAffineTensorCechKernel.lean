/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCohomologyBaseChange

/-!
# Tensor Čech kernels for an affine two-open cover

The kernel of the scalar-extended Čech differential is identified directly with
degree-zero cohomology after pullback.  This comparison uses the affine
base-change isomorphisms and does not require flatness assumptions.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the scalar-extended Čech differential is the pulled-back degree-zero
cohomology module for an affine two-open cover. -/
def twoAffineTensorCechKernelIso
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hI : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤) :
    kernel ((ModuleCat.extendScalars φ.hom).map (baseCechPairMap s M U V)) ≅
      cohomologyModuleCat T g ((Scheme.Modules.pullback p).obj M) 0 := by
  have hc : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  have hpair := cechPairBaseChangeMap_isIso s φ p g h M U V hU hV
  have hoverlap := cechOverlapBaseChangeMap_isIso s φ p g h M U V hI
  exact kernel.mapIso ((ModuleCat.extendScalars φ.hom).map (baseCechPairMap s M U V))
      (baseCechPairMap g ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) (p ⁻¹ᵁ V))
      (asIso (cechPairBaseChangeMap s φ p g h M U V))
      (asIso (cechOverlapBaseChangeMap s φ p g h M U V))
      (cechBaseChange_square s φ p g h M U V) ≪≫
    (cohomologyZeroIsoBaseCechKernel g ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) hc).symm

end GromovWitten.AlgebraicGeometry.Curves
