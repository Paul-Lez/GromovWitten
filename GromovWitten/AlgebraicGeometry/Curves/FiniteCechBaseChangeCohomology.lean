/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteCechGeometricBaseChange
import GromovWitten.AlgebraicGeometry.Curves.FiniteAffineCechCohomology

/-!
# Cohomology after scalar extension of a finite affine Čech complex

The geometric Čech base-change quasi-isomorphism identifies the homology of
the scalar-extended complex with actual cohomology on the base-changed scheme.
Only the new total space must be locally Noetherian for this computation.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}
/-- Scalar extension of the finite affine complex computes actual cohomology after base change.
This is an object isomorphism; no identification of the induced map with a derived
base-change comparison is asserted here. -/
noncomputable def finiteCechBaseChangeHomologyIso
    [X.IsSeparated] [IsLocallyNoetherian Y]
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W) (hcover : coverUnion U = ⊤)
    (n : ℕ) :
    (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (.up ℤ)).obj
      (baseFiniteCechComplex s M U)).homology (n : ℤ) ≅
      cohomologyModuleCat T g ((Scheme.Modules.pullback p).obj M) n := by
  have : IsAffineHom p :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let Up := U.map (TopologicalSpace.Opens.map p.base).obj
  have hUp : ∀ W ∈ Up, IsAffineOpen W := by
    intro W hW
    obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hW
    exact (hU V hV).preimage p
  have hcoverp : coverUnion Up = ⊤ := by
    rw [coverUnion_preimage, hcover]
    rfl
  have := finiteCechGeometricBaseChangeMap_quasiIso s φ p g h M U hU
  exact asIso (homologyMap (finiteCechGeometricBaseChangeMap s φ p g h M U) (n : ℤ)) ≪≫
    baseFiniteCechHomologyIso g ((Scheme.Modules.pullback p).obj M) Up hUp hcoverp n
end GromovWitten.AlgebraicGeometry.Curves
