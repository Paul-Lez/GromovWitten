/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteCechCohomologyZero
import GromovWitten.AlgebraicGeometry.Curves.FiniteCechAugmentationBaseChange
import GromovWitten.AlgebraicGeometry.Curves.OpenGlobalSectionsBaseChange
import GromovWitten.AlgebraicGeometry.Curves.ModulePullbackExact
import GromovWitten.CategoryTheory.AugmentedBaseChangeIso
/-!
# Canonical degree-zero base change from a finite affine cover

Compatibility with the Čech augmentation converts invertibility of the actual
homology comparison into invertibility of the canonical map on global sections.
For flat base-ring changes this applies to any quasi-coherent module on a
separated scheme with a finite affine cover. No Noetherian hypothesis is needed.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}
noncomputable local instance (φ : R ⟶ T) :
    PreservesBinaryBiproducts (ModuleCat.extendScalars.{u, u, u} φ.hom) :=
  preservesBinaryBiproducts_of_preservesBinaryCoproducts _
noncomputable local instance (φ : R ⟶ T) : (ModuleCat.extendScalars.{u, u, u} φ.hom).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _
/-- Invertibility of the canonical finite Čech homology comparison implies
invertibility of canonical base change on the top-open sections. -/
lemma openSectionsBaseChangeMap_isIso_of_finiteCech_comparison
    [X.IsSeparated]
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W)
    (hcover : coverUnion U = ⊤)
    [IsIso ((baseFiniteCechComplex s M U).homologyComparison
      (ModuleCat.extendScalars.{u, u, u} φ.hom) (0 : ℤ))] :
    IsIso (openSectionsBaseChangeMap s φ p g h M ⊤) := by
  have hp : coverUnion (U.map (TopologicalSpace.Opens.map p.base).obj) = ⊤ := by
    rw [coverUnion_preimage, hcover]
    rfl
  have := baseFiniteCechAugmentation_quasiIsoAt_zero s M U hcover
  have := baseFiniteCechAugmentation_quasiIsoAt_zero g ((Scheme.Modules.pullback p).obj M)
    (U.map (TopologicalSpace.Opens.map p.base).obj) hp
  have := finiteCechGeometricBaseChangeMap_quasiIso s φ p g h M U hU
  exact isIso_of_single_augmentation_baseChange (ModuleCat.extendScalars.{u, u, u} φ.hom) 0
    (baseFiniteCechAugmentation s M U)
    (baseFiniteCechAugmentation g ((Scheme.Modules.pullback p).obj M)
      (U.map (TopologicalSpace.Opens.map p.base).obj))
    (openSectionsBaseChangeMap s φ p g h M ⊤)
    (finiteCechGeometricBaseChangeMap s φ p g h M U)
    (finiteCechGeometricBaseChangeMap_augmentation s φ p g h M U)

/-- The canonical global-sections comparison is invertible when the finite Čech
complex has invertible degree-zero homology comparison. -/
lemma sectionsBaseChangeMap_isIso_of_finiteCech_comparison
    [X.IsSeparated]
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W)
    (hcover : coverUnion U = ⊤)
    [IsIso ((baseFiniteCechComplex s M U).homologyComparison
      (ModuleCat.extendScalars φ.hom) (0 : ℤ))] :
    IsIso (sectionsBaseChangeMap s φ p g h M) :=
  (isIso_openSectionsBaseChangeMap_top_iff s φ p g h M).mp
    (openSectionsBaseChangeMap_isIso_of_finiteCech_comparison s φ p g h M U hU hcover)

/-- Flat base-ring change commutes with canonical global sections on any finite
affine cover of a separated scheme, without Noetherian hypotheses. -/
lemma sectionsBaseChangeMap_isIso_of_finiteCech_flat_base
    [X.IsSeparated]
    (s : X ⟶ Spec R) (φ : R ⟶ T) (hφ : φ.hom.Flat)
    (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W)
    (hcover : coverUnion U = ⊤) :
    IsIso (sectionsBaseChangeMap s φ p g h M) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  have : IsIso ((baseFiniteCechComplex s M U).homologyComparison
      (ModuleCat.extendScalars φ.hom) (0 : ℤ)) :=
    ((baseFiniteCechComplex s M U).sc (0 : ℤ)).isIso_homologyComparison_of_preservesKernel
      (ModuleCat.extendScalars φ.hom)
  exact sectionsBaseChangeMap_isIso_of_finiteCech_comparison s φ p g h M U hU hcover

end GromovWitten.AlgebraicGeometry.Curves
