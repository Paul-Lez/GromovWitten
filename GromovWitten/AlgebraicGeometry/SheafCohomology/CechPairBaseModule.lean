/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSectionsLinear
import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairModule
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Base-linear Čech kernel and cokernel comparisons

The two-open Čech kernel and cokernel are identified with degree-zero and
degree-one cohomology after restricting scalars to the base ring.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- The top-section comparison with the scalar-linear global-section module. -/
def baseTopSectionsEquiv (s : X ⟶ Spec R) (M : X.Modules) :
    baseSectionModule s ⊤ M ≃ₗ[R] sectionsModuleCat (R : Type u) s M := by
  have hbase : (baseToSections s ⊤).hom = baseRingHom (R : Type u) s := by
    dsimp [baseToSections, baseRingHom]
    rw [X.presheaf.map_id]
    rfl
  exact
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r x
        change Γ(M, ⊤) at x
        change (baseToSections s ⊤).hom r • x = baseRingHom (R : Type u) s r • x
        rw [hbase] }

/-- The restriction-difference map with scalars restricted to the base. -/
def baseCechPairMap (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :=
  (ModuleCat.restrictScalars (baseRingHom (R : Type u) s)).map
    (sectionsFromPairModuleHom M U V)

set_option backward.isDefEq.respectTransparency false in
/-- The Čech kernel identified with degree-zero cohomology over the base. -/
def cohomologyZeroIsoBaseCechKernel (s : X ⟶ Spec R) (M : X.Modules)
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    ModuleCat.of R (cohomologyModuleCat (R : Type u) s M 0) ≅
      kernel (baseCechPairMap s M U V) := by
  let F := ModuleCat.restrictScalars (baseRingHom (R : Type u) s)
  let eTop : F.obj (sectionModuleCat M ⊤) ≅
      ModuleCat.of R (sectionsModuleCat (R : Type u) s M) :=
    (baseTopSectionsEquiv s M).toModuleIso
  let eCover : sectionModuleCat M (U ⊔ V) ≅ sectionModuleCat M ⊤ :=
    eqToIso (congrArg (sectionModuleCat M) hcover)
  let eK : sectionModuleCat M (U ⊔ V) ≅ kernel (sectionsFromPairModuleHom M U V) :=
    (sectionsToPairKernelLinearEquiv M U V).toModuleIso ≪≫
      (ModuleCat.kernelIsoKer (sectionsFromPairModuleHom M U V)).symm
  exact (cohomologyZeroBaseLinearEquiv (R : Type u) s M).toModuleIso ≪≫
    eTop.symm ≪≫ F.mapIso eCover.symm ≪≫ F.mapIso eK ≪≫
    PreservesKernel.iso F (sectionsFromPairModuleHom M U V)

set_option backward.isDefEq.respectTransparency false in
/-- The Čech cokernel identified with degree-one cohomology over the base. -/
def baseCechCokernelIsoCohomology [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤) :
    cokernel (baseCechPairMap s M U V) ≅
      ModuleCat.of R (cohomologyModuleCat (R : Type u) s M 1) := by
  let F := ModuleCat.restrictScalars (baseRingHom (R : Type u) s)
  exact (PreservesCokernel.iso F (sectionsFromPairModuleHom M U V)).symm ≪≫
    F.mapIso (cechPairModuleLinearEquivCohomology U V hU hV hcover M).toModuleIso

end GromovWitten.AlgebraicGeometry.SheafCohomology
